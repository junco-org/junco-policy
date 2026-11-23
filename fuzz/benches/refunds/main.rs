//! New approved refunds following abandoned transactions.
//!
//! Each stream queries 0 or 16 unapproved refunds once, then never revisits those IDs.
//! It subsequently approves and issues 32 refunds with new IDs, retaining each engine
//! throughout the stream. Only the new refund decisions are timed.
//!
//! Compilation, history ingestion and teardown are untimed. Dogwood request observation,
//! including any history-vector growth, is timed. Histories of 2^k + 1 events leave spare
//! capacity after ingestion; neither workload represents end-to-end refund processing.

use std::hint::black_box;
use std::sync::Arc;
use std::time::{Duration, Instant};

use criterion::{
    BenchmarkId, Criterion, PlottingBackend, SamplingMode, Throughput, criterion_group,
    criterion_main,
};
use dogwood_language::{
    Authorizer, Event, InMemoryTemporalEngine, ParsedPolicySet, PolicySchema, ServiceSchema,
    Validator,
};
use history_semantics::PolicyDecision;
use history_semantics::policy::{CompiledPolicy, PolicyRule, component_equals, component_is};
use history_store::{History, Store};
use history_syntax::{
    Comparison, Component, Component2, ComponentPattern, Head, KeyHash, RegexExpr, Rule, RuleMode,
    TestExpr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Action {
    Approve,
    Refund,
}

impl KeyHash for Action {
    fn key_hash(&self) -> u64 {
        match self {
            Self::Approve => 0,
            Self::Refund => 1,
        }
    }
}

type RefundEvent = (Action, u64);
type Junco = CompiledPolicy<RefundEvent, ()>;

const LENGTHS: [usize; 3] = [1025, 16385, 65537];
const ABORTED_COUNTS: [usize; 2] = [0, 16];
const REFUNDS_PER_STREAM: usize = 32;

const SCHEMA: &str = r#"
namespace Payments {
    entity Agent;
    entity Refund;
    action "Approve" appliesTo { principal: [Agent], resource: [Refund] };
    action "Refund" appliesTo { principal: [Agent], resource: [Refund] };
}
"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    callerResource: resourceType(A),
}
event <A>::response {
    callerResource: resourceType(A),
}
"#;

const POLICY: &str = r#"
@id("prior_approval")
permit (principal, action == Payments::Action::"Refund", resource)
when temporal {
    formerly within 24h Payments::Action::"Approve"::response{
        callerResource: resource
    }
};
"#;

fn junco(store: Arc<Store<RefundEvent>>) -> Junco {
    let approval = TestExpr::and([
        component_equals(
            Component(0),
            Component2::C0(Action::Approve),
            Comparison::Eq,
        ),
        component_is(Component(1), "refund", Comparison::Eq),
    ]);
    let rule = Rule::new(
        RuleMode::Require,
        Head::new([
            ComponentPattern::constant(Component2::C0(Action::Refund)),
            ComponentPattern::variable("refund"),
        ]),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(approval),
            RegexExpr::all(),
        ]),
    );
    CompiledPolicy::new(
        store,
        vec![PolicyRule {
            rule,
            diagnostic: Box::new(|_| ("refund requires approval".into(), Vec::new())),
        }],
    )
    .expect("Junco policy compiles")
}

struct Dogwood {
    parsed: ParsedPolicySet,
    schema: PolicySchema,
}

impl Dogwood {
    fn new() -> Self {
        let service = ServiceSchema::builder()
            .event_schema_str(EVENT_SCHEMA)
            .build()
            .expect("event schema");
        let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema");
        let parsed = ParsedPolicySet::parse(POLICY, &service).expect("policy parses");
        let validation = Validator::new().validate(&parsed.lower(&schema).expect("policy lowers"));
        assert!(
            validation.validation_passed(),
            "{:?}",
            validation.validation_errors().collect::<Vec<_>>()
        );
        Self { parsed, schema }
    }

    fn authorizer(&self) -> Authorizer {
        Authorizer::builder(self.parsed.lower(&self.schema).expect("policy lowers"))
            .temporal_engine(InMemoryTemporalEngine::new().slice_leaves())
            .build()
            .expect("authorizer builds")
    }

    fn ingested(&self, responses: &[Event]) -> Authorizer {
        let mut authorizer = self.authorizer();
        for response in responses {
            assert!(authorizer.is_authorized(response).is_none());
        }
        authorizer
    }
}

fn dogwood_event((action, refund): RefundEvent, kind: &str, timestamp: i64) -> Event {
    let action = match action {
        Action::Approve => "Approve",
        Action::Refund => "Refund",
    };
    Event::builder(&format!("Payments::Action::{action}"), kind)
        .timestamp(timestamp)
        .principal_for("Payments::Agent", "cashier")
        .resource_for("Payments::Refund", &refund.to_string())
        .build()
}

fn dogwood_decision(authorizer: &mut Authorizer, request: &Event, expected: bool) {
    let response = authorizer.is_authorized(request).expect("Dogwood decides");
    assert!(
        response.diagnostics().errors().next().is_none(),
        "{:?}",
        response.diagnostics()
    );
    assert_eq!(response.allowed(), expected);
}

fn junco_decision(
    policy: &mut Junco,
    history: &History<RefundEvent>,
    candidate: &RefundEvent,
    expected: bool,
) {
    assert_eq!(
        matches!(
            policy
                .decide(history, candidate, || ())
                .expect("Junco decides"),
            PolicyDecision::Grant
        ),
        expected,
    );
}

fn preflight(dogwood: &Dogwood) {
    let store = Arc::new(Store::new().expect("store"));
    let mut history = History::new(Arc::clone(&store)).expect("history");
    let mut policy = junco(store);
    let mut authorizer = dogwood.authorizer();
    let candidate = (Action::Refund, 1);
    junco_decision(&mut policy, &history, &candidate, false);
    dogwood_decision(
        &mut authorizer,
        &dogwood_event(candidate, "request", 0),
        false,
    );
    for (index, (event, expected)) in [
        ((Action::Approve, 0), false),
        ((Action::Refund, 0), false),
        ((Action::Approve, 1), true),
        ((Action::Refund, 1), true),
        ((Action::Approve, 2), true),
    ]
    .into_iter()
    .enumerate()
    {
        let timestamp = 2 * index as i64 + 1;
        history.push(event).expect("append");
        assert!(
            authorizer
                .is_authorized(&dogwood_event(event, "response", timestamp))
                .is_none()
        );
        junco_decision(&mut policy, &history, &candidate, expected);
        dogwood_decision(
            &mut authorizer,
            &dogwood_event(candidate, "request", timestamp + 1),
            expected,
        );
    }
    for (refund, expected) in [(2, true), (3, false)] {
        let candidate = (Action::Refund, refund);
        junco_decision(&mut policy, &history, &candidate, expected);
        dogwood_decision(
            &mut authorizer,
            &dogwood_event(candidate, "request", 12 + refund as i64),
            expected,
        );
    }
}

fn junco_stream(
    policy: &mut Junco,
    history: &mut History<RefundEvent>,
    aborted: usize,
    next_refund: &mut u64,
) -> Duration {
    let initial_length = history.len();
    for offset in 0..aborted {
        let candidate = (Action::Refund, (initial_length + offset) as u64);
        junco_decision(policy, history, &candidate, false);
    }
    let mut elapsed = Duration::ZERO;
    for _ in 0..REFUNDS_PER_STREAM {
        let refund = *next_refund;
        *next_refund = next_refund.checked_add(1).expect("refund ID exhaustion");
        history
            .push((Action::Approve, refund))
            .expect("append approval");
        let candidate = (Action::Refund, refund);
        let start = Instant::now();
        let decision = black_box(
            policy
                .decide(black_box(history), black_box(&candidate), || ())
                .expect("Junco decides"),
        );
        elapsed += start.elapsed();
        assert!(matches!(decision, PolicyDecision::Grant));
        history.push(candidate).expect("commit refund");
    }
    assert_eq!(history.len(), initial_length + 2 * REFUNDS_PER_STREAM);
    elapsed
}

fn dogwood_stream(
    authorizer: &mut Authorizer,
    initial_length: usize,
    aborted: usize,
    next_refund: &mut u64,
) -> Duration {
    for offset in 0..aborted {
        let candidate = (Action::Refund, (initial_length + offset) as u64);
        dogwood_decision(
            authorizer,
            &dogwood_event(candidate, "request", (initial_length + offset) as i64),
            false,
        );
    }
    let mut elapsed = Duration::ZERO;
    for index in 0..REFUNDS_PER_STREAM {
        let refund = *next_refund;
        *next_refund = next_refund.checked_add(1).expect("refund ID exhaustion");
        let timestamp = (initial_length + aborted + 3 * index) as i64;
        let approval = dogwood_event((Action::Approve, refund), "response", timestamp);
        let candidate = (Action::Refund, refund);
        let request = dogwood_event(candidate, "request", timestamp + 1);
        let commit = dogwood_event(candidate, "response", timestamp + 2);
        assert!(authorizer.is_authorized(&approval).is_none());
        let start = Instant::now();
        let response = black_box(
            authorizer
                .is_authorized(black_box(&request))
                .expect("Dogwood decides"),
        );
        elapsed += start.elapsed();
        assert!(
            response.diagnostics().errors().next().is_none(),
            "{:?}",
            response.diagnostics()
        );
        assert!(response.allowed());
        assert!(authorizer.is_authorized(&commit).is_none());
    }
    elapsed
}

fn refund_benchmarks(criterion: &mut Criterion) {
    let dogwood = Dogwood::new();
    preflight(&dogwood);

    let mut group = criterion.benchmark_group("refund_stream");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(1));
    group.throughput(Throughput::Elements(REFUNDS_PER_STREAM as u64));
    for length in LENGTHS {
        let store = Arc::new(Store::new().expect("store"));
        let events: Vec<_> = (0..length)
            .map(|refund| (Action::Approve, refund as u64))
            .collect();
        let responses: Vec<_> = events
            .iter()
            .enumerate()
            .map(|(index, event)| dogwood_event(*event, "response", index as i64))
            .collect();
        for aborted in ABORTED_COUNTS {
            let mut policy = junco(Arc::clone(&store));
            let first_refund = (length + 16) as u64;
            let mut next_refund = first_refund;
            for _ in 0..2 {
                let mut history = History::from_events(Arc::clone(&store), events.iter().copied())
                    .expect("history");
                let mut authorizer = dogwood.ingested(&responses);
                let mut dogwood_next = next_refund;
                junco_stream(&mut policy, &mut history, aborted, &mut next_refund);
                dogwood_stream(&mut authorizer, length, aborted, &mut dogwood_next);
                assert_eq!(next_refund, dogwood_next);
            }
            eprintln!(
                "refund stream preflight: history={length}, aborted={aborted}, two streams agree"
            );

            let parameter = format!("history_{length}/aborted_{aborted}");
            group.bench_function(BenchmarkId::new("junco", &parameter), |bencher| {
                bencher.iter_custom(|iters| {
                    let mut total = Duration::ZERO;
                    for _ in 0..iters {
                        let mut history =
                            History::from_events(Arc::clone(&store), events.iter().copied())
                                .expect("history");
                        total += junco_stream(&mut policy, &mut history, aborted, &mut next_refund);
                    }
                    total
                })
            });
            let mut next_refund = first_refund;
            group.bench_function(BenchmarkId::new("dogwood", &parameter), |bencher| {
                bencher.iter_custom(|iters| {
                    let mut total = Duration::ZERO;
                    for _ in 0..iters {
                        let mut authorizer = dogwood.ingested(&responses);
                        total += dogwood_stream(&mut authorizer, length, aborted, &mut next_refund);
                    }
                    total
                })
            });
        }
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().plotting_backend(PlottingBackend::Plotters);
    targets = refund_benchmarks
}
criterion_main!(benches);
