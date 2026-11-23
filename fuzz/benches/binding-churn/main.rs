//! Recent-witness decisions with working sets at and above Junco's cursor capacity.
//!
//! A Release requires a Read by the same principal on the same resource, with no subsequent
//! Edit by that principal on that resource. Round-robin reads put every witness near the end
//! of a long history. Dogwood can find it with a short backward scan; Junco must replay on
//! cursor eviction because the tail can still be invalidated by a future Edit.
//!
//! Each iteration decides one sweep of bindings over an unchanged committed history. Junco
//! retains its policy and history across sweeps. Dogwood ingests the same history outside
//! timing into a fresh leaf-sliced authorizer per sweep, since requests append to its trace.
//! Policy construction, history ingestion and teardown are outside timing for both engines.
//! History lengths of 2^k + 1 select spare-capacity cases for Dogwood's request appends.
//! This is a deliberately favorable case for backward scanning, not a representative workload.

use std::hint::black_box;
use std::sync::Arc;
use std::time::Duration;

use criterion::{
    BatchSize, BenchmarkId, Criterion, PlottingBackend, SamplingMode, Throughput, criterion_group,
    criterion_main,
};
use dogwood_language::{
    Authorizer, Event, InMemoryTemporalEngine, ParsedPolicySet, PolicySchema, ServiceSchema,
    Validator,
};
use history_semantics::PolicyDecision;
use history_semantics::policy::{
    CompiledPolicy, PRINCIPAL_VAR, PolicyRule, RESOURCE_VAR, action_is, last_state_change,
    principal_is, resource_is,
};
use history_store::{History, Store};
use history_syntax::{Comparison, ComponentPattern, Head, Rule, RuleMode, TestExpr};
use junco_policy::{Action, LockComponent, LockEvent};

type TraceEvent = LockEvent<u64, u64>;
type Junco = CompiledPolicy<TraceEvent, ()>;

const SCHEMA: &str = r#"
namespace Bench {
    entity Agent;
    entity Path;
    action "Read" appliesTo { principal: [Agent], resource: [Path] };
    action "Edit" appliesTo { principal: [Agent], resource: [Path] };
    action "Release" appliesTo { principal: [Agent], resource: [Path] };
}
"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    callerPrincipal: principalType(A),
    callerResource: resourceType(A),
}
event <A>::response {
    callerPrincipal: principalType(A),
    callerResource: resourceType(A),
}
"#;

const POLICY: &str = r#"
@id("read_since_edit")
permit (principal, action == Bench::Action::"Release", resource)
when temporal {
    (!Bench::Action::"Edit"::response{
        callerPrincipal: principal, callerResource: resource
    })
    since within 24h
    Bench::Action::"Read"::response{
        callerPrincipal: principal, callerResource: resource
    }
};
"#;

fn junco(store: Arc<Store<TraceEvent>>) -> Junco {
    let same_read = TestExpr::and([
        principal_is(Comparison::Eq),
        action_is(LockComponent::Action(Action::Read), Comparison::Eq),
        resource_is(Comparison::Eq),
    ]);
    let not_same_edit = TestExpr::or([
        principal_is(Comparison::Neq),
        action_is(LockComponent::Action(Action::Edit), Comparison::Neq),
        resource_is(Comparison::Neq),
    ]);
    let rule = Rule::new(
        RuleMode::Require,
        Head::new([
            ComponentPattern::variable(PRINCIPAL_VAR),
            ComponentPattern::constant(LockComponent::Action(Action::Release)),
            ComponentPattern::variable(RESOURCE_VAR),
        ]),
        last_state_change(same_read, not_same_edit),
    );
    CompiledPolicy::new(
        store,
        vec![PolicyRule {
            rule,
            diagnostic: Box::new(|_| ("read required after edit".into(), Vec::new())),
        }],
    )
    .expect("Junco policy compiles")
}

fn dogwood(parsed: &ParsedPolicySet, schema: &PolicySchema) -> Authorizer {
    Authorizer::builder(parsed.lower(schema).expect("Dogwood policy lowers"))
        .temporal_engine(InMemoryTemporalEngine::new().slice_leaves())
        .build()
        .expect("Dogwood authorizer builds")
}

fn dogwood_event(event: &TraceEvent, kind: &str, timestamp: i64) -> Event {
    let action = match event.action {
        Action::Read => "Read",
        Action::Edit => "Edit",
        Action::Release => "Release",
        Action::Remove => panic!("Remove is not in this benchmark's vocabulary"),
    };
    Event::builder(&format!("Bench::Action::{action}"), kind)
        .timestamp(timestamp)
        .principal_for("Bench::Agent", &event.principal.to_string())
        .resource_for("Bench::Path", &event.resource.to_string())
        .build()
}

fn agrees(
    policy: &mut Junco,
    history: &History<TraceEvent>,
    authorizer: &mut Authorizer,
    candidate: &TraceEvent,
    timestamp: i64,
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
    let response = authorizer
        .is_authorized(&dogwood_event(candidate, "request", timestamp))
        .expect("Dogwood decides");
    assert!(
        response.diagnostics().errors().next().is_none(),
        "{:?}",
        response.diagnostics()
    );
    assert_eq!(response.allowed(), expected);
}

fn preflight(parsed: &ParsedPolicySet, schema: &PolicySchema) {
    let store = Arc::new(Store::new().expect("store"));
    let mut history = History::new(Arc::clone(&store)).expect("history");
    let mut policy = junco(store);
    let mut authorizer = dogwood(parsed, schema);
    let candidate = TraceEvent::new(0, Action::Release, 0);
    agrees(&mut policy, &history, &mut authorizer, &candidate, 0, false);
    for (index, (event, expected)) in [
        (TraceEvent::new(1, Action::Read, 0), false),
        (TraceEvent::new(0, Action::Read, 1), false),
        (TraceEvent::new(0, Action::Read, 0), true),
        (TraceEvent::new(1, Action::Edit, 0), true),
        (TraceEvent::new(0, Action::Edit, 1), true),
        (TraceEvent::new(0, Action::Edit, 0), false),
        (TraceEvent::new(0, Action::Read, 0), true),
    ]
    .into_iter()
    .enumerate()
    {
        let timestamp = 2 * index as i64 + 1;
        history.push(event).expect("append");
        assert!(
            authorizer
                .is_authorized(&dogwood_event(&event, "response", timestamp))
                .is_none()
        );
        agrees(
            &mut policy,
            &history,
            &mut authorizer,
            &candidate,
            timestamp + 1,
            expected,
        );
    }
}

fn binding_churn(criterion: &mut Criterion) {
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
    preflight(&parsed, &schema);

    let mut group = criterion.benchmark_group("binding_churn");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(1));
    for length in [1025, 16385, 65537] {
        for width in [16, 17, 32] {
            let store = Arc::new(Store::new().expect("store"));
            let events: Vec<_> = (0..length)
                .map(|index| TraceEvent::new((index % width) as u64, Action::Read, 0))
                .collect();
            let history =
                History::from_events(Arc::clone(&store), events.iter().copied()).expect("history");
            let mut policy = junco(store);
            let candidates: Vec<_> = (0..width)
                .map(|principal| TraceEvent::new(principal as u64, Action::Release, 0))
                .collect();
            let responses: Vec<_> = events
                .iter()
                .enumerate()
                .map(|(index, event)| dogwood_event(event, "response", index as i64))
                .collect();
            let requests: Vec<_> = candidates
                .iter()
                .enumerate()
                .map(|(index, event)| dogwood_event(event, "request", (length + index) as i64))
                .collect();
            let ingested = || {
                let mut authorizer = dogwood(&parsed, &schema);
                for response in &responses {
                    assert!(authorizer.is_authorized(response).is_none());
                }
                authorizer
            };
            for _ in 0..2 {
                let mut authorizer = ingested();
                for (index, candidate) in candidates.iter().enumerate() {
                    agrees(
                        &mut policy,
                        &history,
                        &mut authorizer,
                        candidate,
                        (length + index) as i64,
                        true,
                    );
                }
            }
            eprintln!("binding churn preflight: history={length}, bindings={width} agree");

            let parameter = format!("history_{length}/bindings_{width}");
            group.throughput(Throughput::Elements(width as u64));
            group.bench_function(BenchmarkId::new("junco", &parameter), |bencher| {
                bencher.iter(|| {
                    for candidate in &candidates {
                        black_box(
                            policy
                                .decide(black_box(&history), black_box(candidate), || ())
                                .expect("Junco decides"),
                        );
                    }
                })
            });
            group.bench_function(BenchmarkId::new("dogwood", &parameter), |bencher| {
                bencher.iter_batched_ref(
                    &ingested,
                    |authorizer| {
                        for request in &requests {
                            black_box(
                                authorizer
                                    .is_authorized(black_box(request))
                                    .expect("Dogwood decides"),
                            );
                        }
                    },
                    BatchSize::PerIteration,
                )
            });
        }
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().plotting_backend(PlottingBackend::Plotters);
    targets = binding_churn
}
criterion_main!(benches);
