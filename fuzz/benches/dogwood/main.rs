//! Cold lock-policy replay (`dogwood_replay`), seeded candidates including denials
//! (`dogwood_fuzz`), and Dogwood-only documentation traces (`dogwood_examples`).
//!
//! Junco retains its compiled policy and store across iterations, with a fresh history each
//! time. Dogwood re-lowers and rebuilds outside timing: its authorizer consumes the lowered
//! policy set and has no reset. Timed replay includes decisions and committed-history ingestion.
//! Events are prebuilt: a `request` decides, and only a granted candidate gets a `response`.
//! Temporal predicates see responses only, so denied requests cannot change lock state.
//! One-second timestamps keep the largest stream (2,048 events) inside `within 24h`.
//!
//! VeriMon (`jshs/monpoly` commit `025a142321e4cd9174164568e38c399ec336a076`,
//! `-verified`) runs as a child process per iteration. A prelude sentinel proves readiness and a
//! trailing sentinel marks completion. Timing covers streaming the log and reading verdicts, not
//! process start-up, formula parsing, or exit. Each request time point decides; a commit time point
//! follows only when granted. The three MFOTL disjuncts encode `owned_by_other`, `stale_view`, and
//! `read_by_other`.
//!
//! | Junco rule | Dogwood `@id` |
//! | --- | --- |
//! | edit × owned_by_other | edit_owned_by_other |
//! | release × owned_by_other | release_owned_by_other |
//! | remove × owned_by_other | remove_owned_by_other |
//! | edit × stale_view | edit_stale_view |
//! | remove × stale_view | remove_stale_view |
//! | edit × read_by_other | edit_read_by_other |
//! | remove × read_by_other | remove_read_by_other |
//!
//! Dogwood has no benchmark suite at commit `4ec5e2c01b44ff3882a231ae5d315b330b38fa25`;
//! the examples group replays its doc examples instead. There is no warm single-decision
//! Dogwood probe: every `is_authorized` appends. `../lock_policy.rs` covers junco's warm probe.
//!
//! `deny_scaling` times one denied decision over committed histories of 2^4 ..= 2^16 granted
//! events (the `lock_scaling` trace): Junco warm with a retained policy, Dogwood over a freshly
//! ingested authorizer (ingestion untimed), VeriMon as one long-lived process per length with the
//! history streamed before timing, so the timed region is one request time point.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::hint::black_box;
use std::io::{BufRead, BufReader, Write as IoWrite};
use std::process::{Child, ChildStdout, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use criterion::{
    BatchSize, BenchmarkId, Criterion, PlottingBackend, SamplingMode, Throughput, criterion_group,
    criterion_main,
};
use dogwood_language::{
    Authorizer, Event, ParsedPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema,
    Validator, parse_trace,
};
use history_store::{History, Store};
use junco_policy::{Action, LockEvent, LockPolicy};
use lock_policy_harness::{
    Agent, BYTES_PER_EVENT, BYTES_PER_TRACE, DETERMINISTIC_SEED, MAX_AGENT_NUMBER, MAX_FILE_NUMBER,
    PooledPath, SEEDED_TRACE_COUNT, check, entropy, granted_history, validate_trace,
};

/// Four lock actions over agent principals and path resources.
const CEDAR_SCHEMA: &str = r#"
namespace Lock {
  entity Agent;
  entity Path;
  action "Read" appliesTo { principal: [Agent], resource: [Path] };
  action "Edit" appliesTo { principal: [Agent], resource: [Path] };
  action "Release" appliesTo { principal: [Agent], resource: [Path] };
  action "Remove" appliesTo { principal: [Agent], resource: [Path] };
}
"#;

/// No `pin`: other principals' committed events must remain visible.
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

/// A foreign last setter is a last setter AND NOT a last setter by this principal.
/// Predicates ignore the request under decision, which Dogwood appends before evaluation.
/// shortcut: the 24h window covers these traces; widen it before exceeding 86,400 seconds.
const POLICY: &str = r#"
@id("permit_all")
permit (principal, action, resource);

@id("edit_owned_by_other")
forbid (principal, action == Lock::Action::"Edit", resource)
when temporal {
    (!Lock::Action::"Edit"::response{ callerResource: resource }
     && !Lock::Action::"Release"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource })
    since within 24h
    Lock::Action::"Edit"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Edit"::response{ callerResource: resource }
         && !Lock::Action::"Release"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Edit"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("release_owned_by_other")
forbid (principal, action == Lock::Action::"Release", resource)
when temporal {
    (!Lock::Action::"Edit"::response{ callerResource: resource }
     && !Lock::Action::"Release"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource })
    since within 24h
    Lock::Action::"Edit"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Edit"::response{ callerResource: resource }
         && !Lock::Action::"Release"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Edit"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("remove_owned_by_other")
forbid (principal, action == Lock::Action::"Remove", resource)
when temporal {
    (!Lock::Action::"Edit"::response{ callerResource: resource }
     && !Lock::Action::"Release"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource })
    since within 24h
    Lock::Action::"Edit"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Edit"::response{ callerResource: resource }
         && !Lock::Action::"Release"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Edit"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("edit_stale_view")
forbid (principal, action == Lock::Action::"Edit", resource)
when temporal {
    (!Lock::Action::"Edit"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource }
     && !Lock::Action::"Read"::response{ callerResource: resource, callerPrincipal: principal })
    since within 24h
    Lock::Action::"Edit"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Edit"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Edit"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("remove_stale_view")
forbid (principal, action == Lock::Action::"Remove", resource)
when temporal {
    (!Lock::Action::"Edit"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource }
     && !Lock::Action::"Read"::response{ callerResource: resource, callerPrincipal: principal })
    since within 24h
    Lock::Action::"Edit"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Edit"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Edit"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("edit_read_by_other")
forbid (principal, action == Lock::Action::"Edit", resource)
when temporal {
    (!Lock::Action::"Read"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource })
    since within 24h
    Lock::Action::"Read"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Read"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Read"::response{ callerResource: resource, callerPrincipal: principal }
    )
};

@id("remove_read_by_other")
forbid (principal, action == Lock::Action::"Remove", resource)
when temporal {
    (!Lock::Action::"Read"::response{ callerResource: resource }
     && !Lock::Action::"Remove"::response{ callerResource: resource })
    since within 24h
    Lock::Action::"Read"::response{ callerResource: resource }
    && !(
        (!Lock::Action::"Read"::response{ callerResource: resource }
         && !Lock::Action::"Remove"::response{ callerResource: resource })
        since within 24h
        Lock::Action::"Read"::response{ callerResource: resource, callerPrincipal: principal }
    )
};
"#;

/// Fresh authorizers must re-lower: `LoweredPolicySet` is consumed and is not `Clone`.
struct Dogwood {
    parsed: ParsedPolicySet,
    schema: PolicySchema,
}

impl Dogwood {
    fn lock_policy() -> Self {
        let service = ServiceSchema::builder()
            .event_schema_str(EVENT_SCHEMA)
            .build()
            .expect("event schema builds");
        let schema = PolicySchema::from_cedarschema_str(CEDAR_SCHEMA).expect("cedar schema parses");
        let parsed = ParsedPolicySet::parse(POLICY, &service).expect("lock policy parses");
        let validation =
            Validator::new().validate(&parsed.lower(&schema).expect("lock policy lowers"));
        assert!(
            validation.validation_passed(),
            "{:?}",
            validation.validation_errors().collect::<Vec<_>>()
        );
        Self { parsed, schema }
    }

    fn authorizer(&self) -> Authorizer {
        Authorizer::new(self.parsed.lower(&self.schema).expect("policy lowers"))
    }
}

fn action_id(action: Action) -> &'static str {
    match action {
        Action::Read => "Read",
        Action::Edit => "Edit",
        Action::Release => "Release",
        Action::Remove => "Remove",
    }
}

/// A request decides; a response commits history. Construction is never timed.
fn dogwood_event(event: &LockEvent<Agent, PooledPath>, kind: &str, ts: i64) -> Event {
    Event::builder(&format!("Lock::Action::{}", action_id(event.action)), kind)
        .timestamp(ts)
        .principal_for("Lock::Agent", &event.principal.to_string())
        .resource_for("Lock::Path", &event.resource.to_string())
        .build()
}

const VERIMON_SIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/benches/dogwood/verimon/lock.sig"
);
const VERIMON_FORMULA: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/benches/dogwood/verimon/lock.mfotl"
);
const VERIMON_PRELUDE: &str =
    "@0 edit(\"sentinel_owner\",\"sentinel\")\n@1 edit_req(\"sentinel_other\",\"sentinel\")\n@2\n";
const VERIMON_FIRST_TP: usize = 3;

fn predicate(action: Action) -> &'static str {
    match action {
        Action::Read => "read",
        Action::Edit => "edit",
        Action::Release => "release",
        Action::Remove => "remove",
    }
}

struct VerimonLog {
    text: String,
    denied: Vec<usize>,
    sentinel: usize,
}

fn verimon_log<'a>(
    candidates: impl IntoIterator<Item = (&'a LockEvent<Agent, PooledPath>, bool)>,
) -> VerimonLog {
    let mut text = String::new();
    let mut denied = Vec::new();
    let mut tp = VERIMON_FIRST_TP;
    for (event, granted) in candidates {
        writeln!(
            text,
            "@{tp} {}_req(\"{}\",\"{}\")",
            predicate(event.action),
            event.principal,
            event.resource
        )
        .expect("write to string");
        if !granted {
            denied.push(tp);
        }
        tp += 1;
        if granted {
            writeln!(
                text,
                "@{tp} {}(\"{}\",\"{}\")",
                predicate(event.action),
                event.principal,
                event.resource
            )
            .expect("write to string");
            tp += 1;
        }
    }
    let sentinel = tp;
    write!(
        text,
        "@{tp} edit_req(\"sentinel_other\",\"sentinel\")\n@{}\n",
        tp + 1
    )
    .expect("write to string");
    VerimonLog {
        text,
        denied,
        sentinel,
    }
}

struct Verimon {
    child: Child,
    stdout: BufReader<ChildStdout>,
    line: String,
}

impl Verimon {
    fn spawn() -> Self {
        let binary = env::var_os("VERIMON").unwrap_or_else(|| "monpoly".into());
        let mut child = Command::new(binary)
            .args([
                "-verified",
                "-sig",
                VERIMON_SIG,
                "-formula",
                VERIMON_FORMULA,
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap_or_else(|error| {
                panic!(
                    "cannot start VeriMon: {error}; set VERIMON or install it per fuzz/benches/dogwood/README.md"
                )
            });
        let stdout = BufReader::new(child.stdout.take().expect("piped stdout"));
        child
            .stdin
            .as_mut()
            .expect("piped stdin")
            .write_all(VERIMON_PRELUDE.as_bytes())
            .expect("write VeriMon prelude");
        let mut verimon = Self {
            child,
            stdout,
            line: String::new(),
        };
        assert!(verimon.violations_until(1).is_empty());
        verimon
    }

    fn violations_until(&mut self, sentinel: usize) -> Vec<usize> {
        let mut violated = Vec::new();
        loop {
            self.line.clear();
            if self
                .stdout
                .read_line(&mut self.line)
                .expect("read VeriMon output")
                == 0
            {
                panic!("VeriMon exited before time point {sentinel}; see its stderr above");
            }
            let Some((_, suffix)) = self.line.split_once("(time point ") else {
                continue;
            };
            let time_point = suffix
                .split_once(')')
                .expect("VeriMon time point terminator")
                .0
                .parse()
                .expect("VeriMon numeric time point");
            if time_point == sentinel {
                break;
            }
            violated.push(time_point);
        }
        violated
    }

    fn run(&mut self, log: &VerimonLog) -> (Duration, Vec<usize>) {
        let start = Instant::now();
        // The log produces far less than a pipe buffer of output, so writing it first cannot block.
        self.child
            .stdin
            .as_mut()
            .expect("piped stdin")
            .write_all(log.text.as_bytes())
            .expect("write VeriMon log");
        let violated = self.violations_until(log.sentinel);
        (start.elapsed(), violated)
    }
}

impl Drop for Verimon {
    fn drop(&mut self) {
        self.child.stdin.take();
        let _ = self.child.wait();
    }
}

struct Junco {
    store: Arc<Store<LockEvent<Agent, PooledPath>>>,
    policy: LockPolicy<Agent, PooledPath>,
}

impl Junco {
    fn lock_policy() -> Self {
        let store = Arc::new(Store::new().expect("store"));
        Self {
            policy: LockPolicy::new(Arc::clone(&store)).expect("lock policy compiles"),
            store,
        }
    }

    fn history(&self) -> History<LockEvent<Agent, PooledPath>> {
        History::new(Arc::clone(&self.store)).expect("history")
    }
}

fn replay(criterion: &mut Criterion) {
    const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
    let history = granted_history(&entropy(SEED, 1024 * BYTES_PER_EVENT), 1024)
        .expect("granted replay history");
    let dogwood = Dogwood::lock_policy();
    let mut junco = Junco::lock_policy();
    let mut group = criterion.benchmark_group("dogwood_replay");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(1));

    for length in [16, 64, 256, 1024] {
        let events = &history.as_slice()[..length];
        let dogwood_events: Vec<_> = events
            .iter()
            .enumerate()
            .map(|(index, event)| {
                (
                    dogwood_event(event, "request", 2 * index as i64),
                    dogwood_event(event, "response", 2 * index as i64 + 1),
                )
            })
            .collect();
        let verimon_log = verimon_log(events.iter().map(|event| (event, true)));
        let mut authorizer = dogwood.authorizer();
        let mut prefix = junco.history();
        for (index, (event, (request, response))) in events.iter().zip(&dogwood_events).enumerate()
        {
            assert!(check(&mut junco.policy, &prefix, event).expect("decision"));
            assert!(
                authorizer
                    .is_authorized(request)
                    .expect("decides")
                    .allowed(),
                "dogwood denies granted event {index} at length {length}"
            );
            assert!(authorizer.is_authorized(response).is_none());
            prefix.push(*event).expect("append");
        }
        let (_, violated) = Verimon::spawn().run(&verimon_log);
        assert!(
            violated.is_empty(),
            "verimon denies a granted event at length {length}: {violated:?}"
        );
        eprintln!("replay preflight: {length} granted events agree");

        group.throughput(Throughput::Elements(length as u64));
        group.bench_function(BenchmarkId::new("junco", length), |bencher| {
            bencher.iter_batched(
                || History::new(Arc::clone(&junco.store)).expect("history"),
                |mut history| {
                    for event in events {
                        assert!(check(&mut junco.policy, &history, event).expect("decision"));
                        history.push(*event).expect("append");
                    }
                    history.len()
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_function(BenchmarkId::new("dogwood", length), |bencher| {
            bencher.iter_batched(
                || dogwood.authorizer(),
                |mut authorizer| {
                    for (request, response) in &dogwood_events {
                        assert!(
                            authorizer
                                .is_authorized(request)
                                .expect("decides")
                                .allowed()
                        );
                        assert!(authorizer.is_authorized(response).is_none());
                    }
                },
                BatchSize::PerIteration,
            )
        });
        group.bench_function(BenchmarkId::new("verimon", length), |bencher| {
            bencher.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let (elapsed, violated) = Verimon::spawn().run(&verimon_log);
                    assert!(violated.is_empty());
                    total += elapsed;
                }
                total
            })
        });
    }
    group.finish();
}

fn fuzz(criterion: &mut Criterion) {
    let traces: Vec<Vec<_>> = entropy(DETERMINISTIC_SEED, SEEDED_TRACE_COUNT * BYTES_PER_TRACE)
        .chunks(BYTES_PER_TRACE)
        .map(|bytes| {
            let trace = validate_trace(bytes).expect("seeded trace");
            let mut candidates = Vec::with_capacity(trace.history.len() + trace.denials.len());
            let mut denials = trace.denials.iter().peekable();
            for index in 0..=trace.history.len() {
                while let Some(denial) =
                    denials.next_if(|denial| denial.granted_prefix_len == index)
                {
                    candidates.push((denial.event, false));
                }
                if index < trace.history.len() {
                    candidates.push((trace.history.as_slice()[index], true));
                }
            }
            assert_eq!(candidates.len(), trace.history.len() + trace.denials.len());
            candidates
        })
        .collect();
    let dogwood_traces: Vec<Vec<_>> = traces
        .iter()
        .map(|trace| {
            trace
                .iter()
                .enumerate()
                .map(|(index, (event, granted))| {
                    (
                        dogwood_event(event, "request", 2 * index as i64),
                        granted.then(|| dogwood_event(event, "response", 2 * index as i64 + 1)),
                        *granted,
                    )
                })
                .collect()
        })
        .collect();
    let verimon_traces: Vec<_> = traces
        .iter()
        .map(|trace| verimon_log(trace.iter().map(|(event, granted)| (event, *granted))))
        .collect();
    let dogwood = Dogwood::lock_policy();
    let mut junco = Junco::lock_policy();
    let mut total = 0;
    let mut denied = 0;
    for (trace_index, (trace, dogwood_trace)) in traces.iter().zip(&dogwood_traces).enumerate() {
        let mut history = junco.history();
        let mut authorizer = dogwood.authorizer();
        for (index, ((event, expected), (request, response, _))) in
            trace.iter().zip(dogwood_trace).enumerate()
        {
            let got = check(&mut junco.policy, &history, event).expect("decision");
            assert_eq!(
                got, *expected,
                "trace {trace_index} step {index}: junco for {event:?}"
            );
            let got = authorizer
                .is_authorized(request)
                .expect("decides")
                .allowed();
            assert_eq!(
                got, *expected,
                "trace {trace_index} step {index}: dogwood {got} != junco {expected} for {event:?}"
            );
            if *expected {
                history.push(*event).expect("append");
            } else {
                denied += 1;
            }
            if let Some(response) = response {
                assert!(authorizer.is_authorized(response).is_none());
            }
            total += 1;
        }
        let verimon_log = &verimon_traces[trace_index];
        let (_, violated) = Verimon::spawn().run(verimon_log);
        assert_eq!(
            violated, verimon_log.denied,
            "trace {trace_index}: verimon denials differ from junco"
        );
    }
    assert!(denied > 0, "seeded traces must exercise denials");
    eprintln!(
        "fuzz preflight: {total} candidates ({denied} denied) in {} traces agree across all three engines",
        traces.len()
    );

    let mut group = criterion.benchmark_group("dogwood_fuzz");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(1));
    group.throughput(Throughput::Elements(total as u64));
    group.bench_function("junco", |bencher| {
        bencher.iter_batched(
            || {
                (0..traces.len())
                    .map(|_| History::new(Arc::clone(&junco.store)).expect("history"))
                    .collect::<Vec<_>>()
            },
            |histories| {
                for (trace, mut history) in traces.iter().zip(histories) {
                    for (event, expected) in trace {
                        let granted = check(&mut junco.policy, &history, event).expect("decision");
                        assert_eq!(granted, *expected);
                        if granted {
                            history.push(*event).expect("append");
                        }
                    }
                }
            },
            BatchSize::PerIteration,
        )
    });
    group.bench_function("dogwood", |bencher| {
        bencher.iter_batched(
            || {
                (0..traces.len())
                    .map(|_| dogwood.authorizer())
                    .collect::<Vec<_>>()
            },
            |authorizers| {
                for (trace, mut authorizer) in dogwood_traces.iter().zip(authorizers) {
                    for (request, response, expected) in trace {
                        let granted = authorizer
                            .is_authorized(request)
                            .expect("decides")
                            .allowed();
                        assert_eq!(granted, *expected);
                        if let Some(response) = response {
                            assert!(authorizer.is_authorized(response).is_none());
                        }
                    }
                }
            },
            BatchSize::PerIteration,
        )
    });
    group.bench_function("verimon", |bencher| {
        bencher.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                for log in &verimon_traces {
                    let (elapsed, violated) = Verimon::spawn().run(log);
                    assert_eq!(violated, log.denied);
                    total += elapsed;
                }
            }
            total
        })
    });
    group.finish();
}

const EXAMPLES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/benches/dogwood/examples");

struct Example {
    name: String,
    dogwood: Dogwood,
    events: Vec<Event>,
    expected: String,
}

fn load_examples() -> Vec<Example> {
    let mut directories: Vec<_> = fs::read_dir(EXAMPLES)
        .expect("vendored examples directory")
        .map(|entry| entry.expect("example entry").path())
        .filter(|path| path.is_dir())
        .collect();
    directories.sort();
    let examples: Vec<_> = directories
        .into_iter()
        .map(|directory| {
            let name = directory
                .file_name()
                .expect("example directory name")
                .to_str()
                .expect("UTF-8 example name")
                .to_owned();
            let read = |file| fs::read_to_string(directory.join(file)).expect(&name);
            let optional = |file| fs::read_to_string(directory.join(file)).ok();
            let event_schema = optional("events.dwschema").or_else(|| optional("event.dwschema"));
            let providers = optional("providers.json");
            let macros = optional("macros.dw");
            let service = if event_schema.is_none() && providers.is_none() && macros.is_none() {
                ServiceSchema::defaults()
            } else {
                let mut builder = ServiceSchema::builder();
                if let Some(schema) = event_schema {
                    builder = builder.event_schema_str(&schema);
                }
                if let Some(providers) = providers {
                    builder = builder
                        .providers(ProviderDeclarations::from_json(&providers).expect(&name));
                }
                if let Some(macros) = macros {
                    builder = builder.macros_str(&macros);
                }
                builder.build().expect(&name)
            };
            let schema =
                PolicySchema::from_cedarschema_str(&read("schema.cedarschema")).expect(&name);
            let parsed = ParsedPolicySet::parse(&read("policy.dw"), &service).expect(&name);
            let events = parse_trace(&read("trace.log")).expect(&name);
            let expected = read("expected.out");
            Example {
                name,
                dogwood: Dogwood { parsed, schema },
                events,
                expected,
            }
        })
        .collect();
    assert_eq!(examples.len(), 52);
    examples
}

/// Match the CLI renderer, whose time-point index counts decisions rather than all events.
fn render(authorizer: &mut Authorizer, events: &[Event]) -> String {
    let mut out = String::new();
    let mut index = 0;
    for event in events {
        let Some(response) = authorizer.is_authorized(event) else {
            continue;
        };
        let decision = if response.allowed() { "ALLOW" } else { "DENY" };
        write!(
            out,
            "@{} (time point {index}): {decision}",
            event.timestamp()
        )
        .unwrap();
        let rules: Vec<_> = response
            .diagnostics()
            .reason()
            .map(|rule| rule.rule_index.to_string())
            .collect();
        if !rules.is_empty() {
            write!(out, "  [rules: {}]", rules.join(", ")).unwrap();
        }
        out.push('\n');
        for error in response.diagnostics().errors() {
            writeln!(out, "    error: {error}").unwrap();
        }
        index += 1;
    }
    out
}

fn examples(criterion: &mut Criterion) {
    let examples = load_examples();
    for example in &examples {
        assert_eq!(
            render(&mut example.dogwood.authorizer(), &example.events).trim_end(),
            example.expected.trim_end(),
            "{}",
            example.name
        );
    }
    eprintln!(
        "examples preflight: {} examples match expected.out",
        examples.len()
    );

    let mut group = criterion.benchmark_group("dogwood_examples");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(200));
    group.measurement_time(Duration::from_millis(500));
    for example in &examples {
        group.throughput(Throughput::Elements(example.events.len() as u64));
        group.bench_function(BenchmarkId::from_parameter(&example.name), |bencher| {
            bencher.iter_batched(
                || example.dogwood.authorizer(),
                |mut authorizer| {
                    for event in &example.events {
                        black_box(authorizer.is_authorized(event));
                    }
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
}

/// First Edit/Remove/Release candidate the lock policy denies over `prefix`, in a fixed order
/// over actions, agents and paths. `Read` has no forbid rule and is never denied.
fn denied_candidate(
    policy: &mut LockPolicy<Agent, PooledPath>,
    prefix: &History<LockEvent<Agent, PooledPath>>,
) -> Option<LockEvent<Agent, PooledPath>> {
    [Action::Edit, Action::Remove, Action::Release]
        .into_iter()
        .flat_map(|action| {
            (0..MAX_AGENT_NUMBER).flat_map(move |agent| {
                (0..MAX_FILE_NUMBER)
                    .map(move |path| LockEvent::new(Agent(agent), action, PooledPath(path)))
            })
        })
        .find(|candidate| !check(policy, prefix, candidate).expect("decision"))
}

/// One request time point whose denial is the sentinel; the empty `@{tp + 1}` closes it so
/// VeriMon emits the verdict. Only valid once the request is known to be denied.
fn verimon_request(tp: usize, event: &LockEvent<Agent, PooledPath>) -> VerimonLog {
    VerimonLog {
        text: format!(
            "@{tp} {}_req(\"{}\",\"{}\")\n@{}\n",
            predicate(event.action),
            event.principal,
            event.resource,
            tp + 1
        ),
        denied: Vec::new(),
        sentinel: tp,
    }
}

fn deny(criterion: &mut Criterion) {
    // Same lengths, seed and prefixes as `../lock-policy/main.rs`, so junco points match its panel.
    const LENGTHS: [usize; 13] = [
        16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
    ];
    const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
    const DOGWOOD_MAX_LENGTH: usize = 65536;
    let longest = LENGTHS[LENGTHS.len() - 1];
    let history = granted_history(&entropy(SEED, longest * BYTES_PER_EVENT), longest)
        .expect("benchmark history generation failed");
    let store = history.store();
    let dogwood = Dogwood::lock_policy();
    let mut group = criterion.benchmark_group("deny_scaling");
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(1));

    for length in LENGTHS {
        let events = &history.as_slice()[..length];
        let prefix = History::from_events(Arc::clone(store), events.iter().copied())
            .expect("benchmark prefix construction failed");
        let mut policy = LockPolicy::new(Arc::clone(store)).expect("lock policy compiles");
        let candidate = denied_candidate(&mut policy, &prefix)
            .unwrap_or_else(|| panic!("no denied candidate at length {length}"));
        eprintln!("deny {length}: {candidate:?}");

        // Responses only, one second apart: 65,536 s stays inside the policy's `within 24h`.
        let responses: Vec<Event> = events
            .iter()
            .enumerate()
            .map(|(index, event)| dogwood_event(event, "response", index as i64))
            .collect();
        let request = dogwood_event(&candidate, "request", length as i64);
        let ingested = || {
            let mut authorizer = dogwood.authorizer();
            for response in &responses {
                assert!(authorizer.is_authorized(response).is_none());
            }
            authorizer
        };
        if length <= DOGWOOD_MAX_LENGTH {
            assert!(
                !ingested()
                    .is_authorized(&request)
                    .expect("decides")
                    .allowed(),
                "dogwood grants {candidate:?} at length {length}"
            );
        }

        // Stream the commits once; commits are never requests, so nothing precedes the sentinel.
        let mut verimon = Verimon::spawn();
        let mut text = String::new();
        for (index, event) in events.iter().enumerate() {
            writeln!(
                text,
                "@{} {}(\"{}\",\"{}\")",
                VERIMON_FIRST_TP + index,
                predicate(event.action),
                event.principal,
                event.resource
            )
            .expect("write to string");
        }
        let sentinel = VERIMON_FIRST_TP + length;
        write!(
            text,
            "@{sentinel} edit_req(\"sentinel_other\",\"sentinel\")\n@{}\n",
            sentinel + 1
        )
        .expect("write to string");
        let ingest = VerimonLog {
            text,
            denied: Vec::new(),
            sentinel,
        };
        let (_, violated) = verimon.run(&ingest);
        assert!(
            violated.is_empty(),
            "verimon violations during ingest at length {length}: {violated:?}"
        );
        // Preflight with a guaranteed sentinel so a VeriMon grant cannot hang the reader.
        let mut tp = sentinel + 2;
        let preflight = VerimonLog {
            text: format!(
                "@{tp} {}_req(\"{}\",\"{}\")\n@{} edit_req(\"sentinel_other\",\"sentinel\")\n@{}\n",
                predicate(candidate.action),
                candidate.principal,
                candidate.resource,
                tp + 1,
                tp + 2
            ),
            denied: Vec::new(),
            sentinel: tp + 1,
        };
        assert_eq!(
            verimon.run(&preflight).1,
            vec![tp],
            "verimon grants {candidate:?} at length {length}"
        );
        tp += 3;

        group.bench_function(BenchmarkId::new("junco", length), |bencher| {
            bencher.iter(|| {
                check(&mut policy, black_box(&prefix), black_box(&candidate)).expect("decision")
            })
        });
        if length <= DOGWOOD_MAX_LENGTH {
            group.bench_function(BenchmarkId::new("dogwood", length), |bencher| {
                bencher.iter_batched(
                    ingested,
                    |mut authorizer| {
                        assert!(
                            !authorizer
                                .is_authorized(&request)
                                .expect("decides")
                                .allowed()
                        )
                    },
                    BatchSize::PerIteration,
                )
            });
        }
        group.bench_function(BenchmarkId::new("verimon", length), |bencher| {
            bencher.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let (elapsed, violated) = verimon.run(&verimon_request(tp, &candidate));
                    assert!(violated.is_empty());
                    total += elapsed;
                    tp += 2;
                }
                total
            })
        });
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().plotting_backend(PlottingBackend::Plotters);
    targets = replay, fuzz, examples, deny
}
criterion_main!(benches);
