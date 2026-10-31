//! Criterion benchmarks for compilation, history evaluation, full scans, denial, and rollback.
//!
//! Run the suite from this package with `cargo bench --bench validator`. Pass a Criterion filter,
//! for example `cargo bench --bench validator -- history_scan`, to run one group.

use std::hint::black_box;
use std::time::{Duration, Instant};

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use history_semantics::{Decision, Validator};
use history_store::Store;
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use junco_core::Request;
use junco_policy::{Action, LockEvent};
use std::sync::Arc;

/// Benchmark principal identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Actor(u32);

/// Benchmark resource identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Path(u32);

const ALICE: Actor = Actor(0);
const CANDIDATE: Actor = Actor(1);
const HISTORY: Actor = Actor(2);
/// First id of principals and resources named only by rule constants; no benchmark event carries
/// one.
const ABSENT_IDS: u32 = 1 << 20;
/// First id of the high-cardinality history's unique principals and resources.
const UNIQUE_IDS: u32 = 1 << 24;

const ROOT: Path = Path(0);
const SRC_A: Path = Path(1);
const A: Path = Path(2);
const TARGET: Path = Path(3);
const EVENT: Path = Path(4);

fn request(actor: Actor, action: Action, path: Path) -> Request<LockEvent<Actor, Path>, ()> {
    Request::new(LockEvent::new(actor, action, path), ())
}

fn prior_edit_rule(suffix: usize) -> Rule<LockEvent<Actor, Path>> {
    let actor = format!("actor-{suffix}");
    let target = format!("target-{suffix}");
    let principal = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable(actor.clone())),
    );
    let action = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
    );
    let resource = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::variable(target.clone())),
    );
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable(actor),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable(target),
        ),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(TestExpr::and([principal, action, resource])),
        ]),
    )
}

fn duplicate_remove_rule() -> Rule<LockEvent<Actor, Path>> {
    let matching_remove = RegexExpr::test(TestExpr::and([
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Action(ComponentPattern::constant(Action::Remove)),
        ),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::variable("target")),
        ),
    ]));
    Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Remove),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::concat([RegexExpr::all(), matching_remove, RegexExpr::all()]),
    )
}

fn every_resource_leaf(index: usize) -> RegexExpr<LockEvent<Actor, Path>> {
    RegexExpr::star(RegexExpr::test(TestExpr::atom(
        Comparison::Neq,
        AtomPattern::Resource(ComponentPattern::constant(Path(ABSENT_IDS + index as u32))),
    )))
}

fn deeply_nested_resource_allow_all_rule(depth: usize) -> Rule<LockEvent<Actor, Path>> {
    assert!(depth > 0, "regex depth must be positive");
    let mut leaves = (0..depth).map(every_resource_leaf);
    let mut tail = leaves.next().expect("positive depth has one leaf");
    for (index, leaf) in leaves.enumerate() {
        tail = if index % 2 == 0 {
            RegexExpr::union([tail, leaf])
        } else {
            RegexExpr::intersect([tail, leaf])
        };
    }
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        tail,
    )
}

fn unique_read(index: usize) -> Request<LockEvent<Actor, Path>, ()> {
    let id = UNIQUE_IDS + u32::try_from(index).expect("benchmark index fits u32");
    request(Actor(id), Action::Read, Path(id))
}

// Each distinct star accepts every benchmark event and is stable under differentiation.
fn every_event_leaf(index: usize) -> RegexExpr<LockEvent<Actor, Path>> {
    RegexExpr::star(RegexExpr::test(TestExpr::atom(
        Comparison::Neq,
        AtomPattern::Principal(ComponentPattern::constant(Actor(ABSENT_IDS + index as u32))),
    )))
}

fn deeply_nested_allow_all_rule(depth: usize) -> Rule<LockEvent<Actor, Path>> {
    assert!(depth > 0, "regex depth must be positive");
    let mut leaves = (0..depth).map(every_event_leaf);
    let mut tail = leaves.next().expect("positive depth has one leaf");
    // Alternating operators retain binary nesting because canonicalization only flattens like kinds.
    for (index, leaf) in leaves.enumerate() {
        tail = if index % 2 == 0 {
            RegexExpr::union([tail, leaf])
        } else {
            RegexExpr::intersect([tail, leaf])
        };
    }

    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        tail,
    )
}

fn advancing_optional_rule(steps: usize) -> Rule<LockEvent<Actor, Path>> {
    let factors = (0..steps).map(|index| {
        RegexExpr::union([
            RegexExpr::epsilon(),
            RegexExpr::test(TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Resource(ComponentPattern::constant(Path(ABSENT_IDS + index as u32))),
            )),
        ])
    });
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::concat(factors),
    )
}

/// Language whose residual DAG gains one suffix alternative after each matching event.
///
/// `Σ* · Read · Σ^(window + 1)` recognizes histories whose `(window + 2)`th event from the end is a
/// read. A shorter all-read history keeps adding candidate suffixes without reaching a terminal
/// residual. The full DFA has exponentially many states even though this measured path grows
/// linearly.
fn growing_residual_rule(window: usize) -> Rule<LockEvent<Actor, Path>> {
    assert!(window > 0, "residual-growth window must be positive");
    let any_event = RegexExpr::test(TestExpr::true_test());
    let read = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Read)),
    ));
    let factors = std::iter::once(RegexExpr::all())
        .chain(std::iter::once(read))
        .chain(std::iter::repeat_n(any_event, window + 1));
    Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::concat(factors),
    )
}

/// One unique absent-witness rule that forces a complete nonterminal history scan.
fn absent_witness_rule(index: usize) -> Rule<LockEvent<Actor, Path>> {
    let absent = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::constant(Actor(ABSENT_IDS + index as u32))),
    ));
    Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::concat([RegexExpr::all(), absent, RegexExpr::all()]),
    )
}

// The matching Require rule forces all one million committed events through the depth-32 tail.
fn benchmark_million_event_nested_scan(criterion: &mut Criterion) {
    const HISTORY_LEN: usize = 1_000_000;
    const REGEX_DEPTH: usize = 32;

    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder
        .add_rule(deeply_nested_allow_all_rule(REGEX_DEPTH))
        .expect("benchmark rule is valid");
    let mut validator = builder.finish().unwrap();
    for _ in 0..HISTORY_LEN {
        let _ = validator.check(request(ALICE, Action::Read, ROOT)).unwrap();
    }
    assert_eq!(validator.history().len(), HISTORY_LEN);
    let checkpoint = validator.checkpoint();

    let mut group = criterion.benchmark_group("full_scan");
    group.throughput(Throughput::Elements(HISTORY_LEN as u64));
    group.sample_size(10);
    group.bench_function("1000000_events/depth_32", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..iterations {
                let candidate = request(ALICE, Action::Release, ROOT);
                let start = Instant::now();
                let decision = validator.check(black_box(candidate)).unwrap();
                elapsed += start.elapsed();
                assert!(decision.is_grant());
                validator.rollback(checkpoint).unwrap();
            }
            elapsed
        });
    });
    group.finish();
}

// Every history symbol is distinct, defeating symbol-indexed successor caches. Each leaf compares
// the event's resource with a constant no event carries, so every unique resource is compared.
fn benchmark_high_cardinality_scan(criterion: &mut Criterion) {
    const HISTORY_LEN: usize = 100_000;
    const REGEX_DEPTH: usize = 32;

    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder
        .add_rule(deeply_nested_resource_allow_all_rule(REGEX_DEPTH))
        .expect("benchmark rule is valid");
    let mut validator = builder.finish().unwrap();
    for index in 0..HISTORY_LEN {
        let _ = validator.check(unique_read(index)).unwrap();
    }
    assert_eq!(validator.history().len(), HISTORY_LEN);
    let checkpoint = validator.checkpoint();

    let mut group = criterion.benchmark_group("high_cardinality_scan");
    group.throughput(Throughput::Elements(HISTORY_LEN as u64));
    group.sample_size(10);
    group.bench_function("100000_events/depth_32", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..iterations {
                let candidate = request(CANDIDATE, Action::Release, ROOT);
                let start = Instant::now();
                let decision = validator.check(black_box(candidate)).unwrap();
                elapsed += start.elapsed();
                assert!(decision.is_grant());
                validator.rollback(checkpoint).unwrap();
            }
            elapsed
        });
    });
    group.finish();
}

// Every derivative advances through a new suffix of a long concatenation of optional predicates.
// Symbol caches cannot reuse `(transition, symbol)` because the transition changes at every event.
fn benchmark_advancing_derivatives(criterion: &mut Criterion) {
    const STEPS: usize = 16;

    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder
        .add_rule(advancing_optional_rule(STEPS))
        .expect("benchmark rule is valid");
    let mut validator = builder.finish().unwrap();
    for _ in 0..STEPS {
        let _ = validator
            .check(request(HISTORY, Action::Read, ROOT))
            .unwrap();
    }
    let checkpoint = validator.checkpoint();

    let mut group = criterion.benchmark_group("advancing_derivatives");
    group.throughput(Throughput::Elements(STEPS as u64));
    group.sample_size(10);
    group.bench_function("16_optional_factors", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..iterations {
                let candidate = request(CANDIDATE, Action::Release, ROOT);
                let start = Instant::now();
                let decision = validator.check(black_box(candidate)).unwrap();
                elapsed += start.elapsed();
                assert!(decision.is_grant());
                validator.rollback(checkpoint).unwrap();
            }
            elapsed
        });
    });
    group.finish();
}

fn benchmark_growing_residual_stress(criterion: &mut Criterion) {
    let mut compile = criterion.benchmark_group("stress_growing_residual_compile");
    compile
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3))
        .sample_size(10);
    for window in [4_usize, 8, 12] {
        compile.bench_with_input(
            BenchmarkId::from_parameter(window),
            &window,
            |bencher, &window| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let source = growing_residual_rule(window);
                        let store = Arc::new(Store::new().unwrap());
                        let start = Instant::now();
                        let mut builder = Validator::builder(Arc::clone(&store));
                        builder.add_rule(source).expect("stress rule is valid");
                        let validator = builder.finish().unwrap();
                        black_box(&validator);
                        elapsed += start.elapsed();
                    }
                    elapsed
                });
            },
        );
    }
    compile.finish();

    let mut evaluate = criterion.benchmark_group("stress_growing_residual_evaluate");
    evaluate
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3))
        .sample_size(10);
    for window in [8_usize, 16, 32, 64] {
        let store = Arc::new(Store::new().unwrap());
        let mut builder = Validator::builder(Arc::clone(&store));
        builder
            .add_rule(growing_residual_rule(window))
            .expect("stress rule is valid");
        let mut validator = builder.finish().unwrap();
        for _ in 0..window {
            assert!(
                validator
                    .check(request(HISTORY, Action::Read, EVENT))
                    .unwrap()
                    .is_grant()
            );
        }
        let checkpoint = validator.checkpoint();
        evaluate.throughput(Throughput::Elements(window as u64));
        evaluate.bench_with_input(
            BenchmarkId::from_parameter(window),
            &window,
            |bencher, _| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let candidate = request(CANDIDATE, Action::Release, TARGET);
                        let start = Instant::now();
                        let decision = validator.check(black_box(candidate)).unwrap();
                        elapsed += start.elapsed();
                        assert!(decision.is_grant());
                        validator.rollback(checkpoint).unwrap();
                    }
                    elapsed
                });
            },
        );
    }
    evaluate.finish();
}

fn benchmark_many_rules_stress(criterion: &mut Criterion) {
    const HISTORY_LEN: usize = 64;
    const RULE_COUNTS: [usize; 5] = [1, 16, 64, 256, 1_024];

    let mut compile = criterion.benchmark_group("stress_many_rules_compile");
    compile
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3))
        .sample_size(10);
    for rule_count in RULE_COUNTS {
        compile.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &rule_count,
            |bencher, &rule_count| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let rules = (0..rule_count).map(absent_witness_rule).collect::<Vec<_>>();
                        let store = Arc::new(Store::new().unwrap());
                        let start = Instant::now();
                        let mut builder = Validator::builder(Arc::clone(&store));
                        for rule in rules {
                            builder.add_rule(rule).expect("stress rule is valid");
                        }
                        let validator = builder.finish().unwrap();
                        black_box(&validator);
                        elapsed += start.elapsed();
                    }
                    elapsed
                });
            },
        );
    }
    compile.finish();

    let mut evaluate = criterion.benchmark_group("stress_many_rules_evaluate");
    evaluate
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3))
        .sample_size(10);
    for rule_count in RULE_COUNTS {
        let store = Arc::new(Store::new().unwrap());
        let mut builder = Validator::builder(Arc::clone(&store));
        for index in 0..rule_count {
            builder
                .add_rule(absent_witness_rule(index))
                .expect("stress rule is valid");
        }
        let mut validator = builder.finish().unwrap();
        for _ in 0..HISTORY_LEN {
            assert!(
                validator
                    .check(request(HISTORY, Action::Read, EVENT))
                    .unwrap()
                    .is_grant()
            );
        }
        let checkpoint = validator.checkpoint();
        evaluate.throughput(Throughput::Elements(
            rule_count
                .checked_mul(HISTORY_LEN)
                .expect("stress work count fits u64") as u64,
        ));
        evaluate.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &rule_count,
            |bencher, _| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let candidate = request(CANDIDATE, Action::Release, TARGET);
                        let start = Instant::now();
                        let decision = validator.check(black_box(candidate)).unwrap();
                        elapsed += start.elapsed();
                        assert!(decision.is_grant());
                        validator.rollback(checkpoint).unwrap();
                    }
                    elapsed
                });
            },
        );
    }
    evaluate.finish();
}

fn benchmark_compilation(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("compile_rules");
    for count in [1_usize, 16, 64] {
        group.bench_with_input(
            BenchmarkId::from_parameter(count),
            &count,
            |bencher, &count| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let rules: Vec<Rule<LockEvent<Actor, Path>>> =
                            (0..count).map(prior_edit_rule).collect();
                        let store = Arc::new(Store::new().unwrap());
                        let start = Instant::now();
                        let mut builder = Validator::builder(Arc::clone(&store));
                        for rule in rules {
                            builder.add_rule(rule).expect("benchmark rule is valid");
                        }
                        let validator = builder.finish().unwrap();
                        black_box(&validator);
                        elapsed += start.elapsed();
                        drop(validator);
                    }
                    elapsed
                });
            },
        );
    }
    group.finish();
}

fn validator_with_edit_history(
    store: Arc<Store<LockEvent<Actor, Path>>>,
    history_len: usize,
) -> Validator<LockEvent<Actor, Path>> {
    let mut builder = Validator::builder(store);
    builder
        .add_rule(prior_edit_rule(0))
        .expect("benchmark rule is valid");
    let mut validator = builder.finish().unwrap();
    for _ in 0..history_len {
        let decision = validator
            .check(request(ALICE, Action::Edit, SRC_A))
            .unwrap();
        debug_assert!(decision.is_grant());
    }
    validator
}

fn benchmark_history_scan(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("history_scan");
    for history_len in [1_usize, 32, 256] {
        let store = Arc::new(Store::new().unwrap());
        let mut validator = validator_with_edit_history(Arc::clone(&store), history_len);
        let checkpoint = validator.checkpoint();
        group.bench_with_input(
            BenchmarkId::from_parameter(history_len),
            &history_len,
            |bencher, _| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let candidate = request(ALICE, Action::Release, SRC_A);
                        let start = Instant::now();
                        let decision = validator.check(black_box(candidate)).unwrap();
                        elapsed += start.elapsed();
                        debug_assert!(decision.is_grant());
                        validator.rollback(checkpoint).unwrap();
                    }
                    elapsed
                });
            },
        );
    }
    group.finish();
}

fn benchmark_denial(criterion: &mut Criterion) {
    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder
        .add_rule(duplicate_remove_rule())
        .expect("benchmark rule is valid");
    let mut validator = builder.finish().unwrap();
    let first = validator.check(request(ALICE, Action::Remove, A)).unwrap();
    debug_assert!(first.is_grant());

    criterion.bench_function("deny_duplicate_remove", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..iterations {
                let candidate = request(ALICE, Action::Remove, A);
                let start = Instant::now();
                let decision = validator.check(black_box(candidate)).unwrap();
                elapsed += start.elapsed();
                debug_assert!(matches!(decision, Decision::Denied(_)));
            }
            elapsed
        });
    });
}

fn benchmark_rollback(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("rollback");
    for removed_events in [1_usize, 64, 1024] {
        let store = Arc::new(Store::new().unwrap());
        group.bench_with_input(
            BenchmarkId::from_parameter(removed_events),
            &removed_events,
            |bencher, &removed_events| {
                bencher.iter_batched(
                    || {
                        let mut validator =
                            Validator::builder(Arc::clone(&store)).finish().unwrap();
                        let checkpoint = validator.checkpoint();
                        for _ in 0..removed_events {
                            let decision =
                                validator.check(request(ALICE, Action::Read, A)).unwrap();
                            debug_assert!(decision.is_grant());
                        }
                        (validator, checkpoint)
                    },
                    |(mut validator, checkpoint)| {
                        validator.rollback(checkpoint).unwrap();
                        black_box(validator);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    benchmark_compilation,
    benchmark_history_scan,
    benchmark_million_event_nested_scan,
    benchmark_high_cardinality_scan,
    benchmark_advancing_derivatives,
    benchmark_growing_residual_stress,
    benchmark_many_rules_stress,
    benchmark_denial,
    benchmark_rollback,
);
criterion_main!(benches);
