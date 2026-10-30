//! Cold tagged-event replay versus warm residual progress at long committed histories.
//!
//! Both groups time only `Validator::permits`, with `Instant` around that call alone.
//! `tagged_replay` forces a progress-cursor validity miss before every timed call: it rolls back
//! the final committed read and re-appends the identical event through `check` (untimed). The tail
//! is unchanged and derivative tables stay warm, so the timed call replays the whole compact-event
//! history from the root. `progress_warm` decides repeatedly over an unchanged history, so every
//! timed call resumes its cached residual and folds no events.
//!
//! The policies, seeds, and preflight verdicts mirror the cross-repository comparison scenario.

use std::hint::black_box;
use std::mem::size_of;
use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use history_semantics::Validator;
use history_store::{Checkpoint, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use junco_core::Request;
use junco_policy::{Action, LockEvent};
use std::sync::Arc;

const HISTORY_LENGTHS: [usize; 4] = [16, 4096, 8192, 16384];

/// Benchmark principal identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Actor(u32);

/// Benchmark resource identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Path(u32);

const ALICE: Actor = Actor(0);
const BOB: Actor = Actor(1);
const RESOURCE: Path = Path(0);
const OTHER_RESOURCE: Path = Path(1);

fn principal_is(comparison: Comparison) -> TestExpr<LockEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::variable("actor")),
    )
}

fn resource_is(comparison: Comparison) -> TestExpr<LockEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::variable("resource")),
    )
}

fn action_is(action: Action, comparison: Comparison) -> TestExpr<LockEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

fn release_head() -> Head<LockEvent<Actor, Path>> {
    Head::new(
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(Action::Release),
        ComponentPattern::variable("resource"),
    )
}

/// `All · Test(principal = actor ∧ action = Edit ∧ resource = resource) · All`.
fn prior_edit_rule() -> Rule<LockEvent<Actor, Path>> {
    let matching_edit = TestExpr::and([
        principal_is(Comparison::Eq),
        action_is(Action::Edit, Comparison::Eq),
        resource_is(Comparison::Eq),
    ]);
    Rule::new(
        RuleMode::Require,
        release_head(),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(matching_edit),
            RegexExpr::all(),
        ]),
    )
}

/// `All · Edit(r) · NonEdit(r)* · Approval(r, principal ≠ actor) · NonEdit(r)*`.
fn release_approval_rule() -> Rule<LockEvent<Actor, Path>> {
    let edit = TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(Action::Edit, Comparison::Eq),
    ]);
    let non_edit = TestExpr::or([
        resource_is(Comparison::Neq),
        action_is(Action::Edit, Comparison::Neq),
    ]);
    let approval = TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(Action::Remove, Comparison::Eq),
        principal_is(Comparison::Neq),
    ]);
    Rule::new(
        RuleMode::Require,
        release_head(),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(edit),
            RegexExpr::star(RegexExpr::test(non_edit.clone())),
            RegexExpr::test(approval),
            RegexExpr::star(RegexExpr::test(non_edit)),
        ]),
    )
}

/// Alice reads throughout, with her matching edit at the midpoint.
fn prior_edit_event(index: usize, history_len: usize) -> LockEvent<Actor, Path> {
    let action = if index == history_len / 2 {
        Action::Edit
    } else {
        Action::Read
    };
    LockEvent::new(ALICE, action, RESOURCE)
}

/// Release-approval seed variants and whether Alice may then release the resource.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReleaseCase {
    Approved,
    StaleApproval,
    SelfApproval,
    WrongResource,
    MissingApproval,
    MissingEdit,
    ApprovalBeforeEdit,
    UnrelatedEditAfterApproval,
}

const RELEASE_CASES: [(ReleaseCase, bool); 8] = [
    (ReleaseCase::Approved, true),
    (ReleaseCase::StaleApproval, false),
    (ReleaseCase::SelfApproval, false),
    (ReleaseCase::WrongResource, false),
    (ReleaseCase::MissingApproval, false),
    (ReleaseCase::MissingEdit, false),
    (ReleaseCase::ApprovalBeforeEdit, false),
    (ReleaseCase::UnrelatedEditAfterApproval, true),
];

/// Alice reads throughout; her edit sits at one third and Bob's approval at two thirds.
fn release_event(case: ReleaseCase, index: usize, history_len: usize) -> LockEvent<Actor, Path> {
    let (mut actor, mut action, mut resource) = (ALICE, Action::Read, RESOURCE);
    if index == history_len / 3 {
        match case {
            ReleaseCase::ApprovalBeforeEdit => (actor, action) = (BOB, Action::Remove),
            ReleaseCase::MissingEdit => {}
            _ => action = Action::Edit,
        }
    } else if index == 2 * history_len / 3 {
        match case {
            ReleaseCase::ApprovalBeforeEdit => action = Action::Edit,
            ReleaseCase::MissingApproval => {}
            ReleaseCase::SelfApproval => action = Action::Remove,
            ReleaseCase::WrongResource => {
                (actor, action, resource) = (BOB, Action::Remove, OTHER_RESOURCE);
            }
            _ => (actor, action) = (BOB, Action::Remove),
        }
    } else if index == history_len - 1 {
        match case {
            ReleaseCase::StaleApproval => action = Action::Edit,
            ReleaseCase::UnrelatedEditAfterApproval => {
                (action, resource) = (Action::Edit, OTHER_RESOURCE);
            }
            _ => {}
        }
    }
    LockEvent::new(actor, action, resource)
}

/// A seeded validator plus the checkpoint immediately before its final committed event.
struct Scenario {
    validator: Validator<LockEvent<Actor, Path>>,
    before_final: Checkpoint,
    final_event: LockEvent<Actor, Path>,
}

fn seed(
    store: Arc<Store<LockEvent<Actor, Path>>>,
    rule: Rule<LockEvent<Actor, Path>>,
    history_len: usize,
    event: impl Fn(usize) -> LockEvent<Actor, Path>,
) -> Scenario {
    let mut builder = Validator::builder(store);
    builder.add_rule(rule).expect("benchmark rule compiles");
    let mut validator = builder.finish().unwrap();
    let mut before_final = validator.checkpoint();
    for index in 0..history_len {
        if index + 1 == history_len {
            before_final = validator.checkpoint();
        }
        let decision = validator.check(Request::new(event(index), ())).unwrap();
        assert!(decision.is_grant(), "seed history must be accepted");
    }
    assert_eq!(validator.history().len(), history_len);
    let final_event = *validator
        .history()
        .last()
        .expect("benchmarked histories are non-empty");
    Scenario {
        validator,
        before_final,
        final_event,
    }
}

fn candidate() -> LockEvent<Actor, Path> {
    LockEvent::new(ALICE, Action::Release, RESOURCE)
}

/// Seeds the prior-edit scenario and checks its grant outside timing.
fn prior_edit_scenario(store: Arc<Store<LockEvent<Actor, Path>>>, history_len: usize) -> Scenario {
    let mut scenario = seed(store, prior_edit_rule(), history_len, |index| {
        prior_edit_event(index, history_len)
    });
    assert!(scenario.validator.permits(&candidate()).unwrap());
    scenario
}

/// Seeds the approved release scenario after preflighting every release verdict outside timing.
fn release_approval_scenario(
    store: Arc<Store<LockEvent<Actor, Path>>>,
    history_len: usize,
) -> Scenario {
    for (case, expected) in RELEASE_CASES {
        let case_store = Arc::new(Store::new().unwrap());
        let mut scenario = seed(case_store, release_approval_rule(), history_len, |index| {
            release_event(case, index, history_len)
        });
        assert_eq!(
            scenario.validator.permits(&candidate()).unwrap(),
            expected,
            "{case:?}/{history_len}"
        );
    }
    let mut scenario = seed(store, release_approval_rule(), history_len, |index| {
        release_event(ReleaseCase::Approved, index, history_len)
    });
    assert!(scenario.validator.permits(&candidate()).unwrap());
    scenario
}

/// Benchmarked policy workload.
#[derive(Clone, Copy)]
enum Workload {
    PriorEdit,
    ReleaseApproval,
}

impl Workload {
    const ALL: [Self; 2] = [Self::PriorEdit, Self::ReleaseApproval];

    fn name(self) -> &'static str {
        match self {
            Self::PriorEdit => "prior_edit",
            Self::ReleaseApproval => "release_approval",
        }
    }

    fn scenario(self, store: Arc<Store<LockEvent<Actor, Path>>>, history_len: usize) -> Scenario {
        match self {
            Self::PriorEdit => prior_edit_scenario(store, history_len),
            Self::ReleaseApproval => release_approval_scenario(store, history_len),
        }
    }
}

fn configure<'criterion>(
    criterion: &'criterion mut Criterion,
    name: &str,
) -> criterion::BenchmarkGroup<'criterion, criterion::measurement::WallTime> {
    let mut group = criterion.benchmark_group(name);
    group
        .warm_up_time(Duration::from_millis(500))
        .measurement_time(Duration::from_secs(2))
        .sample_size(30);
    group
}

fn tagged_replay(criterion: &mut Criterion) {
    eprintln!(
        "size_of::<LockEvent<Actor, Path>>() = {} bytes",
        size_of::<LockEvent<Actor, Path>>()
    );
    let mut group = configure(criterion, "tagged_replay");
    for workload in Workload::ALL {
        for history_len in HISTORY_LENGTHS {
            let store = Arc::new(Store::new().unwrap());
            let mut scenario = workload.scenario(store, history_len);
            assert_eq!(scenario.final_event.action(), Action::Read);
            let candidate = candidate();
            group.bench_function(BenchmarkId::new(workload.name(), history_len), |bencher| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        scenario.validator.rollback(scenario.before_final).unwrap();
                        let reappended = scenario
                            .validator
                            .check(Request::new(scenario.final_event, ()))
                            .unwrap();
                        assert!(reappended.is_grant());
                        let start = Instant::now();
                        let permitted = scenario.validator.permits(black_box(&candidate)).unwrap();
                        elapsed += start.elapsed();
                        assert!(permitted);
                    }
                    elapsed
                });
            });
        }
    }
    group.finish();
}

fn progress_warm(criterion: &mut Criterion) {
    let mut group = configure(criterion, "progress_warm");
    for workload in Workload::ALL {
        for history_len in HISTORY_LENGTHS {
            let store = Arc::new(Store::new().unwrap());
            let mut scenario = workload.scenario(store, history_len);
            let candidate = candidate();
            group.bench_function(BenchmarkId::new(workload.name(), history_len), |bencher| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let start = Instant::now();
                        let permitted = scenario.validator.permits(black_box(&candidate)).unwrap();
                        elapsed += start.elapsed();
                        assert!(permitted);
                    }
                    elapsed
                });
            });
        }
    }
    group.finish();
}

criterion_group!(benches, tagged_replay, progress_warm);
criterion_main!(benches);
