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
use junco_policy::{
    Action, AtomPattern, Bump, Checkpoint, Comparison, ComponentPattern, Event, GitEvent, Head,
    RegexExpr, Request, Rule, RuleMode, TestExpr, Validator, git_event,
};

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

fn principal_is(comparison: Comparison) -> TestExpr<GitEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::variable("actor")),
    )
}

fn resource_is(comparison: Comparison) -> TestExpr<GitEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::variable("resource")),
    )
}

fn action_is(action: Action, comparison: Comparison) -> TestExpr<GitEvent<Actor, Path>> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

fn stage_head() -> Head<GitEvent<Actor, Path>> {
    Head::new(
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(Action::Stage),
        ComponentPattern::variable("resource"),
    )
}

/// `All · Test(principal = actor ∧ action = Edit ∧ resource = resource) · All`.
fn prior_edit_rule() -> Rule<GitEvent<Actor, Path>> {
    let matching_edit = TestExpr::and([
        principal_is(Comparison::Eq),
        action_is(Action::Edit, Comparison::Eq),
        resource_is(Comparison::Eq),
    ]);
    Rule::new(
        RuleMode::Require,
        stage_head(),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(matching_edit),
            RegexExpr::all(),
        ]),
    )
}

/// `All · Edit(r) · NonEdit(r)* · Approval(r, principal ≠ actor) · NonEdit(r)*`.
fn release_approval_rule() -> Rule<GitEvent<Actor, Path>> {
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
        action_is(Action::Diff, Comparison::Eq),
        principal_is(Comparison::Neq),
    ]);
    Rule::new(
        RuleMode::Require,
        stage_head(),
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
fn prior_edit_event(index: usize, history_len: usize) -> GitEvent<Actor, Path> {
    let action = if index == history_len / 2 {
        Action::Edit
    } else {
        Action::Read
    };
    git_event(ALICE, action, RESOURCE)
}

/// Release-approval seed variants and whether Alice may then stage the resource.
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
fn release_event(case: ReleaseCase, index: usize, history_len: usize) -> GitEvent<Actor, Path> {
    let (mut actor, mut action, mut resource) = (ALICE, Action::Read, RESOURCE);
    if index == history_len / 3 {
        match case {
            ReleaseCase::ApprovalBeforeEdit => (actor, action) = (BOB, Action::Diff),
            ReleaseCase::MissingEdit => {}
            _ => action = Action::Edit,
        }
    } else if index == 2 * history_len / 3 {
        match case {
            ReleaseCase::ApprovalBeforeEdit => action = Action::Edit,
            ReleaseCase::MissingApproval => {}
            ReleaseCase::SelfApproval => action = Action::Diff,
            ReleaseCase::WrongResource => {
                (actor, action, resource) = (BOB, Action::Diff, OTHER_RESOURCE);
            }
            _ => (actor, action) = (BOB, Action::Diff),
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
    git_event(actor, action, resource)
}

/// A seeded validator plus the checkpoint immediately before its final committed event.
struct Scenario<'arena> {
    validator: Validator<'arena, GitEvent<Actor, Path>>,
    before_final: Checkpoint,
    final_event: GitEvent<Actor, Path>,
}

fn seed<'arena>(
    arena: &'arena Bump,
    rule: Rule<GitEvent<Actor, Path>>,
    history_len: usize,
    event: impl Fn(usize) -> GitEvent<Actor, Path>,
) -> Scenario<'arena> {
    let mut builder = Validator::builder(arena);
    builder.add_rule(rule).expect("benchmark rule compiles");
    let mut validator = builder.finish();
    let mut before_final = validator.checkpoint();
    for index in 0..history_len {
        if index + 1 == history_len {
            before_final = validator.checkpoint();
        }
        let decision = validator.check(Request::new(event(index), ()));
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

fn candidate() -> GitEvent<Actor, Path> {
    git_event(ALICE, Action::Stage, RESOURCE)
}

/// Seeds the prior-edit scenario and checks its grant outside timing.
fn prior_edit_scenario(arena: &Bump, history_len: usize) -> Scenario<'_> {
    let mut scenario = seed(arena, prior_edit_rule(), history_len, |index| {
        prior_edit_event(index, history_len)
    });
    assert!(scenario.validator.permits(&candidate()));
    scenario
}

/// Seeds the approved release scenario after preflighting every release verdict outside timing.
fn release_approval_scenario(arena: &Bump, history_len: usize) -> Scenario<'_> {
    for (case, expected) in RELEASE_CASES {
        let case_arena = Bump::new();
        let mut scenario = seed(&case_arena, release_approval_rule(), history_len, |index| {
            release_event(case, index, history_len)
        });
        assert_eq!(
            scenario.validator.permits(&candidate()),
            expected,
            "{case:?}/{history_len}"
        );
    }
    let mut scenario = seed(arena, release_approval_rule(), history_len, |index| {
        release_event(ReleaseCase::Approved, index, history_len)
    });
    assert!(scenario.validator.permits(&candidate()));
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

    fn scenario(self, arena: &Bump, history_len: usize) -> Scenario<'_> {
        match self {
            Self::PriorEdit => prior_edit_scenario(arena, history_len),
            Self::ReleaseApproval => release_approval_scenario(arena, history_len),
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
        "size_of::<GitEvent<Actor, Path>>() = {} bytes",
        size_of::<GitEvent<Actor, Path>>()
    );
    let mut group = configure(criterion, "tagged_replay");
    for workload in Workload::ALL {
        for history_len in HISTORY_LENGTHS {
            let arena = Bump::new();
            let mut scenario = workload.scenario(&arena, history_len);
            assert_eq!(scenario.final_event.action(), Action::Read);
            let candidate = candidate();
            group.bench_function(BenchmarkId::new(workload.name(), history_len), |bencher| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        scenario.validator.rollback(scenario.before_final);
                        let reappended = scenario
                            .validator
                            .check(Request::new(scenario.final_event, ()));
                        assert!(reappended.is_grant());
                        let start = Instant::now();
                        let permitted = scenario.validator.permits(black_box(&candidate));
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
            let arena = Bump::new();
            let mut scenario = workload.scenario(&arena, history_len);
            let candidate = candidate();
            group.bench_function(BenchmarkId::new(workload.name(), history_len), |bencher| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let start = Instant::now();
                        let permitted = scenario.validator.permits(black_box(&candidate));
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
