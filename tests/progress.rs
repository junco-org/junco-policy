//! Public contracts of caller-defined tagged events and retained history progress.

use std::cell::Cell;
use std::fmt;
use std::panic::{AssertUnwindSafe, catch_unwind};

use junco_policy::{
    Action, AtomPattern, Bump, Comparison, ComponentPattern, Coprod, Coproduct, Decision, Event,
    GitPolicy, Head, History, MessageId, PolicyDecision, RegexExpr, Request, Rule, RuleMode,
    TestExpr, Validator, git_decision, git_event,
};

/// Caller-assigned principal identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Actor(u32);

impl fmt::Display for Actor {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "actor{}", self.0)
    }
}

/// Caller-assigned resource identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Doc(u32);

impl fmt::Display for Doc {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "doc{}", self.0)
    }
}

const ALICE: Actor = Actor(1);
const BOB: Actor = Actor(2);
const A: Doc = Doc(1);
const B: Doc = Doc(2);

fn action_is<E: Event<Action = Action>>(action: Action) -> TestExpr<E> {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

/// Head matching every `Stage` candidate, binding its principal `actor` and resource `doc`.
fn stage_head<E: Event<Action = Action>>() -> Head<E> {
    Head::new(
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(Action::Stage),
        ComponentPattern::variable("doc"),
    )
}

/// `All · T · All`.
fn contains<E: Event>(test: TestExpr<E>) -> RegexExpr<E> {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(test), RegexExpr::all()])
}

/// Stage requires an earlier edit of the same resource by the same principal.
fn prior_edit<E: Event<Action = Action>>() -> Rule<E> {
    let same_edit = TestExpr::and([
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("actor")),
        ),
        action_is(Action::Edit),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::variable("doc")),
        ),
    ]);
    Rule::new(RuleMode::Require, stage_head(), contains(same_edit))
}

fn validator_with<'arena, E>(arena: &'arena Bump, rules: &[Rule<E>]) -> Validator<'arena, E>
where
    E: Event + 'arena,
{
    let mut builder = Validator::builder(arena);
    for rule in rules {
        builder.add_rule(rule.clone()).expect("test rule compiles");
    }
    builder.finish()
}

/// First violated mode of `candidate` after uncached replay of `history` by a fresh validator.
fn fresh<E: Event>(rules: &[Rule<E>], history: &[E], candidate: &E) -> Option<RuleMode> {
    let arena = Bump::new();
    let mut validator = validator_with(&arena, rules);
    for event in history {
        assert!(
            validator.check(Request::new(*event, ())).is_grant(),
            "fresh replay regrants committed history"
        );
    }
    mode(validator.check(Request::new(*candidate, ())))
}

fn mode<E: Event, M>(decision: Decision<E, M>) -> Option<RuleMode> {
    match decision {
        Decision::Grant(_) => None,
        Decision::Denied(denial) => Some(denial.mode),
    }
}

/// Checks `candidate` with the retained validator and asserts the fresh-replay verdict and mode.
fn check_matches_fresh<'arena, E>(
    validator: &mut Validator<'arena, E>,
    rules: &[Rule<E>],
    candidate: E,
) -> Option<RuleMode>
where
    E: Event + 'arena,
{
    let expected = fresh(rules, validator.history(), &candidate);
    let retained = mode(validator.check(Request::new(candidate, ())));
    assert_eq!(retained, expected, "{candidate:?}");
    retained
}

macro_rules! payload {
    ($name:ident, $action:expr) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct $name {
            actor: Actor,
            doc: Doc,
        }

        impl Event for $name {
            type Principal = Actor;
            type Action = Action;
            type Resource = Doc;

            fn principal(self) -> Actor {
                self.actor
            }

            fn action(self) -> Action {
                $action
            }

            fn resource(self) -> Doc {
                self.doc
            }
        }
    };
}

payload!(ReadPayload, Action::Read);
payload!(EditPayload, Action::Edit);
payload!(ApprovalPayload, Action::Diff);
payload!(ProbePayload, Action::Stage);

fn read(
    actor: Actor,
    doc: Doc,
) -> Coprod!(ReadPayload, EditPayload, ApprovalPayload, ProbePayload) {
    Coproduct::inject(ReadPayload { actor, doc })
}

fn edit(
    actor: Actor,
    doc: Doc,
) -> Coprod!(ReadPayload, EditPayload, ApprovalPayload, ProbePayload) {
    Coproduct::inject(EditPayload { actor, doc })
}

fn approve(
    actor: Actor,
    doc: Doc,
) -> Coprod!(ReadPayload, EditPayload, ApprovalPayload, ProbePayload) {
    Coproduct::inject(ApprovalPayload { actor, doc })
}

fn probe(
    actor: Actor,
    doc: Doc,
) -> Coprod!(ReadPayload, EditPayload, ApprovalPayload, ProbePayload) {
    Coproduct::inject(ProbePayload { actor, doc })
}

#[test]
fn caller_coproduct_events_keep_full_component_identity() {
    let rules = [prior_edit()];
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);

    assert!(!validator.permits(&probe(ALICE, A)));
    for event in [read(BOB, A), approve(BOB, A), edit(ALICE, A)] {
        assert!(validator.check(Request::new(event, ())).is_grant());
    }
    assert!(validator.permits(&probe(ALICE, A)));
    assert!(!validator.permits(&probe(BOB, A)));
    assert!(!validator.permits(&probe(ALICE, B)));
    for candidate in [probe(ALICE, A), probe(BOB, A), probe(ALICE, B)] {
        assert_eq!(
            validator.permits(&candidate),
            fresh(&rules, validator.history(), &candidate).is_none()
        );
    }
}

#[test]
fn exact_commit_message_identity_is_part_of_event_equality() {
    let committed = git_event(ALICE, Action::commit(MessageId(1)), A);
    for (required, accepted) in [
        (Action::commit(MessageId(1)), true),
        (Action::commit_without_message(), false),
        (Action::commit(MessageId(2)), false),
    ] {
        let rules = [Rule::new(
            RuleMode::Require,
            stage_head(),
            contains(action_is(required)),
        )];
        let arena = Bump::new();
        let mut validator = validator_with(&arena, &rules);
        assert!(validator.check(Request::new(committed, ())).is_grant());
        assert_eq!(
            validator.permits(&git_event(ALICE, Action::Stage, A)),
            accepted,
            "history {committed:?} against required {required}"
        );
    }
}

#[test]
fn cached_residual_advances_at_every_appended_event() {
    // Probe-only head; `a · All · b` with a = Read, b = Edit, x = Diff.
    let probe_actor = Actor(99);
    let probe_doc = Doc(99);
    let rules = [Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::constant(probe_actor),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::constant(probe_doc),
        ),
        RegexExpr::concat([
            RegexExpr::test(action_is(Action::Read)),
            RegexExpr::all(),
            RegexExpr::test(action_is(Action::Edit)),
        ]),
    )];
    let candidate = git_event(probe_actor, Action::Stage, probe_doc);
    let word = [
        Action::Read,
        Action::Edit,
        Action::Edit,
        Action::Diff,
        Action::Edit,
    ];
    let expected = [false, false, true, true, false, true];

    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    for (split, expected) in expected.into_iter().enumerate() {
        for pass in ["first", "repeat"] {
            assert_eq!(
                validator.permits(&candidate),
                expected,
                "{pass} prefix {split}"
            );
        }
        assert_eq!(
            fresh(&rules, validator.history(), &candidate).is_none(),
            expected
        );
        if let Some(&action) = word.get(split) {
            assert!(
                validator
                    .check(Request::new(git_event(ALICE, action, A), ()))
                    .is_grant()
            );
        }
    }
    assert_eq!(validator.history().len(), 5);
}

#[test]
fn rollback_then_same_length_append_does_not_leak_a_warmed_grant() {
    let rules = [prior_edit()];
    let stage = git_event(ALICE, Action::Stage, A);
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);

    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(git_event(ALICE, Action::Edit, A), ()))
            .is_grant()
    );
    assert!(validator.permits(&stage));
    assert!(validator.permits(&stage));

    validator.rollback(before);
    assert!(
        validator
            .check(Request::new(git_event(BOB, Action::Edit, B), ()))
            .is_grant()
    );
    assert_eq!(validator.history().len(), 1);
    assert!(!validator.permits(&stage));
    assert!(fresh(&rules, validator.history(), &stage).is_some());
}

#[test]
fn owners_and_replacements_keep_separate_progress() {
    let arena = Bump::new();
    let mut policy = GitPolicy::new(&arena);
    let stage = git_event(ALICE, Action::Stage, A);

    // Two clones of one empty owner share length and revision but never progress.
    let empty = History::new();
    let mut first = empty.clone();
    let mut second = empty.clone();
    first.push(git_event(ALICE, Action::Edit, A));
    second.push(git_event(BOB, Action::Edit, A));
    assert_eq!(policy.decide(&first, &stage), PolicyDecision::Grant);
    assert_eq!(policy.decide(&first, &stage), PolicyDecision::Grant);
    let denied = policy.decide(&second, &stage);
    assert_ne!(denied, PolicyDecision::Grant);
    assert_eq!(denied, git_decision(&second, &stage));

    // Truncate-and-reappend replaces a warmed branch on one owner.
    let mut owner = History::from_events([git_event(ALICE, Action::Edit, A)]);
    assert_eq!(policy.decide(&owner, &stage), PolicyDecision::Grant);
    assert_eq!(policy.decide(&owner, &stage), PolicyDecision::Grant);
    owner.truncate(0);
    owner.push(git_event(BOB, Action::Edit, A));
    let replaced = policy.decide(&owner, &stage);
    assert_ne!(replaced, PolicyDecision::Grant);
    assert_eq!(replaced, git_decision(&owner, &stage));
}

#[test]
fn foreign_and_future_checkpoints_are_rejected_before_mutation() {
    let events = [
        git_event(ALICE, Action::Read, A),
        git_event(BOB, Action::Read, B),
    ];
    let mut owner = History::from_events(events);
    let other = History::from_events(events);
    let foreign = other.checkpoint();
    assert!(catch_unwind(AssertUnwindSafe(|| owner.rollback(foreign))).is_err());
    assert_eq!(owner.as_slice(), events);

    let clone_checkpoint = owner.clone().checkpoint();
    assert!(catch_unwind(AssertUnwindSafe(|| owner.rollback(clone_checkpoint))).is_err());
    assert_eq!(owner.as_slice(), events);

    let future = owner.checkpoint();
    owner.truncate(1);
    assert!(catch_unwind(AssertUnwindSafe(|| owner.rollback(future))).is_err());
    assert_eq!(owner.as_slice(), &events[..1]);

    owner.truncate(5);
    assert_eq!(owner.as_slice(), &events[..1]);

    // Validators delegate to their owner; denials never append.
    let rules = [prior_edit()];
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    let mut stranger = validator_with(&arena, &rules);
    assert!(
        stranger
            .check(Request::new(git_event(BOB, Action::Read, B), ()))
            .is_grant()
    );
    let stranger_checkpoint = stranger.checkpoint();
    assert!(catch_unwind(AssertUnwindSafe(|| validator.rollback(stranger_checkpoint))).is_err());
    for _ in 0..2 {
        let denied = validator.check(Request::new(git_event(ALICE, Action::Stage, A), ()));
        assert_eq!(mode(denied), Some(RuleMode::Require));
        assert!(validator.history().is_empty());
    }
}

thread_local! {
    /// Action projections of history-marked [`Counted`] events on this test thread.
    static HISTORY_ACTION_PROJECTIONS: Cell<usize> = const { Cell::new(0) };
}

/// Returns and resets this thread's count of history action projections.
fn take_projections() -> usize {
    HISTORY_ACTION_PROJECTIONS.with(|count| count.replace(0))
}

/// Whether a [`Counted`] event is committed history or a probe.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Role {
    History,
    Probe,
}

/// Unique identity of one recorded event.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Sequence(u32);

/// Caller event whose action projection counts reads of committed history.
///
/// Full equality includes the role and sequence, so every recorded event is distinct. The count
/// is test-local observation; projected values are pure and stable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Counted {
    role: Role,
    sequence: Sequence,
    actor: Actor,
    action: Action,
    doc: Doc,
}

impl Event for Counted {
    type Principal = Actor;
    type Action = Action;
    type Resource = Doc;

    fn principal(self) -> Actor {
        self.actor
    }

    fn action(self) -> Action {
        if self.role == Role::History {
            HISTORY_ACTION_PROJECTIONS.with(|count| count.set(count.get() + 1));
        }
        self.action
    }

    fn resource(self) -> Doc {
        self.doc
    }
}

fn recorded(sequence: u32, actor: Actor, action: Action, doc: Doc) -> Counted {
    Counted {
        role: Role::History,
        sequence: Sequence(sequence),
        actor,
        action,
        doc,
    }
}

fn staged(actor: Actor, doc: Doc) -> Counted {
    Counted {
        role: Role::Probe,
        sequence: Sequence(0),
        actor,
        action: Action::Stage,
        doc,
    }
}

#[test]
fn evicted_cursor_rereads_history_and_keeps_its_verdict() {
    let rules = [prior_edit()];
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    assert!(
        validator
            .check(Request::new(recorded(0, ALICE, Action::Edit, A), ()))
            .is_grant()
    );

    let alice = staged(ALICE, A);
    assert!(validator.permits(&alice));
    take_projections();
    assert!(validator.permits(&alice));
    assert_eq!(take_projections(), 0, "a warm cursor reads no history");

    for actor in 100..116 {
        assert!(!validator.permits(&staged(Actor(actor), A)));
    }
    take_projections();
    assert!(validator.permits(&alice));
    assert!(take_projections() > 0, "an evicted cursor refolds history");
    assert!(fresh(&rules, validator.history(), &alice).is_none());
    assert_eq!(validator.history().len(), 1);

    // Opposite verdicts after append and after rollback.
    let bob = staged(BOB, A);
    assert!(!validator.permits(&bob));
    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(recorded(1, BOB, Action::Edit, A), ()))
            .is_grant()
    );
    assert!(validator.permits(&bob));
    assert!(fresh(&rules, validator.history(), &bob).is_none());
    validator.rollback(before);
    assert!(!validator.permits(&bob));
    assert!(fresh(&rules, validator.history(), &bob).is_some());
}

#[test]
fn alternating_bindings_and_owners_change_work_never_verdicts() {
    // Forbid repeating an identical operation; the head binds the action, so every distinct
    // message ID and resource is a distinct cursor key.
    let same_operation = TestExpr::and([
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("actor")),
        ),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Action(ComponentPattern::variable("operation")),
        ),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::variable("doc")),
        ),
    ]);
    let rules = [Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::variable("operation"),
            ComponentPattern::variable("doc"),
        ),
        contains(same_operation),
    )];
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    for message in 0..9 {
        let commit = git_event(
            ALICE,
            Action::commit(MessageId(message)),
            Doc(message as u32 % 3),
        );
        assert!(validator.check(Request::new(commit, ())).is_grant());
    }
    for _ in 0..2 {
        for index in 0..40_u32 {
            let candidate = git_event(
                ALICE,
                Action::commit(MessageId(u64::from(index % 12))),
                Doc(index % 4),
            );
            assert_eq!(
                validator.permits(&candidate),
                fresh(&rules, validator.history(), &candidate).is_none(),
                "{candidate:?}"
            );
        }
    }

    let mut policy = GitPolicy::new(&arena);
    let owners = [
        History::from_events([git_event(ALICE, Action::Edit, A)]),
        History::from_events([git_event(BOB, Action::Edit, A)]),
        History::new(),
    ];
    for _ in 0..2 {
        for index in 0..30_u32 {
            let owner = &owners[index as usize % owners.len()];
            let candidate = git_event(Actor(index % 20), Action::Stage, Doc(index % 2 + 1));
            assert_eq!(
                policy.decide(owner, &candidate),
                git_decision(owner, &candidate)
            );
        }
    }
}

#[test]
fn lagging_rules_resume_independently_after_rollback() {
    let rules = [
        Rule::new(
            RuleMode::Require,
            stage_head(),
            contains(action_is(Action::Edit)),
        ),
        Rule::new(
            RuleMode::Forbid,
            stage_head(),
            contains(action_is(Action::Diff)),
        ),
    ];
    let stage = git_event(ALICE, Action::Stage, A);
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    let empty = validator.checkpoint();

    assert_eq!(
        check_matches_fresh(&mut validator, &rules, git_event(ALICE, Action::Edit, A)),
        None
    );
    assert_eq!(check_matches_fresh(&mut validator, &rules, stage), None);

    validator.rollback(empty);
    assert_eq!(
        check_matches_fresh(&mut validator, &rules, stage),
        Some(RuleMode::Require)
    );

    assert_eq!(
        check_matches_fresh(&mut validator, &rules, git_event(ALICE, Action::Diff, A)),
        None
    );
    assert_eq!(
        check_matches_fresh(&mut validator, &rules, git_event(ALICE, Action::Edit, A)),
        None
    );
    assert_eq!(
        check_matches_fresh(&mut validator, &rules, stage),
        Some(RuleMode::Forbid)
    );
}

#[test]
fn warm_permits_read_no_history_and_one_append_reads_one_event() {
    let rules = [Rule::new(
        RuleMode::Require,
        stage_head(),
        RegexExpr::star(RegexExpr::test(action_is(Action::Read))),
    )];
    let arena = Bump::new();
    let mut validator = validator_with(&arena, &rules);
    for sequence in 0..4_096 {
        let event = recorded(
            sequence,
            Actor(sequence % 7),
            Action::Read,
            Doc(sequence % 5),
        );
        assert!(validator.check(Request::new(event, ())).is_grant());
    }
    let candidate = staged(ALICE, A);

    take_projections();
    assert!(validator.permits(&candidate));
    take_projections();
    for _ in 0..3 {
        assert!(validator.permits(&candidate));
        assert_eq!(take_projections(), 0, "unchanged history is not replayed");
    }

    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(recorded(4_096, BOB, Action::Read, B), ()))
            .is_grant()
    );
    take_projections();
    assert!(validator.permits(&candidate));
    assert_eq!(take_projections(), 1, "one append folds exactly one event");
    assert!(validator.permits(&candidate));
    assert_eq!(take_projections(), 0);

    assert!(
        validator
            .check(Request::new(recorded(4_097, BOB, Action::Edit, B), ()))
            .is_grant()
    );
    assert!(!validator.permits(&candidate));
    validator.rollback(before);
    let expected = fresh(&rules, validator.history(), &candidate).is_none();
    assert!(expected);
    assert_eq!(validator.permits(&candidate), expected);
}
