//! Public contracts of caller-defined tagged events and retained history progress.

use std::fmt;

use history_semantics::{Decision, PolicyDecision, Validator};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Coprod, Coproduct, Event, Head, RegexExpr, Rule,
    RuleMode, TestExpr,
};
use junco_core::{HistoryError, Request};
use junco_policy::{Action, LockEvent, LockPolicy, lock_decision};
use std::sync::Arc;

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
const OPERATIONS: [Action; 4] = [Action::Read, Action::Edit, Action::Release, Action::Remove];

fn action_is<E: Event<Action = Action>>(action: Action) -> TestExpr<E> {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

/// Head matching every `Release` candidate, binding its principal `actor` and resource `doc`.
fn release_head<E: Event<Action = Action>>() -> Head<E> {
    Head::new(
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(Action::Release),
        ComponentPattern::variable("doc"),
    )
}

/// `All · T · All`.
fn contains<E: Event>(test: TestExpr<E>) -> RegexExpr<E> {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(test), RegexExpr::all()])
}

/// Release requires an earlier edit of the same resource by the same principal.
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
    Rule::new(RuleMode::Require, release_head(), contains(same_edit))
}

fn validator_with<E>(store: Arc<Store<E>>, rules: &[Rule<E>]) -> Validator<E>
where
    E: Event,
{
    let mut builder = Validator::builder(store);
    for rule in rules {
        builder.add_rule(rule.clone()).expect("test rule compiles");
    }
    builder.finish().unwrap()
}

/// First violated mode of `candidate` after uncached replay of `history` by a fresh validator.
fn fresh<E: Event>(rules: &[Rule<E>], history: &[E], candidate: &E) -> Option<RuleMode> {
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), rules);
    for event in history {
        assert!(
            validator
                .check(Request::new(*event, ()))
                .unwrap()
                .is_grant(),
            "fresh replay regrants committed history"
        );
    }
    mode(validator.check(Request::new(*candidate, ())).unwrap())
}

fn mode<E: Event, M>(decision: Decision<E, M>) -> Option<RuleMode> {
    match decision {
        Decision::Grant(_) => None,
        Decision::Denied(denial) => Some(denial.mode),
    }
}

/// Checks `candidate` with the retained validator and asserts the fresh-replay verdict and mode.
fn check_matches_fresh<E>(
    validator: &mut Validator<E>,
    rules: &[Rule<E>],
    candidate: E,
) -> Option<RuleMode>
where
    E: Event,
{
    let expected = fresh(rules, validator.history(), &candidate);
    let retained = mode(validator.check(Request::new(candidate, ())).unwrap());
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
payload!(ApprovalPayload, Action::Remove);
payload!(ProbePayload, Action::Release);

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
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);

    assert!(!validator.permits(&probe(ALICE, A)).unwrap());
    for event in [read(BOB, A), approve(BOB, A), edit(ALICE, A)] {
        assert!(validator.check(Request::new(event, ())).unwrap().is_grant());
    }
    assert!(validator.permits(&probe(ALICE, A)).unwrap());
    assert!(!validator.permits(&probe(BOB, A)).unwrap());
    assert!(!validator.permits(&probe(ALICE, B)).unwrap());
    for candidate in [probe(ALICE, A), probe(BOB, A), probe(ALICE, B)] {
        assert_eq!(
            validator.permits(&candidate).unwrap(),
            fresh(&rules, validator.history(), &candidate).is_none()
        );
    }
}

#[test]
fn cached_residual_advances_at_every_appended_event() {
    // Probe-only head; `a · All · b` with a = Read, b = Edit, x = Remove.
    let probe_actor = Actor(99);
    let probe_doc = Doc(99);
    let rules = [Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::constant(probe_actor),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::constant(probe_doc),
        ),
        RegexExpr::concat([
            RegexExpr::test(action_is(Action::Read)),
            RegexExpr::all(),
            RegexExpr::test(action_is(Action::Edit)),
        ]),
    )];
    let candidate = LockEvent::new(probe_actor, Action::Release, probe_doc);
    let word = [
        Action::Read,
        Action::Edit,
        Action::Edit,
        Action::Remove,
        Action::Edit,
    ];
    let expected = [false, false, true, true, false, true];

    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    for (split, expected) in expected.into_iter().enumerate() {
        for pass in ["first", "repeat"] {
            assert_eq!(
                validator.permits(&candidate).unwrap(),
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
                    .check(Request::new(LockEvent::new(ALICE, action, A), ()))
                    .unwrap()
                    .is_grant()
            );
        }
    }
    assert_eq!(validator.history().len(), 5);
}

#[test]
fn rollback_then_same_length_append_does_not_leak_a_warmed_grant() {
    let rules = [prior_edit()];
    let release = LockEvent::new(ALICE, Action::Release, A);
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);

    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(LockEvent::new(ALICE, Action::Edit, A), ()))
            .unwrap()
            .is_grant()
    );
    assert!(validator.permits(&release).unwrap());
    assert!(validator.permits(&release).unwrap());

    validator.rollback(before).unwrap();
    assert!(
        validator
            .check(Request::new(LockEvent::new(BOB, Action::Edit, B), ()))
            .unwrap()
            .is_grant()
    );
    assert_eq!(validator.history().len(), 1);
    assert!(!validator.permits(&release).unwrap());
    assert!(fresh(&rules, validator.history(), &release).is_some());
}

#[test]
fn owners_and_replacements_keep_separate_progress() {
    let store = Arc::new(Store::new().unwrap());
    let mut policy = LockPolicy::new(Arc::clone(&store)).unwrap();
    let release = LockEvent::new(ALICE, Action::Release, A);

    // Two clones of one empty owner share length and revision but never progress.
    let empty = History::new(Arc::clone(&store)).unwrap();
    let mut first = empty.try_clone().unwrap();
    let mut second = empty.try_clone().unwrap();
    first.push(LockEvent::new(ALICE, Action::Edit, A)).unwrap();
    second.push(LockEvent::new(BOB, Action::Edit, A)).unwrap();
    assert_eq!(
        policy.decide(&first, &release).unwrap(),
        PolicyDecision::Grant
    );
    assert_eq!(
        policy.decide(&first, &release).unwrap(),
        PolicyDecision::Grant
    );
    let denied = policy.decide(&second, &release).unwrap();
    assert_ne!(denied, PolicyDecision::Grant);
    assert_eq!(denied, lock_decision(&second, &release).unwrap());

    // Truncate-and-reappend replaces a warmed branch on one owner.
    let mut owner =
        History::from_events(Arc::clone(&store), [LockEvent::new(ALICE, Action::Edit, A)]).unwrap();
    assert_eq!(
        policy.decide(&owner, &release).unwrap(),
        PolicyDecision::Grant
    );
    assert_eq!(
        policy.decide(&owner, &release).unwrap(),
        PolicyDecision::Grant
    );
    owner.truncate(0).unwrap();
    owner.push(LockEvent::new(BOB, Action::Edit, A)).unwrap();
    let replaced = policy.decide(&owner, &release).unwrap();
    assert_ne!(replaced, PolicyDecision::Grant);
    assert_eq!(replaced, lock_decision(&owner, &release).unwrap());
}

#[test]
fn foreign_and_future_checkpoints_are_rejected_before_mutation() {
    let events = [
        LockEvent::new(ALICE, Action::Read, A),
        LockEvent::new(BOB, Action::Read, B),
    ];
    let store = Arc::new(Store::new().unwrap());
    let mut owner = History::from_events(Arc::clone(&store), events).unwrap();
    let other = History::from_events(Arc::clone(&store), events).unwrap();
    let foreign = other.checkpoint();
    assert_eq!(
        owner.rollback(foreign),
        Err(HistoryError::WrongCheckpointOwner)
    );
    assert_eq!(owner.as_slice(), events);

    let clone_checkpoint = owner.try_clone().unwrap().checkpoint();
    assert_eq!(
        owner.rollback(clone_checkpoint),
        Err(HistoryError::WrongCheckpointOwner)
    );
    assert_eq!(owner.as_slice(), events);

    let future = owner.checkpoint();
    owner.truncate(1).unwrap();
    assert_eq!(
        owner.rollback(future),
        Err(HistoryError::CheckpointBeyondHistory)
    );
    assert_eq!(owner.as_slice(), &events[..1]);

    owner.truncate(5).unwrap();
    assert_eq!(owner.as_slice(), &events[..1]);

    // Validators delegate to their owner; denials never append.
    let rules = [prior_edit()];
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    let mut stranger = validator_with(Arc::clone(&store), &rules);
    assert!(
        stranger
            .check(Request::new(LockEvent::new(BOB, Action::Read, B), ()))
            .unwrap()
            .is_grant()
    );
    let stranger_checkpoint = stranger.checkpoint();
    assert_eq!(
        validator.rollback(stranger_checkpoint),
        Err(HistoryError::WrongCheckpointOwner)
    );
    for _ in 0..2 {
        let denied = validator
            .check(Request::new(LockEvent::new(ALICE, Action::Release, A), ()))
            .unwrap();
        assert_eq!(mode(denied), Some(RuleMode::Require));
        assert!(validator.history().is_empty());
    }
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

/// Caller event retaining full identity beyond its projected components.
///
/// Full equality includes the role and sequence, so every recorded event is distinct.
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

fn released(actor: Actor, doc: Doc) -> Counted {
    Counted {
        role: Role::Probe,
        sequence: Sequence(0),
        actor,
        action: Action::Release,
        doc,
    }
}

#[test]
fn evicted_cursor_rereads_history_and_keeps_its_verdict() {
    let rules = [prior_edit()];
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    assert!(
        validator
            .check(Request::new(recorded(0, ALICE, Action::Edit, A), ()))
            .unwrap()
            .is_grant()
    );

    let alice = released(ALICE, A);
    assert!(validator.permits(&alice).unwrap());
    validator.reset_work_events();
    assert!(validator.permits(&alice).unwrap());
    assert_eq!(validator.work_events(), 0, "a warm cursor reads no history");

    for actor in 100..116 {
        assert!(!validator.permits(&released(Actor(actor), A)).unwrap());
    }
    validator.reset_work_events();
    assert!(validator.permits(&alice).unwrap());
    assert_eq!(
        validator.work_events(),
        1,
        "an evicted cursor refolds history"
    );
    validator.reset_work_events();
    assert!(validator.permits(&alice).unwrap());
    assert_eq!(validator.work_events(), 0, "a warm cursor reads no history");
    assert!(fresh(&rules, validator.history(), &alice).is_none());
    assert_eq!(validator.history().len(), 1);

    // Opposite verdicts after append and after rollback.
    let bob = released(BOB, A);
    assert!(!validator.permits(&bob).unwrap());
    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(recorded(1, BOB, Action::Edit, A), ()))
            .unwrap()
            .is_grant()
    );
    assert!(validator.permits(&bob).unwrap());
    assert!(fresh(&rules, validator.history(), &bob).is_none());
    validator.rollback(before).unwrap();
    assert!(!validator.permits(&bob).unwrap());
    assert!(fresh(&rules, validator.history(), &bob).is_some());
}

#[test]
fn alternating_bindings_and_owners_change_work_never_verdicts() {
    // Forbid repeating an identical operation; the head binds the action, so every distinct
    // action and resource is a distinct cursor key.
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
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    // Nine distinct (operation, doc) pairs, so every seed is granted.
    for index in 0..9_u32 {
        let event = LockEvent::new(ALICE, OPERATIONS[index as usize % 4], Doc(index % 3));
        assert!(validator.check(Request::new(event, ())).unwrap().is_grant());
    }
    for _ in 0..2 {
        for index in 0..40_u32 {
            let candidate = LockEvent::new(ALICE, OPERATIONS[index as usize % 4], Doc(index % 6));
            assert_eq!(
                validator.permits(&candidate).unwrap(),
                fresh(&rules, validator.history(), &candidate).is_none(),
                "{candidate:?}"
            );
        }
    }

    let mut policy = LockPolicy::new(Arc::clone(&store)).unwrap();
    let owners = [
        History::from_events(Arc::clone(&store), [LockEvent::new(ALICE, Action::Edit, A)]).unwrap(),
        History::from_events(Arc::clone(&store), [LockEvent::new(BOB, Action::Edit, A)]).unwrap(),
        History::new(Arc::clone(&store)).unwrap(),
    ];
    for _ in 0..2 {
        for index in 0..30_u32 {
            let owner = &owners[index as usize % owners.len()];
            let candidate = LockEvent::new(Actor(index % 20), Action::Release, Doc(index % 2 + 1));
            assert_eq!(
                policy.decide(owner, &candidate).unwrap(),
                lock_decision(owner, &candidate).unwrap()
            );
        }
    }
}

#[test]
fn lagging_rules_resume_independently_after_rollback() {
    let rules = [
        Rule::new(
            RuleMode::Require,
            release_head(),
            contains(action_is(Action::Edit)),
        ),
        Rule::new(
            RuleMode::Forbid,
            release_head(),
            contains(action_is(Action::Remove)),
        ),
    ];
    let release = LockEvent::new(ALICE, Action::Release, A);
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    let empty = validator.checkpoint();

    assert_eq!(
        check_matches_fresh(
            &mut validator,
            &rules,
            LockEvent::new(ALICE, Action::Edit, A)
        ),
        None
    );
    assert_eq!(check_matches_fresh(&mut validator, &rules, release), None);

    validator.rollback(empty).unwrap();
    assert_eq!(
        check_matches_fresh(&mut validator, &rules, release),
        Some(RuleMode::Require)
    );

    assert_eq!(
        check_matches_fresh(
            &mut validator,
            &rules,
            LockEvent::new(ALICE, Action::Remove, A)
        ),
        None
    );
    assert_eq!(
        check_matches_fresh(
            &mut validator,
            &rules,
            LockEvent::new(ALICE, Action::Edit, A)
        ),
        None
    );
    assert_eq!(
        check_matches_fresh(&mut validator, &rules, release),
        Some(RuleMode::Forbid)
    );
}

#[test]
fn warm_permits_read_no_history_and_one_append_reads_one_event() {
    let rules = [Rule::new(
        RuleMode::Require,
        release_head(),
        RegexExpr::star(RegexExpr::test(action_is(Action::Read))),
    )];
    let store = Arc::new(Store::new().unwrap());
    let mut validator = validator_with(Arc::clone(&store), &rules);
    for sequence in 0..4_096 {
        let event = recorded(
            sequence,
            Actor(sequence % 7),
            Action::Read,
            Doc(sequence % 5),
        );
        assert!(validator.check(Request::new(event, ())).unwrap().is_grant());
    }
    let candidate = released(ALICE, A);

    validator.reset_work_events();
    assert!(validator.permits(&candidate).unwrap());
    assert_eq!(validator.work_events(), 4_096);
    validator.reset_work_events();
    for _ in 0..3 {
        validator.reset_work_events();
        assert!(validator.permits(&candidate).unwrap());
        assert_eq!(
            validator.work_events(),
            0,
            "unchanged history is not replayed"
        );
    }

    let before = validator.checkpoint();
    assert!(
        validator
            .check(Request::new(recorded(4_096, BOB, Action::Read, B), ()))
            .unwrap()
            .is_grant()
    );
    validator.reset_work_events();
    assert!(validator.permits(&candidate).unwrap());
    assert_eq!(
        validator.work_events(),
        1,
        "one append folds exactly one event"
    );
    validator.reset_work_events();
    assert!(validator.permits(&candidate).unwrap());
    assert_eq!(validator.work_events(), 0);

    assert!(
        validator
            .check(Request::new(recorded(4_097, BOB, Action::Edit, B), ()))
            .unwrap()
            .is_grant()
    );
    validator.reset_work_events();
    assert!(!validator.permits(&candidate).unwrap());
    assert_eq!(
        validator.work_events(),
        1,
        "rejecting append folds exactly one event"
    );
    validator.rollback(before).unwrap();
    let expected = fresh(&rules, validator.history(), &candidate).is_none();
    assert!(expected);
    assert_eq!(validator.permits(&candidate).unwrap(), expected);
}
