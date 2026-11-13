//! Instrumented progress checks, run explicitly with the root `test-util` feature.

use super::*;

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
    type Component = LockComponent<Actor, Doc>;
    type Arity = history_syntax::N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => LockComponent::Principal(self.actor),
            1 => LockComponent::Action(self.action),
            _ => LockComponent::Resource(self.doc),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            LockComponent::Principal(_) => 0,
            LockComponent::Action(_) => 1,
            LockComponent::Resource(_) => 2,
        }
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
