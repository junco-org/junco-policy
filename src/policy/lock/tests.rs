//! The lock table, checked against an independent claim-state oracle.

use super::{LockPolicy, lock_decision};
use crate::policy::PolicyDecision;
use crate::{Action, Bump, Event};

const R: [&str; 2] = ["src", "x"];
const ACTIONS: [Action; 4] = [Action::Read, Action::Edit, Action::Release, Action::Remove];

/// Which principal, if any, holds a claim, seen from the acting principal "self".
#[derive(Clone, Copy, Debug, PartialEq)]
enum Holder {
    Nobody,
    Myself,
    Another,
}

impl Holder {
    fn name(self) -> Option<&'static str> {
        match self {
            Self::Nobody => None,
            Self::Myself => Some("self"),
            Self::Another => Some("other"),
        }
    }
}

/// A history leaving `owner` owning and `reader` last reading `src/x`.
fn history(owner: Holder, reader: Holder) -> Vec<Event> {
    let mut history = Vec::new();
    if let Some(reader) = reader.name() {
        history.push(Event::new(reader, Action::Read, R));
    }
    if let Some(owner) = owner.name() {
        history.push(Event::new(owner, Action::Edit, R));
    }
    history
}

/// `None` grants; `Some(true)` is an owner denial, `Some(false)` a reader denial.
fn oracle(owner: Holder, reader: Holder, action: &Action) -> Option<bool> {
    let owner_blocks = owner == Holder::Another && *action != Action::Read;
    let reader_blocks =
        reader == Holder::Another && matches!(action, Action::Edit | Action::Remove);
    if owner_blocks {
        Some(true)
    } else if reader_blocks {
        Some(false)
    } else {
        None
    }
}

fn verdict(decision: PolicyDecision) -> Option<bool> {
    match decision {
        PolicyDecision::Grant => None,
        PolicyDecision::Deny {
            failed_precondition,
            ..
        } => Some(failed_precondition.contains(" is owned by ")),
    }
}

#[test]
fn lock_decision_matches_the_claim_table_exhaustively() {
    let holders = [Holder::Nobody, Holder::Myself, Holder::Another];
    for owner in holders {
        for reader in holders {
            let history = history(owner, reader);
            for action in &ACTIONS {
                let candidate = Event::new("self", action.clone(), R);
                assert_eq!(
                    verdict(lock_decision(&history, &candidate)),
                    oracle(owner, reader, action),
                    "owner={owner:?} reader={reader:?} action={action}",
                );
            }
        }
    }
}

fn grants(history: &[Event], principal: &str, action: Action) -> bool {
    lock_decision(history, &Event::new(principal, action, R)) == PolicyDecision::Grant
}

#[test]
fn release_clears_only_ownership_and_remove_clears_both_claims() {
    let read_then_edit = vec![
        Event::new("other", Action::Read, R),
        Event::new("other", Action::Edit, R),
    ];

    let mut released = read_then_edit.clone();
    released.push(Event::new("other", Action::Release, R));
    // The owner is gone, but the reader claim survives a release.
    assert!(grants(&released, "self", Action::Release));
    assert!(!grants(&released, "self", Action::Edit));
    assert!(!grants(&released, "self", Action::Remove));

    let mut removed = read_then_edit;
    removed.push(Event::new("other", Action::Remove, R));
    // Recreating a removed name needs no read of a missing file.
    assert!(grants(&removed, "self", Action::Edit));
    assert!(grants(&removed, "self", Action::Remove));

    // A release then a fresh edit reacquires ownership.
    released.push(Event::new("other", Action::Edit, R));
    assert!(!grants(&released, "self", Action::Release));
    // Claims on another resource never interfere.
    assert!(
        lock_decision(&released, &Event::new("self", Action::Edit, ["src", "y"]))
            == PolicyDecision::Grant
    );
}

#[test]
fn retained_policy_matches_one_shot_decisions_across_history_updates() {
    let arena = Bump::new();
    let mut policy = LockPolicy::new(&arena);
    let mut history = Vec::new();
    let candidates = [
        Event::new("self", Action::Edit, R),
        Event::new("other", Action::Release, R),
        Event::new("other", Action::Read, R),
        Event::new("self", Action::Release, R),
        Event::new("self", Action::Edit, R),
        Event::new("other", Action::Edit, R),
        Event::new("other", Action::Remove, R),
        Event::new("self", Action::Read, R),
        Event::new("self", Action::Remove, R),
        Event::new("other", Action::Edit, R),
    ];

    for candidate in candidates {
        let expected = lock_decision(&history, &candidate);
        let actual = policy.decide(&history, &candidate);
        assert_eq!(actual, expected);
        if actual == PolicyDecision::Grant {
            history.push(candidate);
        }
    }
}
