//! The lock table, checked against an independent claim-state oracle.

use std::fmt;
use std::sync::Arc;

use history_semantics::PolicyDecision;
use history_store::{History, Store};
use junco_core::HistoryError;

use super::{LockPolicy, lock_decision};
use crate::{Action, LockEvent};

const ACTIONS: [Action; 4] = [Action::Read, Action::Edit, Action::Release, Action::Remove];

/// The two principals the oracle names; the acting principal is always "self".
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Who {
    Me,
    Other,
}

impl fmt::Display for Who {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Me => "self",
            Self::Other => "other",
        })
    }
}

/// The protected resource `src/x` and an unrelated `src/y`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Path {
    X,
    Y,
}

impl fmt::Display for Path {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::X => "src/x",
            Self::Y => "src/y",
        })
    }
}

type Lock = LockEvent<Who, Path>;

fn store() -> Arc<Store<Lock>> {
    Arc::new(Store::new().unwrap())
}

fn on_x(who: Who, action: Action) -> Lock {
    LockEvent::new(who, action, Path::X)
}

/// Which principal, if any, holds a claim, seen from the acting principal "self".
#[derive(Clone, Copy, Debug, PartialEq)]
enum Holder {
    Nobody,
    Myself,
    Another,
}

impl Holder {
    fn who(self) -> Option<Who> {
        match self {
            Self::Nobody => None,
            Self::Myself => Some(Who::Me),
            Self::Another => Some(Who::Other),
        }
    }
}

/// A history leaving `owner` owning and `reader` last reading `src/x`.
fn history(owner: Holder, reader: Holder) -> History<Lock> {
    History::from_events(
        store(),
        [
            reader.who().map(|reader| on_x(reader, Action::Read)),
            owner.who().map(|owner| on_x(owner, Action::Edit)),
        ]
        .into_iter()
        .flatten(),
    )
    .unwrap()
}

/// `None` grants; `Some(true)` is an owner denial, `Some(false)` a reader denial.
fn oracle(owner: Holder, reader: Holder, action: Action) -> Option<bool> {
    let owner_blocks = owner == Holder::Another && action != Action::Read;
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
            for action in ACTIONS {
                assert_eq!(
                    verdict(lock_decision(&history, &on_x(Who::Me, action)).unwrap()),
                    oracle(owner, reader, action),
                    "owner={owner:?} reader={reader:?} action={action}",
                );
            }
        }
    }
}

fn grants(history: &History<Lock>, principal: Who, action: Action) -> bool {
    lock_decision(history, &on_x(principal, action)).unwrap() == PolicyDecision::Grant
}

#[test]
fn release_clears_only_ownership_and_remove_clears_both_claims() {
    let read_then_edit = [
        on_x(Who::Other, Action::Read),
        on_x(Who::Other, Action::Edit),
    ];

    let mut released = History::from_events(store(), read_then_edit).unwrap();
    released.push(on_x(Who::Other, Action::Release)).unwrap();
    // The owner is gone, but the reader claim survives a release.
    assert!(grants(&released, Who::Me, Action::Release));
    assert!(!grants(&released, Who::Me, Action::Edit));
    assert!(!grants(&released, Who::Me, Action::Remove));

    let mut removed = History::from_events(store(), read_then_edit).unwrap();
    removed.push(on_x(Who::Other, Action::Remove)).unwrap();
    // Recreating a removed name needs no read of a missing file.
    assert!(grants(&removed, Who::Me, Action::Edit));
    assert!(grants(&removed, Who::Me, Action::Remove));

    // A release then a fresh edit reacquires ownership.
    released.push(on_x(Who::Other, Action::Edit)).unwrap();
    assert!(!grants(&released, Who::Me, Action::Release));
    // Claims on another resource never interfere.
    assert_eq!(
        lock_decision(&released, &LockEvent::new(Who::Me, Action::Edit, Path::Y)).unwrap(),
        PolicyDecision::Grant
    );
}

#[test]
fn retained_policy_matches_one_shot_decisions_across_history_updates() {
    let store = store();
    let mut policy = LockPolicy::new(store.clone()).unwrap();
    let mut history = History::new(store).unwrap();
    let candidates = [
        on_x(Who::Me, Action::Edit),
        on_x(Who::Other, Action::Release),
        on_x(Who::Other, Action::Read),
        on_x(Who::Me, Action::Release),
        on_x(Who::Me, Action::Edit),
        on_x(Who::Other, Action::Edit),
        on_x(Who::Other, Action::Remove),
        on_x(Who::Me, Action::Read),
        on_x(Who::Me, Action::Remove),
        on_x(Who::Other, Action::Edit),
    ];

    for candidate in candidates {
        let expected = lock_decision(&history, &candidate).unwrap();
        let actual = policy.decide(&history, &candidate).unwrap();
        assert_eq!(actual, expected);
        if actual == PolicyDecision::Grant {
            history.push(candidate).unwrap();
        }
    }
}

/// Asserts the literal `src/x` outcomes for self after self's edit and other's read: self owns
/// it, so release grants, but other's read claim blocks the edit. Runs twice so the second pass
/// decides on warm progress cursors.
fn assert_x_owner_and_reader(policy: &mut LockPolicy<Who, Path>, history: &History<Lock>) {
    for _ in 0..2 {
        assert_eq!(
            policy
                .decide(history, &on_x(Who::Me, Action::Release))
                .unwrap(),
            PolicyDecision::Grant,
            "{history:?}",
        );
        assert_eq!(
            policy
                .decide(history, &on_x(Who::Me, Action::Edit))
                .unwrap(),
            PolicyDecision::Deny {
                failed_precondition:
                    "src/x was last read by other; self must read it before it may edit it"
                        .to_string(),
                allowed_fixes: vec!["self read src/x".to_string()],
            },
            "{history:?}",
        );
    }
}

#[test]
fn other_resource_changes_preserve_owner_and_reader() {
    let store = store();
    let mut policy = LockPolicy::new(store.clone()).unwrap();
    let mut history = History::from_events(
        store,
        [on_x(Who::Me, Action::Edit), on_x(Who::Other, Action::Read)],
    )
    .unwrap();
    assert_x_owner_and_reader(&mut policy, &history);

    for (who, action) in [
        (Who::Me, Action::Read),
        (Who::Other, Action::Read),
        (Who::Other, Action::Edit),
        (Who::Other, Action::Release),
        (Who::Other, Action::Remove),
    ] {
        let candidate = LockEvent::new(who, action, Path::Y);
        assert_eq!(
            policy.decide(&history, &candidate).unwrap(),
            PolicyDecision::Grant,
            "{candidate:?} over {history:?}",
        );
        history.push(candidate).unwrap();
        assert_x_owner_and_reader(&mut policy, &history);
    }
}

#[test]
fn retained_policy_rejects_a_foreign_store_without_mutating_history() {
    let mut policy = LockPolicy::new(store()).unwrap();
    let history = History::from_events(store(), [on_x(Who::Other, Action::Edit)]).unwrap();
    assert_eq!(
        policy.decide(&history, &on_x(Who::Me, Action::Read)),
        Err(HistoryError::WrongHistoryOwner),
    );
    assert_eq!(history.as_slice(), &[on_x(Who::Other, Action::Edit)]);
    assert_eq!(
        lock_decision(&history, &on_x(Who::Me, Action::Read)).unwrap(),
        PolicyDecision::Grant,
    );
}
