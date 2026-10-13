//! The lock table, checked against an independent claim-state oracle.

use std::fmt;

use super::{LockPolicy, lock_decision};
use crate::policy::PolicyDecision;
use crate::{Action, Bump, History, LockEvent};

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
        [
            reader.who().map(|reader| on_x(reader, Action::Read)),
            owner.who().map(|owner| on_x(owner, Action::Edit)),
        ]
        .into_iter()
        .flatten(),
    )
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
                    verdict(lock_decision(&history, &on_x(Who::Me, action))),
                    oracle(owner, reader, action),
                    "owner={owner:?} reader={reader:?} action={action}",
                );
            }
        }
    }
}

fn grants(history: &History<Lock>, principal: Who, action: Action) -> bool {
    lock_decision(history, &on_x(principal, action)) == PolicyDecision::Grant
}

#[test]
fn release_clears_only_ownership_and_remove_clears_both_claims() {
    let read_then_edit = [
        on_x(Who::Other, Action::Read),
        on_x(Who::Other, Action::Edit),
    ];

    let mut released = History::from_events(read_then_edit);
    released.push(on_x(Who::Other, Action::Release));
    // The owner is gone, but the reader claim survives a release.
    assert!(grants(&released, Who::Me, Action::Release));
    assert!(!grants(&released, Who::Me, Action::Edit));
    assert!(!grants(&released, Who::Me, Action::Remove));

    let mut removed = History::from_events(read_then_edit);
    removed.push(on_x(Who::Other, Action::Remove));
    // Recreating a removed name needs no read of a missing file.
    assert!(grants(&removed, Who::Me, Action::Edit));
    assert!(grants(&removed, Who::Me, Action::Remove));

    // A release then a fresh edit reacquires ownership.
    released.push(on_x(Who::Other, Action::Edit));
    assert!(!grants(&released, Who::Me, Action::Release));
    // Claims on another resource never interfere.
    assert_eq!(
        lock_decision(&released, &LockEvent::new(Who::Me, Action::Edit, Path::Y)),
        PolicyDecision::Grant
    );
}

#[test]
fn retained_policy_matches_one_shot_decisions_across_history_updates() {
    let arena = Bump::new();
    let mut policy = LockPolicy::new(&arena);
    let mut history = History::new();
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
        let expected = lock_decision(&history, &candidate);
        let actual = policy.decide(&history, &candidate);
        assert_eq!(actual, expected);
        if actual == PolicyDecision::Grant {
            history.push(candidate);
        }
    }
}

/// Asserts the literal `src/x` outcomes for self after self's edit and other's read: self owns
/// it, so release grants, but other's read claim blocks the edit. Runs twice so the second pass
/// decides on warm progress cursors.
fn assert_x_owner_and_reader(policy: &mut LockPolicy<'_, Who, Path>, history: &History<Lock>) {
    for _ in 0..2 {
        assert_eq!(
            policy.decide(history, &on_x(Who::Me, Action::Release)),
            PolicyDecision::Grant,
            "{history:?}",
        );
        assert_eq!(
            policy.decide(history, &on_x(Who::Me, Action::Edit)),
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
    let arena = Bump::new();
    let mut policy = LockPolicy::new(&arena);
    let mut history =
        History::from_events([on_x(Who::Me, Action::Edit), on_x(Who::Other, Action::Read)]);
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
            policy.decide(&history, &candidate),
            PolicyDecision::Grant,
            "{candidate:?} over {history:?}",
        );
        history.push(candidate);
        assert_x_owner_and_reader(&mut policy, &history);
    }
}
