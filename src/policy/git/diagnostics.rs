//! What a git denial says: the failed precondition and the fixes that would unblock it.

use std::fmt::Display;

use crate::{Action, Event};

/// Everything a git denial renders from: who acted, on what, who currently holds it dirty, and who
/// holds the outstanding read claim.
pub(super) struct GitContext {
    pub(super) principal: String,
    pub(super) resource: String,
    pub(super) owner: String,
    pub(super) reader: String,
}

/// Builds the context for `candidate`; called only when a rule is violated.
///
/// Principal and resource identities are rendered through the caller's `Display` labels here, off
/// the grant path.
pub(super) fn git_context<E>(history: &[E], candidate: &E) -> GitContext
where
    E: Event<Action = Action>,
    E::Principal: Display,
    E::Resource: Display,
{
    let resource = candidate.resource();
    GitContext {
        principal: candidate.principal().to_string(),
        resource: resource.to_string(),
        owner: current_owner(history, resource),
        reader: current_reader(history, resource),
    }
}

/// Extracts the current owner of `resource` for diagnostics only — grant/deny is entirely
/// trace-policy driven and never consults this value. Folds to the principal of the most-recent
/// `edit`/`unstage` (reset by `stage`/`commit`/`checkout`/`stash`), or `"another principal"`.
fn current_owner<E>(history: &[E], resource: E::Resource) -> String
where
    E: Event<Action = Action>,
    E::Principal: Display,
{
    let mut owner = None;
    for event in history.iter().filter(|event| event.resource() == resource) {
        match event.action() {
            Action::Edit | Action::Unstage => owner = Some(event.principal()),
            Action::Stage
            | Action::Delete
            | Action::Commit { .. }
            | Action::Checkout
            | Action::Stash => {
                owner = None;
            }
            Action::Read | Action::Diff | Action::History | Action::Clean => {}
        }
    }
    owner.map_or_else(
        || "another principal".to_string(),
        |owner| owner.to_string(),
    )
}

/// Extracts the principal holding the outstanding read claim on `resource`, for diagnostics only.
/// Folds to the principal of the most-recent `read`, or `"another principal"`. Its arms MUST stay
/// in lockstep with `not_read_on_r`.
fn current_reader<E>(history: &[E], resource: E::Resource) -> String
where
    E: Event<Action = Action>,
    E::Principal: Display,
{
    let mut reader = None;
    for event in history.iter().filter(|event| event.resource() == resource) {
        match event.action() {
            Action::Read => reader = Some(event.principal()),
            Action::Edit
            | Action::Stage
            | Action::Unstage
            | Action::Commit { .. }
            | Action::Checkout
            | Action::Stash
            | Action::Delete
            | Action::Diff
            | Action::History
            | Action::Clean => {}
        }
    }
    reader.map_or_else(
        || "another principal".to_string(),
        |reader| reader.to_string(),
    )
}

/// Owner-protection fixes shared by every foreign-owner contention cell.
pub(super) fn opf(p: &str, r: &str, q: &str) -> Vec<String> {
    vec![
        format!("{q} stage {r}"),
        format!("{q} checkout {r}"),
        format!("{q} stash {r}"),
        format!("{p} only reads, diffs, or histories {r}"),
    ]
}

/// Read-claim fixes shared by every outstanding-read contention cell. The claim moves only when
/// another principal reads `r`, so reading it is the only fix.
pub(super) fn rcf(p: &str, r: &str) -> Vec<String> {
    vec![format!("{p} read {r}")]
}
