//! Git legality expressed as a native trace policy over the [`crate::policy`] kernel.
//!
//! The git authorization table is re-expressed as declarative [`crate::Rule`] values whose tails
//! are past-regexes over committed history. Each deny cell of the table is one `Forbid` rule
//! paired with a diagnostic closure carrying the exact precondition/fix strings the consumer
//! boundary surfaces. Grant/deny is entirely trace-policy driven; the commit-message payload is
//! omitted from policy checking (the candidate commit is normalized to a canonical payload-less
//! form).
//!
//! The table is assembled bottom-up: the kernel's [`crate::policy::atoms`] feed [`predicates`]
//! (one-event git tests), which feed [`languages`] (the four canonical row states built on the
//! kernel's tail shapes), which feed [`rules`] (the 23 deny cells), which the kernel's
//! [`crate::policy::evaluate::decide`] walks. [`diagnostics`] renders the strings a denial carries.

mod diagnostics;
mod languages;
mod predicates;
mod rules;

use self::diagnostics::git_context;
use self::rules::git_rules;
use crate::policy::decision::PolicyDecision;
use crate::policy::evaluate::decide;
use crate::{Action, Event};

/// Decides one candidate against the resource's committed history via the trace-policy table.
///
/// The commit message is omitted from policy checking: any commit candidate is normalized to the
/// canonical payload-less form so the `Constant(commit_without_message)` head fires on every
/// commit. History is passed unnormalized — row-languages classify commits by the message-agnostic
/// `commit_checkout_stash_on_r` enumeration, so history commit messages never affect the outcome.
pub fn git_decision(history: &[Event], candidate: &Event) -> PolicyDecision {
    let mut probe = candidate.clone();
    if let Action::Commit { .. } = probe.action {
        probe.action = Action::commit_without_message();
    }
    decide(&git_rules(), history, &probe, || {
        git_context(history, candidate)
    })
}

#[cfg(test)]
mod tests;
