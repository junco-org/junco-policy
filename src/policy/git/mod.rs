//! Git legality expressed as a native trace policy over the [`crate::policy`] kernel.
//!
//! The git authorization table is re-expressed as declarative [`crate::Rule`] values whose tails
//! are past-regexes over committed history. Each deny cell of the table is one `Forbid` rule
//! paired with a diagnostic closure carrying the exact precondition/fix strings the consumer
//! boundary surfaces. Grant/deny is entirely trace-policy driven; the commit-message identity is
//! omitted from policy checking (the candidate commit is normalized to a canonical payload-less
//! form).
//!
//! The table is assembled bottom-up: the kernel's [`crate::policy::atoms`] feed [`predicates`]
//! (one-event git tests), which feed [`languages`] (the four canonical row states built on the
//! kernel's tail shapes), which feed [`rules`] (the 23 deny cells). [`GitPolicy`] compiles that table
//! once and retains its canonical nodes and evaluator caches across decisions. [`diagnostics`]
//! renders the strings a denial carries from the caller's principal/resource `Display` labels.

mod diagnostics;
mod languages;
mod predicates;
mod rules;

use std::fmt::{Debug, Display};
use std::hash::Hash;

use self::diagnostics::git_context;
use self::rules::git_rules;
use crate::policy::decision::PolicyDecision;
use crate::policy::evaluate::CompiledPolicy;
use crate::{Action, Bump, Event, GitEvent, History, git_event};

/// Compiled Git trace policy reusable across candidate decisions.
///
/// Construction builds and compiles the static 23-rule table once. [`GitPolicy::decide`] accepts an
/// externally owned committed [`History`] so callers can preserve append-on-grant semantics while
/// this value retains canonical syntax, derivative caches, and per-history evaluated progress.
pub struct GitPolicy<'arena, P, R>
where
    P: Copy + Debug + Eq + Hash + 'arena,
    R: Copy + Debug + Eq + Hash + 'arena,
{
    compiled: CompiledPolicy<'arena, GitEvent<P, R>, diagnostics::GitContext>,
}

impl<'arena, P, R> GitPolicy<'arena, P, R>
where
    P: Copy + Debug + Eq + Hash + Display + 'arena,
    R: Copy + Debug + Eq + Hash + Display + 'arena,
{
    /// Builds and compiles the static Git policy in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            compiled: CompiledPolicy::new(arena, git_rules())
                .expect("static Git policy rules compile"),
        }
    }

    /// Decides one candidate against `history`, reusing the compiled table and evaluator caches.
    ///
    /// Commit-message identities are ignored by the policy: commit candidates are matched through
    /// the canonical payload-less action, while diagnostics still receive the original candidate.
    pub fn decide(
        &mut self,
        history: &History<GitEvent<P, R>>,
        candidate: &GitEvent<P, R>,
    ) -> PolicyDecision {
        let probe = match candidate.action() {
            Action::Commit { .. } => git_event(
                candidate.principal(),
                Action::commit_without_message(),
                candidate.resource(),
            ),
            _ => *candidate,
        };
        self.compiled.decide(history, &probe, || {
            git_context(history.as_slice(), candidate)
        })
    }
}

/// Decides one candidate with a one-shot Git policy.
///
/// Prefer retaining [`GitPolicy`] for repeated decisions. This compatibility function constructs
/// and compiles the policy for this call only.
pub fn git_decision<P, R>(
    history: &History<GitEvent<P, R>>,
    candidate: &GitEvent<P, R>,
) -> PolicyDecision
where
    P: Copy + Debug + Eq + Hash + Display,
    R: Copy + Debug + Eq + Hash + Display,
{
    let arena = Bump::new();
    GitPolicy::new(&arena).decide(history, candidate)
}

#[cfg(test)]
mod tests;
