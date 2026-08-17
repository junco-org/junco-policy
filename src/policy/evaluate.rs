//! The decision loop: match each table rule's head, then test its tail against history.
//!
//! This runs its own compiled-rule loop rather than building a [`crate::Validator`], because
//! `Validator::check` returns a single opaque denial message that cannot carry a policy's per-cell
//! diagnostic, and its arena invariance forbids a persistent compiled form across napi calls.

use super::decision::PolicyDecision;
use super::rule::PolicyRule;
use crate::syntax::{CanonicalStore, compile_rule};
use crate::{Bump, Event, RuleMode};

/// Walks `rules` in order and returns the first violated rule's rendered denial.
///
/// `probe` is the candidate form heads match against; a policy normalizes it before calling.
/// `context` is invoked at most once, only when a rule is violated, so the grant path allocates
/// nothing beyond rule compilation.
pub(super) fn decide<C>(
    rules: &[PolicyRule<C>],
    history: &[Event],
    probe: &Event,
    context: impl Fn() -> C,
) -> PolicyDecision {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);

    for rule in rules {
        let mut rt = compile_rule(&mut store, &rule.rule).expect("static policy rules compile");
        let Some(inside) = rt.accepts_history(&mut store, history.iter(), probe) else {
            continue;
        };
        let violated = match rt.mode {
            RuleMode::Forbid => inside,
            RuleMode::Require => !inside,
        };
        if violated {
            let (failed_precondition, allowed_fixes) = (rule.diagnostic)(&context());
            return PolicyDecision::Deny {
                failed_precondition,
                allowed_fixes,
            };
        }
    }
    PolicyDecision::Grant
}
