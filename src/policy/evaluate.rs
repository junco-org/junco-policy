//! The decision loop: match each table rule's head, then test its tail against history.
//!
//! This runs its own `match_candidate` + `accepts` loop (mirroring `validator.rs::check`) rather
//! than building a [`crate::Validator`], because `Validator::check` returns a single opaque denial
//! message that cannot carry a policy's per-cell diagnostic, and its arena invariance forbids a
//! persistent compiled form across napi calls.

use super::decision::PolicyDecision;
use super::rule::PolicyRule;
use crate::syntax::{CanonicalStore, accepts, compile_rule};
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
        let rt = compile_rule(&mut store, &rule.rule).expect("static policy rules compile");
        let Some(subst) = rt.head.match_candidate(&mut store, probe) else {
            continue;
        };
        let inside = accepts(&mut store, rt.tail, history.iter(), &subst);
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
