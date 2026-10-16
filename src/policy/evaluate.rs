//! Compilation and evaluation for declarative trace-policy tables.
//!
//! [`CompiledPolicy`] resolves source rules once into one canonical store, then retains both the
//! runtime rules and their derivative caches across decisions. Diagnostics remain paired with their
//! compiled rules so a policy can preserve domain-specific denial details without using the opaque
//! denial produced by [`crate::Validator`].

use super::decision::PolicyDecision;
use super::rule::{Diagnostic, PolicyRule};
use crate::syntax::{CandidateSubstitution, CanonicalStore, RegexId, RuntimeRule, compile_rule};
use crate::{Bump, CompileError, Event, RuleMode};

/// One compiled runtime rule paired with the diagnostic rendered when it is violated.
struct CompiledPolicyRule<'arena, C> {
    runtime: RuntimeRule<'arena>,
    diagnostic: Diagnostic<C>,
}

/// A policy table compiled once into an arena-backed canonical store.
///
/// The store and runtime rules are retained together because runtime handles borrow nodes allocated
/// in `arena`. Calls to [`CompiledPolicy::decide`] mutate only evaluator caches; source rules are not
/// reconstructed or recompiled.
pub(super) struct CompiledPolicy<'arena, C> {
    store: CanonicalStore<'arena>,
    rules: Vec<CompiledPolicyRule<'arena, C>>,
}

impl<'arena, C> CompiledPolicy<'arena, C> {
    /// Compiles every source rule in order and preserves its paired diagnostic.
    pub(super) fn new(
        arena: &'arena Bump,
        rules: Vec<PolicyRule<C>>,
    ) -> Result<Self, CompileError> {
        let mut store = CanonicalStore::new(arena);
        let mut compiled = Vec::with_capacity(rules.len());
        for PolicyRule { rule, diagnostic } in rules {
            let runtime = compile_rule(&mut store, &rule)?;
            compiled.push(CompiledPolicyRule {
                runtime,
                diagnostic,
            });
        }
        Ok(Self {
            store,
            rules: compiled,
        })
    }

    /// Walks compiled rules in source order and returns the first violation's rendered denial.
    ///
    /// `probe` is the candidate form heads match against; a policy may normalize it before calling.
    /// `context` is invoked at most once, only when a rule is violated. Runtime derivative caches and
    /// canonical nodes survive this call and are reused by later decisions.
    pub(super) fn decide(
        &mut self,
        history: &[Event],
        probe: &Event,
        context: impl FnOnce() -> C,
    ) -> PolicyDecision {
        let store = &mut self.store;
        first_violation(
            self.rules.iter_mut().map(|rule| {
                let inside = rule.runtime.accepts_history(store, history.iter(), probe);
                (&*rule, inside)
            }),
            context,
        )
    }

    /// Matches every rule head against `probe` once; `None` marks a rule that stays inert.
    pub(super) fn start(
        &mut self,
        probe: &Event,
    ) -> Vec<Option<(RegexId<'arena>, CandidateSubstitution<'arena>)>> {
        self.rules
            .iter()
            .map(|rule| rule.runtime.start(&mut self.store, probe))
            .collect()
    }

    /// Advances every active rule's state by one history event, one derivative step each.
    pub(super) fn advance(
        &mut self,
        substitutions: &[Option<CandidateSubstitution<'arena>>],
        states: &mut [Option<RegexId<'arena>>],
        event: &Event,
    ) {
        for ((rule, substitution), state) in self.rules.iter_mut().zip(substitutions).zip(states) {
            if let (Some(substitution), Some(state)) = (substitution, state) {
                *state = rule
                    .runtime
                    .step(&mut self.store, *state, substitution, event);
            }
        }
    }

    /// [`CompiledPolicy::decide`] for the history already consumed into `states`.
    pub(super) fn verdict(
        &self,
        states: &[Option<RegexId<'arena>>],
        context: impl FnOnce() -> C,
    ) -> PolicyDecision {
        first_violation(
            self.rules.iter().zip(states).map(|(rule, state)| {
                let inside = state.map(|state| RuntimeRule::accepts_state(&self.store, state));
                (rule, inside)
            }),
            context,
        )
    }
}

/// Returns the first violated rule's rendered denial; `None` marks a rule whose head did not match.
fn first_violation<'rule, 'arena: 'rule, C: 'rule>(
    rules: impl IntoIterator<Item = (&'rule CompiledPolicyRule<'arena, C>, Option<bool>)>,
    context: impl FnOnce() -> C,
) -> PolicyDecision {
    for (rule, inside) in rules {
        let Some(inside) = inside else {
            continue;
        };
        let violated = match rule.runtime.mode {
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

/// Compiles and evaluates one policy table once.
///
/// This convenience path exists for isolated tests. Stateful production callers should retain a
/// [`CompiledPolicy`] so they do not pay source construction and compilation on every decision.
#[cfg(test)]
pub(super) fn decide<C>(
    rules: Vec<PolicyRule<C>>,
    history: &[Event],
    probe: &Event,
    context: impl FnOnce() -> C,
) -> PolicyDecision {
    let arena = Bump::new();
    CompiledPolicy::new(&arena, rules)
        .expect("static policy rules compile")
        .decide(history, probe, context)
}
