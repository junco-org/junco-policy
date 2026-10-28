//! A caller-assembled trace policy: the kernel's compile-once table over any rule set.
//!
//! [`crate::Validator`] owns its history and appends on grant, so it cannot judge a candidate
//! against a history someone else owns. [`TracePolicy`] is the same table walk the lock policy uses,
//! opened to arbitrary [`Rule`] values: history stays with the caller, the first violated rule wins,
//! and its diagnostic renders the denial from the candidate event.

use std::sync::Arc;

use super::decision::PolicyDecision;
use super::evaluate::CompiledPolicy;
use super::rule::PolicyRule;
use crate::{Bump, CompileError, Event, History, Rule};

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the candidate event.
pub type TraceDiagnostic<E> = Arc<dyn Fn(&E) -> (String, Vec<String>) + Send + Sync>;

/// One caller-supplied rule paired with the diagnostic its violation surfaces.
pub struct TraceRule<E: Event> {
    /// The past-regex rule.
    pub rule: Rule<E>,
    /// Renders the denial when `rule` is violated.
    pub diagnostic: TraceDiagnostic<E>,
}

impl<E: Event> TraceRule<E> {
    /// Pairs `rule` with `diagnostic`.
    pub fn new(
        rule: Rule<E>,
        diagnostic: impl Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static,
    ) -> Self {
        Self {
            rule,
            diagnostic: Arc::new(diagnostic),
        }
    }
}

impl<E: Event> Clone for TraceRule<E> {
    fn clone(&self) -> Self {
        Self {
            rule: self.rule.clone(),
            diagnostic: Arc::clone(&self.diagnostic),
        }
    }
}

impl<E: Event> std::fmt::Debug for TraceRule<E> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("TraceRule")
            .field("rule", &self.rule)
            .finish_non_exhaustive()
    }
}

/// A caller-assembled rule table compiled once into `arena`, decided against external histories.
pub struct TracePolicy<'arena, E: Event + 'arena> {
    compiled: CompiledPolicy<'arena, E, E>,
}

impl<'arena, E: Event + 'static> TracePolicy<'arena, E> {
    /// Compiles every rule in order.
    ///
    /// # Errors
    /// When a rule does not compile.
    pub fn new(
        arena: &'arena Bump,
        rules: impl IntoIterator<Item = TraceRule<E>>,
    ) -> Result<Self, CompileError> {
        let rules = rules
            .into_iter()
            .map(|TraceRule { rule, diagnostic }| PolicyRule {
                rule,
                diagnostic: Box::new(move |event: &E| diagnostic(event)),
            })
            .collect();
        Ok(Self {
            compiled: CompiledPolicy::new(arena, rules)?,
        })
    }

    /// Decides `candidate` against `history` without appending it. Rules apply in source order and
    /// the first violation's diagnostic is returned. Evaluator progress over `history` is retained,
    /// so deciding again after appending to it folds only the new events.
    pub fn decide(&mut self, history: &History<E>, candidate: &E) -> PolicyDecision {
        self.compiled.decide(history, candidate, || *candidate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Action, AtomPattern, Comparison, ComponentPattern, Head, LockEvent, RegexExpr, RuleMode,
        TestExpr,
    };

    type Event = LockEvent<&'static str, &'static str>;

    /// Editing anything after the same principal read `secret` is forbidden.
    fn taint() -> TraceRule<Event> {
        let read_secret = TestExpr::and([
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("p")),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(Action::Read)),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Resource(ComponentPattern::constant("secret")),
            ),
        ]);
        TraceRule::new(
            Rule::new(
                RuleMode::Forbid,
                Head::new(
                    ComponentPattern::variable("p"),
                    ComponentPattern::constant(Action::Edit),
                    ComponentPattern::variable("r"),
                ),
                RegexExpr::concat([
                    RegexExpr::all(),
                    RegexExpr::test(read_secret),
                    RegexExpr::all(),
                ]),
            ),
            |event: &Event| (format!("{} read a secret", event.principal), Vec::new()),
        )
    }

    #[test]
    fn decides_against_external_history_without_appending() {
        let arena = Bump::new();
        let mut policy = TracePolicy::new(&arena, [taint()]).unwrap();
        let edit = LockEvent::new("a", Action::Edit, "out");
        assert_eq!(policy.decide(&History::new(), &edit), PolicyDecision::Grant);
        let other = History::from_events([LockEvent::new("b", Action::Read, "secret")]);
        assert_eq!(policy.decide(&other, &edit), PolicyDecision::Grant);
        let mut history = History::from_events([LockEvent::new("a", Action::Read, "secret")]);
        history.push(LockEvent::new("a", Action::Read, "other"));
        assert_eq!(
            policy.decide(&history, &edit),
            PolicyDecision::Deny {
                failed_precondition: "a read a secret".into(),
                allowed_fixes: Vec::new(),
            }
        );
        assert_eq!(history.len(), 2);
    }
}
