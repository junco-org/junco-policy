//! A caller-assembled trace policy: the kernel's compile-once table over any rule set.
//!
//! [`crate::Validator`] owns its history and appends on grant, so it cannot judge a candidate
//! against a history someone else owns. [`TracePolicy`] is the same table walk the git policy uses,
//! opened to arbitrary [`Rule`] values: history stays with the caller, the first violated rule wins,
//! and its diagnostic renders the denial from the candidate event.

use std::sync::Arc;

use super::decision::PolicyDecision;
use super::evaluate::CompiledPolicy;
use super::rule::PolicyRule;
use crate::{Bump, CompileError, Event, Rule};

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the candidate event.
pub type TraceDiagnostic = Arc<dyn Fn(&Event) -> (String, Vec<String>) + Send + Sync>;

/// One caller-supplied rule paired with the diagnostic its violation surfaces.
#[derive(Clone)]
pub struct TraceRule {
    /// The past-regex rule.
    pub rule: Rule,
    /// Renders the denial when `rule` is violated.
    pub diagnostic: TraceDiagnostic,
}

impl TraceRule {
    /// Pairs `rule` with `diagnostic`.
    pub fn new(
        rule: Rule,
        diagnostic: impl Fn(&Event) -> (String, Vec<String>) + Send + Sync + 'static,
    ) -> Self {
        Self {
            rule,
            diagnostic: Arc::new(diagnostic),
        }
    }
}

/// A caller-assembled rule table compiled once into `arena`, decided against external histories.
pub struct TracePolicy<'arena> {
    compiled: CompiledPolicy<'arena, Event>,
}

impl<'arena> TracePolicy<'arena> {
    /// Compiles every rule in order.
    pub fn new(
        arena: &'arena Bump,
        rules: impl IntoIterator<Item = TraceRule>,
    ) -> Result<Self, CompileError> {
        let rules = rules
            .into_iter()
            .map(|TraceRule { rule, diagnostic }| PolicyRule {
                rule,
                diagnostic: Box::new(move |event: &Event| diagnostic(event)),
            })
            .collect();
        Ok(Self {
            compiled: CompiledPolicy::new(arena, rules)?,
        })
    }

    /// Decides `candidate` against `history` without appending it. Rules apply in source order and
    /// the first violation's diagnostic is returned.
    pub fn decide(&mut self, history: &[Event], candidate: &Event) -> PolicyDecision {
        self.compiled
            .decide(history, candidate, || candidate.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Action, AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, RuleMode, TestExpr,
    };

    /// Editing anything after the same principal read `secret` is forbidden.
    fn taint() -> TraceRule {
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
                AtomPattern::Resource(ComponentPattern::constant(["secret"])),
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
            |event| (format!("{} read a secret", event.principal), Vec::new()),
        )
    }

    #[test]
    fn decides_against_external_history_without_appending() {
        let arena = Bump::new();
        let mut policy = TracePolicy::new(&arena, [taint()]).unwrap();
        let edit = Event::new("a", Action::Edit, ["out"]);
        assert_eq!(policy.decide(&[], &edit), PolicyDecision::Grant);
        let history = [Event::new("b", Action::Read, ["secret"])];
        assert_eq!(policy.decide(&history, &edit), PolicyDecision::Grant);
        let history = [
            Event::new("a", Action::Read, ["secret"]),
            Event::new("a", Action::Read, ["other"]),
        ];
        assert_eq!(
            policy.decide(&history, &edit),
            PolicyDecision::Deny {
                failed_precondition: "a read a secret".into(),
                allowed_fixes: Vec::new(),
            }
        );
    }
}
