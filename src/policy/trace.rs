//! A caller-assembled trace policy: the kernel's compile-once table over any rule set.
//!
//! [`crate::Validator`] owns its history and appends on grant, so it cannot judge a candidate
//! against a history someone else owns. [`TracePolicy`] is the same table walk the git policy uses,
//! opened to arbitrary [`Rule`] values: history stays with the caller, the first violated rule wins,
//! and its diagnostic renders the denial from the candidate event.
//!
//! [`TraceCursor`] is the incremental form for one fixed candidate: each rule keeps its derivative
//! state, so appending one history event costs at most one derivative step per active rule.

use std::sync::Arc;

use super::decision::PolicyDecision;
use super::evaluate::CompiledPolicy;
use super::rule::PolicyRule;
use crate::syntax::{CandidateSubstitution, RegexId};
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

/// Incremental decision state for one fixed candidate.
///
/// Meaningful only with the [`TracePolicy`] that built it: equality compares canonical derivative
/// handles, which are unique within that policy's store. Clones share the candidate and its head
/// bindings, copying only one handle per rule.
#[derive(Clone, PartialEq, Eq)]
pub struct TraceCursor<'arena> {
    candidate: Arc<CursorCandidate<'arena>>,
    /// Per-rule derivative state over the consumed history; `None` marks a rule whose head does not
    /// match the candidate.
    states: Vec<Option<RegexId<'arena>>>,
}

/// The fixed part of a cursor: the candidate and each rule's head bindings for it.
#[derive(PartialEq, Eq)]
struct CursorCandidate<'arena> {
    event: Event,
    substitutions: Vec<Option<CandidateSubstitution<'arena>>>,
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

    /// Starts deciding `candidate` against an empty history.
    pub fn cursor(&mut self, candidate: &Event) -> TraceCursor<'arena> {
        let (states, substitutions) = self
            .compiled
            .start(candidate)
            .into_iter()
            .map(Option::unzip)
            .unzip();
        TraceCursor {
            candidate: Arc::new(CursorCandidate {
                event: candidate.clone(),
                substitutions,
            }),
            states,
        }
    }

    /// Consumes one more history event: at most one derivative step per rule whose head matches.
    /// Rules already saturated at the universal or empty language take no step.
    pub fn advance(&mut self, cursor: &mut TraceCursor<'arena>, event: &Event) {
        self.compiled
            .advance(&cursor.candidate.substitutions, &mut cursor.states, event);
    }

    /// Exactly [`TracePolicy::decide`] of the history consumed so far against the cursor's
    /// candidate.
    pub fn verdict(&self, cursor: &TraceCursor<'arena>) -> PolicyDecision {
        self.compiled
            .verdict(&cursor.states, || cursor.candidate.event.clone())
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

    /// Staging needs the stager's own edit of the resource with no other principal acting since.
    fn fresh_edit() -> TraceRule {
        let own_edit = TestExpr::and([
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("p")),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Resource(ComponentPattern::variable("r")),
            ),
        ]);
        let someone_else = TestExpr::atom(
            Comparison::Neq,
            AtomPattern::Principal(ComponentPattern::variable("p")),
        );
        TraceRule::new(
            Rule::new(
                RuleMode::Require,
                Head::new(
                    ComponentPattern::variable("p"),
                    ComponentPattern::constant(Action::Stage),
                    ComponentPattern::variable("r"),
                ),
                RegexExpr::concat([
                    RegexExpr::all(),
                    RegexExpr::test(own_edit),
                    RegexExpr::star(RegexExpr::test(someone_else)),
                ]),
            ),
            |event| (format!("{} must edit first", event.principal), Vec::new()),
        )
    }

    /// A head no generated candidate matches.
    fn inert() -> TraceRule {
        TraceRule::new(
            Rule::new(
                RuleMode::Require,
                Head::new(
                    ComponentPattern::constant("nobody"),
                    ComponentPattern::variable("a"),
                    ComponentPattern::variable("r"),
                ),
                RegexExpr::empty(),
            ),
            |_| ("inert rule fired".into(), Vec::new()),
        )
    }

    /// Nothing may be the first event: denies every candidate, but only against an empty history.
    fn first() -> TraceRule {
        TraceRule::new(
            Rule::new(
                RuleMode::Forbid,
                Head::new(
                    ComponentPattern::variable("p"),
                    ComponentPattern::variable("a"),
                    ComponentPattern::variable("r"),
                ),
                RegexExpr::epsilon(),
            ),
            |_| ("first event".into(), Vec::new()),
        )
    }

    /// Deterministic xorshift64 so the differential test needs no extra dependency.
    struct XorShift(u64);

    impl XorShift {
        fn below(&mut self, bound: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % bound as u64) as usize
        }

        fn event(&mut self) -> Event {
            let principal = ["a", "b"][self.below(2)];
            let action = [Action::Read, Action::Edit, Action::Stage][self.below(3)].clone();
            let resource = ["secret", "out"][self.below(2)];
            Event::new(principal, action, [resource])
        }
    }

    #[test]
    fn cursor_verdict_matches_decide_on_every_prefix() {
        let arena = Bump::new();
        let mut policy =
            TracePolicy::new(&arena, [taint(), fresh_edit(), inert(), first()]).unwrap();
        let mut rng = XorShift(0x9E37_79B9_7F4A_7C15);
        let mut denials = std::collections::HashSet::new();
        for _ in 0..300 {
            let candidate = rng.event();
            let mut cursor = policy.cursor(&candidate);
            let mut history = Vec::new();
            loop {
                let verdict = policy.verdict(&cursor);
                assert_eq!(verdict, policy.decide(&history, &candidate), "{history:?}");
                if let PolicyDecision::Deny {
                    failed_precondition,
                    ..
                } = verdict
                {
                    denials.insert(failed_precondition);
                }
                if history.len() == 12 {
                    break;
                }
                let event = rng.event();
                policy.advance(&mut cursor, &event);
                history.push(event);
            }
        }
        for expected in [
            "a read a secret",
            "b read a secret",
            "a must edit first",
            "b must edit first",
            "first event",
        ] {
            assert!(denials.contains(expected), "never saw {expected:?}");
        }
        assert!(!denials.contains("inert rule fired"));
    }

    #[test]
    fn cursor_clones_advance_independently_and_compare_by_state() {
        let arena = Bump::new();
        let mut policy =
            TracePolicy::new(&arena, [taint(), fresh_edit(), inert(), first()]).unwrap();
        let edit = Event::new("a", Action::Edit, ["out"]);
        let read_secret = Event::new("a", Action::Read, ["secret"]);
        let unrelated = Event::new("b", Action::Read, ["out"]);

        let mut cursor = policy.cursor(&edit);
        let mut twin = policy.cursor(&edit);
        assert!(cursor == twin);
        policy.advance(&mut cursor, &unrelated);
        assert!(cursor != twin);
        policy.advance(&mut twin, &unrelated);
        assert!(cursor == twin);

        let mut tainted = cursor.clone();
        assert!(tainted == cursor);
        policy.advance(&mut tainted, &read_secret);
        policy.advance(&mut cursor, &unrelated);
        assert!(tainted != cursor);
        assert_eq!(
            policy.verdict(&tainted),
            PolicyDecision::Deny {
                failed_precondition: "a read a secret".into(),
                allowed_fixes: Vec::new(),
            }
        );
        assert_eq!(policy.verdict(&cursor), PolicyDecision::Grant);
        assert_eq!(policy.verdict(&twin), PolicyDecision::Grant);

        let other_edit = Event::new("b", Action::Edit, ["out"]);
        assert!(policy.cursor(&edit) != policy.cursor(&other_edit));
    }
}
