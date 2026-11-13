//! Candidate-filtered trace policies with ordered diagnostics and optional auditing.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{self, Debug, Display};

use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::History;
use history_syntax::{Arity, ComponentPattern, Event, Head};
use junco_core::{CompileError, HistoryError};

/// An event that a rule policy can retain, judge, and render in a denial.
pub trait Judged: Event + Display + Send + Sync + 'static {}
impl<E: Event + Display + Send + Sync + 'static> Judged for E {}

/// One refused event, with the violated rule's explanation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleDenial<E> {
    /// The refused event.
    pub event: E,
    /// The precondition it failed.
    pub failed_precondition: String,
    /// Ways to make it legal.
    pub allowed_fixes: Vec<String>,
}

impl<E: Display> Display for RuleDenial<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.event, self.failed_precondition)?;
        if !self.allowed_fixes.is_empty() {
            write!(formatter, "\n    fix: {}", self.allowed_fixes.join("; "))?;
        }
        Ok(())
    }
}

/// Rules returned by one policy constructor; [`RulePolicy::rule`] adds them in order.
#[derive(Debug)]
pub struct RuleSet<E: Judged> {
    pub(super) rules: Vec<TraceRule<E>>,
}

impl<E: Judged> RuleSet<E> {
    /// Collects a constructor's ordered trace rules.
    pub const fn new(rules: Vec<TraceRule<E>>) -> Self {
        Self { rules }
    }
}

/// Rules over one event type, and how their verdicts are applied to an owned history.
///
/// Unverified glue (D1): this type is outside the Verus proofs. On top of the verified
/// `TracePolicy`/`History` it adds, exactly: (1) a `could_fire` head filter selecting the rules
/// compiled for each event; (2) one `TracePolicy` per distinct event of the batch, built from the
/// selected rules; (3) decide-then-append: a granted event is pushed to the history after its
/// decision; (4) audit mode, which also appends denied events and reports them without enforcing;
/// (5) error-to-deny: a compile or history error becomes a `Deny` decision (and a reported
/// denial, even in audit mode when the append itself failed). The verified `check_step` contract
/// covers each `TracePolicy::decide` call, not this composition.
pub struct RulePolicy<E: Judged> {
    rules: Vec<TraceRule<E>>,
    audit: bool,
}

impl<E: Judged> Default for RulePolicy<E> {
    fn default() -> Self {
        Self {
            rules: Vec::new(),
            audit: false,
        }
    }
}

impl<E: Judged> Debug for RulePolicy<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RulePolicy")
            .field("rules", &self.rules)
            .field("audit", &self.audit)
            .finish()
    }
}

impl<E: Judged> RulePolicy<E> {
    /// Creates a policy with no rules: it denies nothing.
    pub fn new() -> Self {
        Self::default()
    }

    /// Appends rules in order; the first violation supplies the diagnostic.
    #[must_use]
    pub fn rule(mut self, rules: impl Into<RuleSet<E>>) -> Self {
        self.rules.extend(rules.into().rules);
        self
    }

    /// Reports would-be denials but appends them as granted events.
    #[must_use]
    pub const fn audit(mut self) -> Self {
        self.audit = true;
        self
    }

    fn firing(&self, event: &E) -> Vec<TraceRule<E>> {
        self.rules
            .iter()
            .filter(|rule| could_fire(&rule.rule.head, event))
            .cloned()
            .collect()
    }

    /// Decides a batch in order and appends grants and audit denials.
    ///
    /// Each event sees earlier committed events, including earlier calls to `check`.
    /// Every decision is passed to `observe`; enforcing denials are not appended.
    /// A rule that does not compile denies candidates selected by its head. Malformed
    /// head arities or coordinate tags are compilation errors, never filtered-out rules.
    ///
    /// # Errors
    /// Returns denials in batch order. History failures are errors even in audit mode.
    pub fn check(
        &self,
        history: &mut History<E>,
        batch: &[E],
        mut observe: impl FnMut(&E, &PolicyDecision),
    ) -> Result<(), Vec<RuleDenial<E>>> {
        let mut judges = HashMap::new();
        let mut denials = Vec::new();
        for event in batch {
            let judge = match judges.entry(*event) {
                Entry::Occupied(judge) => judge.into_mut(),
                Entry::Vacant(slot) => {
                    let firing = self.firing(event);
                    slot.insert((!firing.is_empty()).then(|| {
                        TracePolicy::new(history.store().clone(), firing)
                            .map_err(|error| uncompiled(event, &error))
                    }))
                }
            };
            let mut decision = match judge {
                None => PolicyDecision::Grant,
                Some(Ok(judge)) => judge.decide(history, event).unwrap_or_else(history_failure),
                Some(Err(denial)) => PolicyDecision::Deny {
                    failed_precondition: denial.failed_precondition.clone(),
                    allowed_fixes: denial.allowed_fixes.clone(),
                },
            };
            let mut append_failed = false;
            if (matches!(decision, PolicyDecision::Grant) || self.audit)
                && let Err(error) = history.push(*event)
            {
                decision = history_failure(error);
                append_failed = true;
            }
            observe(event, &decision);
            if let PolicyDecision::Deny {
                failed_precondition,
                allowed_fixes,
            } = decision
                && (!self.audit || append_failed)
            {
                denials.push(RuleDenial {
                    event: *event,
                    failed_precondition,
                    allowed_fixes,
                });
            }
        }
        if denials.is_empty() {
            Ok(())
        } else {
            Err(denials)
        }
    }

    /// Decides one candidate without appending it to the history.
    ///
    /// Audit mode leaves reporting or enforcement of this returned denial to the caller.
    pub fn decide(&self, history: &History<E>, candidate: &E) -> Option<RuleDenial<E>> {
        let rules = self.firing(candidate);
        if rules.is_empty() {
            return None;
        }
        let mut judge = match TracePolicy::new(history.store().clone(), rules) {
            Ok(judge) => judge,
            Err(error) => return Some(uncompiled(candidate, &error)),
        };
        match judge
            .decide(history, candidate)
            .unwrap_or_else(history_failure)
        {
            PolicyDecision::Grant => None,
            PolicyDecision::Deny {
                failed_precondition,
                allowed_fixes,
            } => Some(RuleDenial {
                event: *candidate,
                failed_precondition,
                allowed_fixes,
            }),
        }
    }
}

fn history_failure(error: HistoryError) -> PolicyDecision {
    PolicyDecision::Deny {
        failed_precondition: format!("policy failed: {error}"),
        allowed_fixes: Vec::new(),
    }
}

fn uncompiled<E: Copy>(event: &E, error: &CompileError) -> RuleDenial<E> {
    RuleDenial {
        event: *event,
        failed_precondition: format!("policy does not compile: {error}"),
        allowed_fixes: Vec::new(),
    }
}

fn could_fire<E: Event>(head: &Head<E>, event: &E) -> bool {
    if head.slots().len() != E::Arity::value() {
        return true;
    }
    let mut matches = true;
    for (index, pattern) in head.slots().iter().enumerate() {
        if let ComponentPattern::Constant(constant) = pattern {
            // Invalid heads must reach the compiler even if another constant does not match.
            if E::coordinate(*constant) != index {
                return true;
            }
            matches &= *constant == event.component(index);
        }
    }
    matches
}
