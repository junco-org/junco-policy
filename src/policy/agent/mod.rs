//! Agent policies: past-time rules over classified observations of what agents did.
//!
//! [`crate::LockPolicy`] speaks about exact resources. An agent policy speaks about *classes*: the
//! caller classifies every concrete resource it observes (see [`crate::Classifier`]) — a path read
//! or written, a program run, a peer contacted — and logs an [`AgentEvent`] over the class. Its
//! [`AgentRule`]s are past-regexes over that classified log, so a rule such as "no external peer
//! once this principal has read a secret" stays one rule however many secrets and peers there are.
//!
//! | Observation | Action | Resource |
//! | --- | --- | --- |
//! | read of a resource | [`AgentAction::Read`] | its class |
//! | creation of a resource | [`AgentAction::Create`] | its class |
//! | modification of a resource | [`AgentAction::Edit`] | its class |
//! | removal of a resource | [`AgentAction::Remove`] | its class |
//! | program run | [`AgentAction::Run`] | its class (for example its basename) |
//! | peer contacted | [`AgentAction::Contact`] | the peer's class |
//! | operator approval | [`AgentAction::Approve`] | the approved label |
//! | data of a propagated class received from another principal | [`AgentAction::Receive`] | the class |
//! | operator declassification of what the principal holds | [`AgentAction::Declassify`] | the class |
//!
//! [`AgentPolicy::check`] decides a batch of candidates atomically against a log the caller owns;
//! [`AgentPolicy::decide`] decides one candidate as it happens. Both compile only the rules whose
//! head can match a candidate.
//!
//! Rules follow the principal that read a class. A principal can hand the data to another one, so
//! a rule set may name classes that *propagate* ([`AgentRuleSet::propagating`]): a
//! [`crate::TaintState`] tracks which principals hold them and which carriers they wrote them to,
//! and a principal that receives one is logged with [`AgentAction::Receive`], which
//! [`AgentRule::no_contact_after_read`] treats like reading the class itself.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use super::atoms::{PRINCIPAL_VAR, RESOURCE_VAR, action_is, principal_is};
use super::decision::PolicyDecision;
use super::language::last_state_change;
use super::trace::{TracePolicy, TraceRule};
use crate::{
    AtomPattern, Bump, Comparison, CompileError, ComponentPattern, Event, Head, History, RegexExpr,
    Rule, RuleMode, TestExpr,
};

/// A principal or class identity agent rules can name and render: compact, comparable, and
/// shareable with the diagnostics that print it.
pub trait Label: Copy + Debug + Eq + Hash + Display + Send + Sync + 'static {}
impl<T: Copy + Debug + Eq + Hash + Display + Send + Sync + 'static> Label for T {}

/// What an observation did to the resource of its class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AgentAction {
    /// Read an existing resource.
    Read,
    /// Created a resource.
    Create,
    /// Modified an existing resource.
    Edit,
    /// Removed a resource.
    Remove,
    /// Ran a program.
    Run,
    /// Contacted a peer.
    Contact,
    /// An operator approved a label.
    Approve,
    /// Received data of a propagated class from another principal.
    Receive,
    /// An operator declassified a class the principal holds.
    Declassify,
}

impl Display for AgentAction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Read => "read",
            Self::Create => "create",
            Self::Edit => "edit",
            Self::Remove => "remove",
            Self::Run => "run",
            Self::Contact => "contact",
            Self::Approve => "approve",
            Self::Receive => "receive",
            Self::Declassify => "declassify",
        })
    }
}

/// One classified observation: `principal` did `action` to a resource of class `resource`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AgentEvent<P, C> {
    /// The acting principal.
    pub principal: P,
    /// What it did.
    pub action: AgentAction,
    /// The class of the resource it did it to.
    pub resource: C,
}

impl<P, C> AgentEvent<P, C> {
    /// Creates a classified observation.
    pub const fn new(principal: P, action: AgentAction, resource: C) -> Self {
        Self {
            principal,
            action,
            resource,
        }
    }
}

impl<P, C> Event for AgentEvent<P, C>
where
    P: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash,
{
    type Principal = P;
    type Action = AgentAction;
    type Resource = C;

    fn principal(self) -> P {
        self.principal
    }

    fn action(self) -> AgentAction {
        self.action
    }

    fn resource(self) -> C {
        self.resource
    }
}

impl<P: Display, C: Display> Display for AgentEvent<P, C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} {} {}",
            self.principal, self.action, self.resource
        )
    }
}

/// One refused candidate, with the violated rule's explanation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentDenial<P, C> {
    /// The refused candidate.
    pub event: AgentEvent<P, C>,
    /// The precondition it failed.
    pub failed_precondition: String,
    /// Ways to make it legal.
    pub allowed_fixes: Vec<String>,
}

impl<P: Display, C: Display> Display for AgentDenial<P, C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.event, self.failed_precondition)?;
        if !self.allowed_fixes.is_empty() {
            write!(formatter, "\n    fix: {}", self.allowed_fixes.join("; "))?;
        }
        Ok(())
    }
}

/// Rules over classified observations, and how their verdicts are applied.
pub struct AgentPolicy<P: Label, C: Label> {
    rules: Vec<AgentRule<P, C>>,
    /// Classes whose data taints whoever receives it from a principal holding it.
    propagated: Vec<C>,
    audit: bool,
}

impl<P: Label, C: Label> Default for AgentPolicy<P, C> {
    fn default() -> Self {
        Self {
            rules: Vec::new(),
            propagated: Vec::new(),
            audit: false,
        }
    }
}

impl<P: Label, C: Label> Clone for AgentPolicy<P, C> {
    fn clone(&self) -> Self {
        Self {
            rules: self.rules.clone(),
            propagated: self.propagated.clone(),
            audit: self.audit,
        }
    }
}

impl<P: Label, C: Label> Debug for AgentPolicy<P, C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentPolicy")
            .field("rules", &self.rules)
            .field("propagated", &self.propagated)
            .field("audit", &self.audit)
            .finish()
    }
}

impl<P: Label, C: Label> AgentPolicy<P, C> {
    /// A policy with no rules: it denies nothing.
    pub fn new() -> Self {
        Self::default()
    }

    /// Appends a rule or a constructor's rule set, and the classes the set propagates. Rules
    /// apply in order and the first violation is reported.
    #[must_use]
    pub fn rule(mut self, rules: impl Into<AgentRuleSet<P, C>>) -> Self {
        let AgentRuleSet { rules, propagated } = rules.into();
        for class in propagated {
            if !self.propagated.contains(&class) {
                self.propagated.push(class);
            }
        }
        self.rules.extend(rules);
        self
    }

    /// Reports every decision but never denies: a would-be denial is recorded as granted. For
    /// measuring a policy's false denials on unmodified runs.
    #[must_use]
    pub const fn audit(mut self) -> Self {
        self.audit = true;
        self
    }

    /// Whether this policy reports denials without enforcing them.
    pub const fn audits(&self) -> bool {
        self.audit
    }

    /// Every rule, in order.
    pub fn rules(&self) -> impl Iterator<Item = &AgentRule<P, C>> {
        self.rules.iter()
    }

    /// Whether a principal that receives data of `class` from another one holds it too.
    pub fn propagates(&self, class: C) -> bool {
        self.propagated.contains(&class)
    }

    /// The classes that propagate, in the order their rules were added.
    pub fn propagated(&self) -> impl Iterator<Item = C> + '_ {
        self.propagated.iter().copied()
    }

    /// Whether any rule's head can match `event`; when none can, every decision grants it.
    pub fn judges(&self, event: &AgentEvent<P, C>) -> bool {
        self.rules
            .iter()
            .any(|rule| could_fire(&rule.0.rule.head, event))
    }

    /// The rules whose head can match `event`; no other rule can judge it.
    fn firing(&self, event: &AgentEvent<P, C>) -> Vec<TraceRule<AgentEvent<P, C>>> {
        self.rules
            .iter()
            .filter(|rule| could_fire(&rule.0.rule.head, event))
            .map(|rule| rule.0.clone())
            .collect()
    }

    /// Decides `batch` in order against `history` as one atomic decision: each candidate is
    /// judged against the history plus the candidates granted before it. Every decision is passed
    /// to `observe`; on any denial, every denial is returned, unless this policy only audits.
    ///
    /// A rule that does not compile denies every candidate it could judge.
    ///
    /// # Errors
    /// The denials, in batch order, when any candidate is refused and the policy enforces.
    pub fn check(
        &self,
        history: impl IntoIterator<Item = AgentEvent<P, C>>,
        batch: &[AgentEvent<P, C>],
        mut observe: impl FnMut(&AgentEvent<P, C>, &PolicyDecision),
    ) -> Result<(), Vec<AgentDenial<P, C>>> {
        if self.rules.is_empty() {
            return Ok(());
        }
        let arena = Bump::new();
        // Each distinct candidate compiles only the rules that can judge it, once per batch.
        let mut judges = HashMap::new();
        let mut history = History::from_events(history);
        let mut denials = Vec::new();
        for event in batch {
            let judge = match judges.entry(*event) {
                Entry::Occupied(judge) => judge.into_mut(),
                Entry::Vacant(slot) => slot.insert(
                    TracePolicy::new(&arena, self.firing(event))
                        .map_err(|error| uncompiled(event, &error)),
                ),
            };
            let decision = match judge {
                Ok(judge) => judge.decide(&history, event),
                Err(denial) => PolicyDecision::Deny {
                    failed_precondition: denial.failed_precondition.clone(),
                    allowed_fixes: denial.allowed_fixes.clone(),
                },
            };
            observe(event, &decision);
            match decision {
                PolicyDecision::Grant => history.push(*event),
                PolicyDecision::Deny { .. } if self.audit => history.push(*event),
                PolicyDecision::Deny {
                    failed_precondition,
                    allowed_fixes,
                } => denials.push(AgentDenial {
                    event: *event,
                    failed_precondition,
                    allowed_fixes,
                }),
            }
        }
        if denials.is_empty() {
            Ok(())
        } else {
            Err(denials)
        }
    }

    /// Decides `candidate` alone against `history`, for example while the observation that
    /// produced it is still in progress. Returns the denial, if any; an auditing policy's denial
    /// is the caller's to report, not to enforce.
    pub fn decide(
        &self,
        history: impl IntoIterator<Item = AgentEvent<P, C>>,
        candidate: &AgentEvent<P, C>,
    ) -> Option<AgentDenial<P, C>> {
        let rules = self.firing(candidate);
        if rules.is_empty() {
            return None;
        }
        let arena = Bump::new();
        let mut judge = match TracePolicy::new(&arena, rules) {
            Ok(judge) => judge,
            Err(error) => return Some(uncompiled(candidate, &error)),
        };
        match judge.decide(&History::from_events(history), candidate) {
            PolicyDecision::Grant => None,
            PolicyDecision::Deny {
                failed_precondition,
                allowed_fixes,
            } => Some(AgentDenial {
                event: *candidate,
                failed_precondition,
                allowed_fixes,
            }),
        }
    }
}

/// The denial of `event` when a rule that could judge it does not compile.
fn uncompiled<P, C>(event: &AgentEvent<P, C>, error: &CompileError) -> AgentDenial<P, C>
where
    P: Copy,
    C: Copy,
{
    AgentDenial {
        event: *event,
        failed_precondition: format!("agent policy does not compile: {error}"),
        allowed_fixes: Vec::new(),
    }
}

/// Whether `head` can match `event`: every constant component equals the event's.
fn could_fire<P: Label, C: Label>(head: &Head<AgentEvent<P, C>>, event: &AgentEvent<P, C>) -> bool {
    fn admits<T: PartialEq>(pattern: &ComponentPattern<T>, value: &T) -> bool {
        match pattern {
            ComponentPattern::Constant(constant) => constant == value,
            ComponentPattern::Variable(_) => true,
        }
    }
    admits(&head.principal, &event.principal)
        && admits(&head.action, &event.action)
        && admits(&head.resource, &event.resource)
}

/// One rule of an [`AgentPolicy`]: a past-regex over classified observations, with the diagnostic
/// its violation renders.
pub struct AgentRule<P: Label, C: Label>(TraceRule<AgentEvent<P, C>>);

impl<P: Label, C: Label> Clone for AgentRule<P, C> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: Label, C: Label> Debug for AgentRule<P, C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("AgentRule")
            .field(&self.0.rule)
            .finish()
    }
}

type Test<P, C> = TestExpr<AgentEvent<P, C>>;
type Regex<P, C> = RegexExpr<AgentEvent<P, C>>;

/// An event whose resource is the class `class`.
fn class_is<P: Label, C: Label>(class: C, comparison: Comparison) -> Test<P, C> {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::constant(class)),
    )
}

/// The acting principal changed a resource of `class`: created, modified or removed it.
fn changed_by_p<P: Label, C: Label>(class: C) -> Test<P, C> {
    TestExpr::and([
        principal_is(Comparison::Eq),
        class_is(class, Comparison::Eq),
        TestExpr::or(
            CHANGES
                .into_iter()
                .map(|action| action_is(action, Comparison::Eq)),
        ),
    ])
}

/// Any event that is not an approval of `label`.
fn not_approval<P: Label, C: Label>(label: C) -> Test<P, C> {
    TestExpr::or([
        action_is(AgentAction::Approve, Comparison::Neq),
        class_is(label, Comparison::Neq),
    ])
}

/// Histories with no approval of `label` after their last `trigger`.
fn since_unapproved<P: Label, C: Label>(trigger: Test<P, C>, label: C) -> Regex<P, C> {
    last_state_change(trigger, not_approval(label))
}

/// Any event that is not an operator's declassification of `class` for the acting principal.
fn not_declassified<P: Label, C: Label>(class: C) -> Test<P, C> {
    TestExpr::or([
        principal_is(Comparison::Neq),
        action_is(AgentAction::Declassify, Comparison::Neq),
        class_is(class, Comparison::Neq),
    ])
}

/// Histories with no declassification of `class` for the acting principal after their last
/// `trigger`.
fn since_undeclassified<P: Label, C: Label>(trigger: Test<P, C>, class: C) -> Regex<P, C> {
    last_state_change(trigger, not_declassified(class))
}

/// Histories that contain `event` somewhere.
fn ever<P: Label, C: Label>(event: Test<P, C>) -> Regex<P, C> {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(event), RegexExpr::all()])
}

/// A `Forbid` rule over the acting principal with an action- and class-constant head.
fn forbid<P: Label, C: Label>(
    action: AgentAction,
    class: C,
    tail: Regex<P, C>,
) -> Rule<AgentEvent<P, C>> {
    Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable(PRINCIPAL_VAR),
            ComponentPattern::constant(action),
            ComponentPattern::constant(class),
        ),
        tail,
    )
}

/// The actions that change a resource.
const CHANGES: [AgentAction; 3] = [AgentAction::Create, AgentAction::Edit, AgentAction::Remove];

impl<P: Label, C: Label> AgentRule<P, C> {
    /// A caller-built rule over the classified vocabulary in the module docs.
    pub const fn custom(rule: TraceRule<AgentEvent<P, C>>) -> Self {
        Self(rule)
    }

    /// The rule and its diagnostic.
    pub const fn trace_rule(&self) -> &TraceRule<AgentEvent<P, C>> {
        &self.0
    }

    /// One rule per action in `actions`, each forbidding that action on `class` when `tail`
    /// holds, with the diagnostic `render` builds from the refused event.
    fn per_action(
        actions: impl IntoIterator<Item = AgentAction>,
        class: C,
        tail: &Regex<P, C>,
        render: impl Fn(&AgentEvent<P, C>) -> (String, Vec<String>) + Clone + Send + Sync + 'static,
    ) -> AgentRuleSet<P, C> {
        AgentRuleSet::new(
            actions
                .into_iter()
                .map(|action| {
                    Self(TraceRule::new(
                        forbid(action, class, tail.clone()),
                        render.clone(),
                    ))
                })
                .collect(),
        )
    }

    /// No peer of any of `peers` once the same principal has read a resource of `secret`, or
    /// received its data from another principal, unless an operator has since declassified
    /// `secret` for that principal. The set propagates `secret`.
    pub fn no_contact_after_read(secret: C, peers: &[C]) -> AgentRuleSet<P, C> {
        let read = TestExpr::and([
            principal_is(Comparison::Eq),
            TestExpr::or([
                action_is(AgentAction::Read, Comparison::Eq),
                action_is(AgentAction::Receive, Comparison::Eq),
            ]),
            class_is(secret, Comparison::Eq),
        ]);
        let tail = since_undeclassified(read, secret);
        AgentRuleSet::new(
            peers
                .iter()
                .map(|&peer| {
                    Self(TraceRule::new(
                        forbid(AgentAction::Contact, peer, tail.clone()),
                        move |event: &AgentEvent<P, C>| {
                            (
                                format!(
                                    "{} contacted an {peer} peer after reading {secret} data",
                                    event.principal
                                ),
                                vec![format!(
                                    "contact {peer} peers only from a principal that has not read {secret}"
                                )],
                            )
                        },
                    ))
                })
                .collect(),
        )
        .propagating(secret)
    }

    /// No peer of class `peer` at all.
    pub fn no_network(peer: C) -> AgentRuleSet<P, C> {
        Self::per_action(
            [AgentAction::Contact],
            peer,
            &RegexExpr::all(),
            move |event| {
                (
                    format!("{} contacted a forbidden {peer} peer", event.principal),
                    Vec::new(),
                )
            },
        )
    }

    /// Changing (creating, modifying or removing) a resource of `class` requires an earlier
    /// operator approval of `class`.
    pub fn requires_approval(class: C) -> AgentRuleSet<P, C> {
        let approval = TestExpr::and([
            action_is(AgentAction::Approve, Comparison::Eq),
            class_is(class, Comparison::Eq),
        ]);
        let unapproved = RegexExpr::complement(ever(approval));
        Self::per_action(CHANGES, class, &unapproved, move |event| {
            (
                format!(
                    "{} may not change {class} resources without approval",
                    event.principal
                ),
                vec![format!("an operator approves {class}")],
            )
        })
    }

    /// Once a principal has changed a resource of `edited`, it may not change one of `locked`
    /// until an operator approves `locked`. With `(src, tests)`: no editing tests to make changed
    /// code pass.
    pub fn locked_after(edited: C, locked: C) -> AgentRuleSet<P, C> {
        let tail = since_unapproved(changed_by_p(edited), locked);
        Self::per_action(CHANGES, locked, &tail, move |event| {
            (
                format!(
                    "{} changed {edited} resources, so it may not also change {locked} resources",
                    event.principal
                ),
                vec![format!("an operator approves {locked}")],
            )
        })
    }

    /// Once a principal ran a program of any of `programs`, it may not change resources of the
    /// `protected` classes until an operator approves that class.
    pub fn tainted_by_run(programs: &[C], protected: &[C]) -> AgentRuleSet<P, C> {
        let ran = TestExpr::and([
            principal_is(Comparison::Eq),
            action_is(AgentAction::Run, Comparison::Eq),
            TestExpr::or(
                programs
                    .iter()
                    .map(|&program| class_is(program, Comparison::Eq)),
            ),
        ]);
        let names = programs
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let mut rules = AgentRuleSet::new(Vec::new());
        for &class in protected {
            let tail = since_unapproved(ran.clone(), class);
            let names = names.clone();
            rules
                .rules
                .extend(Self::per_action(CHANGES, class, &tail, move |event| {
                    (
                        format!(
                            "{} ran {names} and may not then change {class} resources",
                            event.principal
                        ),
                        vec![format!("an operator approves {class}")],
                    )
                }));
        }
        rules
    }

    /// Resources of `class` may be created but never modified or removed.
    pub fn append_only(class: C) -> AgentRuleSet<P, C> {
        Self::per_action(
            [AgentAction::Edit, AgentAction::Remove],
            class,
            &RegexExpr::all(),
            move |event| {
                (
                    format!(
                        "{class} resources are append-only; {} may only create them",
                        event.principal
                    ),
                    Vec::new(),
                )
            },
        )
    }

    /// A principal may remove at most `limit` resources between operator approvals of
    /// `approval`.
    pub fn deletion_budget(limit: usize, approval: C) -> AgentRuleSet<P, C> {
        let deletion = TestExpr::and([
            principal_is(Comparison::Eq),
            action_is(AgentAction::Remove, Comparison::Eq),
        ]);
        let quiet = RegexExpr::star(RegexExpr::test(not_approval(approval)));
        let mut tail = vec![RegexExpr::all()];
        for _ in 0..limit {
            tail.push(RegexExpr::test(deletion.clone()));
            tail.push(quiet.clone());
        }
        let rule = Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable(PRINCIPAL_VAR),
                ComponentPattern::constant(AgentAction::Remove),
                ComponentPattern::variable(RESOURCE_VAR),
            ),
            RegexExpr::concat(tail),
        );
        AgentRuleSet::new(vec![Self(TraceRule::new(
            rule,
            move |event: &AgentEvent<P, C>| {
                (
                    format!(
                        "{} exceeded its budget of {limit} removals",
                        event.principal
                    ),
                    vec![format!("an operator approves {approval}")],
                )
            },
        ))])
    }
}

/// The rules one [`AgentRule`] constructor produces; [`AgentPolicy::rule`] adds them all.
///
/// A set may also name classes that propagate: a principal that receives data of such a class
/// from another one holding it is judged as if it had read the class.
/// [`AgentRule::no_contact_after_read`] propagates its secret class.
pub struct AgentRuleSet<P: Label, C: Label> {
    rules: Vec<AgentRule<P, C>>,
    propagated: Vec<C>,
}

impl<P: Label, C: Label> AgentRuleSet<P, C> {
    const fn new(rules: Vec<AgentRule<P, C>>) -> Self {
        Self {
            rules,
            propagated: Vec::new(),
        }
    }

    /// Also propagates `class`.
    #[must_use]
    pub fn propagating(mut self, class: C) -> Self {
        self.propagated.push(class);
        self
    }
}

impl<P: Label, C: Label> Clone for AgentRuleSet<P, C> {
    fn clone(&self) -> Self {
        Self {
            rules: self.rules.clone(),
            propagated: self.propagated.clone(),
        }
    }
}

impl<P: Label, C: Label> Debug for AgentRuleSet<P, C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentRuleSet")
            .field("rules", &self.rules)
            .field("propagated", &self.propagated)
            .finish()
    }
}

impl<P: Label, C: Label> From<AgentRule<P, C>> for AgentRuleSet<P, C> {
    fn from(rule: AgentRule<P, C>) -> Self {
        Self::new(vec![rule])
    }
}

impl<P: Label, C: Label> IntoIterator for AgentRuleSet<P, C> {
    type Item = AgentRule<P, C>;
    type IntoIter = std::vec::IntoIter<AgentRule<P, C>>;

    fn into_iter(self) -> Self::IntoIter {
        self.rules.into_iter()
    }
}

#[cfg(test)]
mod tests;
