//! Agent policies: past-time rules over classified observations of what agents did.
//!
//! [`crate::LockPolicy`] speaks about exact resources. An agent policy speaks about *classes*: the
//! caller classifies every concrete resource it observes — a path read
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
//! [`AgentPolicy::check`] decides and appends a batch of candidates to a log the caller owns;
//! [`AgentPolicy::decide`] decides one candidate as it happens. Both compile only the rules whose
//! head can match a candidate.
//!
//! Rules follow the principal that read a class. The caller tracks which principals hold such
//! data and logs [`AgentAction::Receive`] when data moves; [`AgentRule::no_contact_after_read`]
//! treats receiving the class like reading it.

use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use history_semantics::TraceRule;
use history_semantics::policy::{
    PRINCIPAL_VAR, RESOURCE_VAR, action_is, last_state_change, principal_is,
};
use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Event, Head, N3, RegexExpr, Rule,
    RuleMode, TestExpr,
};

use super::rules::{RuleDenial, RulePolicy, RuleSet};

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

/// Tagged coordinates of an [`AgentEvent`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AgentComponent<P, C> {
    /// Coordinate 0: the principal.
    Principal(P),
    /// Coordinate 1: the observed action.
    Action(AgentAction),
    /// Coordinate 2: the resource class.
    Class(C),
}

impl<P, C> Event for AgentEvent<P, C>
where
    P: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash,
{
    type Component = AgentComponent<P, C>;
    type Arity = N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => AgentComponent::Principal(self.principal),
            1 => AgentComponent::Action(self.action),
            _ => AgentComponent::Class(self.resource),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            AgentComponent::Principal(_) => 0,
            AgentComponent::Action(_) => 1,
            AgentComponent::Class(_) => 2,
        }
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

/// One refused classified observation, with the violated rule's explanation.
pub type AgentDenial<P, C> = RuleDenial<AgentEvent<P, C>>;

/// Ordered rules over classified observations, with optional auditing.
pub type AgentPolicy<P, C> = RulePolicy<AgentEvent<P, C>>;

/// The ordered rules produced by an [`AgentRule`] constructor.
pub type AgentRuleSet<P, C> = RuleSet<AgentEvent<P, C>>;

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
        AtomPattern::new(
            Component(2),
            ComponentPattern::constant(AgentComponent::Class(class)),
        ),
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
                .map(|action| action_is(AgentComponent::Action(action), Comparison::Eq)),
        ),
    ])
}

/// Any event that is not an approval of `label`.
fn not_approval<P: Label, C: Label>(label: C) -> Test<P, C> {
    TestExpr::or([
        action_is(
            AgentComponent::Action(AgentAction::Approve),
            Comparison::Neq,
        ),
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
        action_is(
            AgentComponent::Action(AgentAction::Declassify),
            Comparison::Neq,
        ),
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
        Head::new([
            ComponentPattern::variable(PRINCIPAL_VAR),
            ComponentPattern::constant(AgentComponent::Action(action)),
            ComponentPattern::constant(AgentComponent::Class(class)),
        ]),
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
                .map(|action| TraceRule::new(forbid(action, class, tail.clone()), render.clone()))
                .collect(),
        )
    }

    /// No peer of any of `peers` once the same principal has read a resource of `secret`, or
    /// received its data from another principal, unless an operator has since declassified
    /// `secret` for that principal.
    pub fn no_contact_after_read(secret: C, peers: &[C]) -> AgentRuleSet<P, C> {
        let read = TestExpr::and([
            principal_is(Comparison::Eq),
            TestExpr::or([
                action_is(AgentComponent::Action(AgentAction::Read), Comparison::Eq),
                action_is(AgentComponent::Action(AgentAction::Receive), Comparison::Eq),
            ]),
            class_is(secret, Comparison::Eq),
        ]);
        let tail = since_undeclassified(read, secret);
        AgentRuleSet::new(
            peers
                .iter()
                .map(|&peer| {
                    TraceRule::new(forbid(AgentAction::Contact, peer, tail.clone()),
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
                    },)
                })
                .collect(),
        )
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

    /// `class` can never be declassified: an operator's declassification of it for any principal
    /// is refused.
    pub fn undeclassifiable(class: C) -> AgentRuleSet<P, C> {
        Self::per_action(
            [AgentAction::Declassify],
            class,
            &RegexExpr::all(),
            move |event| {
                (
                    format!("{class} cannot be declassified for {}", event.principal),
                    Vec::new(),
                )
            },
        )
    }

    /// Changing (creating, modifying or removing) a resource of `class` requires an earlier
    /// operator approval of `class`.
    pub fn requires_approval(class: C) -> AgentRuleSet<P, C> {
        let approval = TestExpr::and([
            action_is(AgentComponent::Action(AgentAction::Approve), Comparison::Eq),
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
            action_is(AgentComponent::Action(AgentAction::Run), Comparison::Eq),
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
            rules.rules.extend(
                Self::per_action(CHANGES, class, &tail, move |event| {
                    (
                        format!(
                            "{} ran {names} and may not then change {class} resources",
                            event.principal
                        ),
                        vec![format!("an operator approves {class}")],
                    )
                })
                .rules,
            );
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
            action_is(AgentComponent::Action(AgentAction::Remove), Comparison::Eq),
        ]);
        let quiet = RegexExpr::star(RegexExpr::test(not_approval(approval)));
        let mut tail = vec![RegexExpr::all()];
        for _ in 0..limit {
            tail.push(RegexExpr::test(deletion.clone()));
            tail.push(quiet.clone());
        }
        let rule = Rule::new(
            RuleMode::Forbid,
            Head::new([
                ComponentPattern::variable(PRINCIPAL_VAR),
                ComponentPattern::constant(AgentComponent::Action(AgentAction::Remove)),
                ComponentPattern::variable(RESOURCE_VAR),
            ]),
            RegexExpr::concat(tail),
        );
        AgentRuleSet::new(vec![TraceRule::new(
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
        )])
    }
}

impl<P: Label, C: Label> From<AgentRule<P, C>> for AgentRuleSet<P, C> {
    fn from(rule: AgentRule<P, C>) -> Self {
        Self::new(vec![rule.0])
    }
}

#[cfg(test)]
mod tests;
