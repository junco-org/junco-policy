//! Information-flow rules over `(principal, handle, action, label)` observations.
//!
//! Taint belongs to a principal's copy of a handle. Callers record [`FlowAction::Receive`]
//! when labeled data propagates; receiving and reading both establish taint. Only a
//! matching principal, handle, and label can declassify that copy.

use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::str::FromStr;

use history_semantics::TraceRule;
use history_semantics::policy::{PRINCIPAL_VAR, component_equals, component_is, last_state_change};
use history_syntax::{
    Comparison, Component, ComponentPattern, Event, Head, N4, Rule, RuleMode, TestExpr,
};

use super::agent::Label;
use super::rules::{RuleDenial, RulePolicy, RuleSet};

const HANDLE_VAR: &str = "v";

/// How a principal used or changed the classification of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FlowAction {
    /// Read data with the observed label.
    Read,
    /// Received data with a propagated label.
    Receive,
    /// Passed the value to a sink with the observed label.
    Contact,
    /// Declassified the observed label for this principal's copy of the value.
    Declassify,
}

impl Display for FlowAction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Read => "read",
            Self::Receive => "receive",
            Self::Contact => "contact",
            Self::Declassify => "declassify",
        })
    }
}

impl FromStr for FlowAction {
    type Err = String;

    /// Parses the lowercase action name written by [`Display`].
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        match text {
            "read" => Ok(Self::Read),
            "receive" => Ok(Self::Receive),
            "contact" => Ok(Self::Contact),
            "declassify" => Ok(Self::Declassify),
            other => Err(format!("invalid action: {other:?}")),
        }
    }
}

/// One labeled observation of a principal's copy of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FlowEvent<P, V, L> {
    /// The acting principal.
    pub principal: P,
    /// The handle identifying the value.
    pub handle: V,
    /// How the principal used or classified the value.
    pub action: FlowAction,
    /// The data's classification, or the contacted sink's classification.
    pub label: L,
}

/// A tagged coordinate of a [`FlowEvent`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FlowComponent<P, V, L> {
    /// The principal at coordinate 0.
    Principal(P),
    /// The value handle at coordinate 1.
    Handle(V),
    /// The action at coordinate 2.
    Action(FlowAction),
    /// The classification at coordinate 3.
    Label(L),
}

// This root crate is not a Verus target. Keeping the public tagged component enum
// preserves callers' vocabulary; use of verified guarantees requires R1 projection
// laws and R4 key laws for this implementation, including the action coordinate.
impl<P, V, L> Event for FlowEvent<P, V, L>
where
    P: Copy + Debug + Eq + Hash,
    V: Copy + Debug + Eq + Hash,
    L: Copy + Debug + Eq + Hash,
{
    type Component = FlowComponent<P, V, L>;
    type Arity = N4;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => FlowComponent::Principal(self.principal),
            1 => FlowComponent::Handle(self.handle),
            2 => FlowComponent::Action(self.action),
            _ => FlowComponent::Label(self.label),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            FlowComponent::Principal(_) => 0,
            FlowComponent::Handle(_) => 1,
            FlowComponent::Action(_) => 2,
            FlowComponent::Label(_) => 3,
        }
    }
}

impl<P: Display, V: Display, L: Display> Display for FlowEvent<P, V, L> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} {} {} {}",
            self.principal, self.handle, self.action, self.label
        )
    }
}

/// An information-flow policy over principal-local value handles.
pub type FlowPolicy<P, V, L> = RulePolicy<FlowEvent<P, V, L>>;

/// A refused information-flow event and its rendered diagnostic.
pub type FlowDenial<P, V, L> = RuleDenial<FlowEvent<P, V, L>>;

/// A caller-built rule over the four-coordinate information-flow vocabulary.
#[derive(Clone, Debug)]
pub struct FlowRule<P: Label, V: Label, L: Label>(TraceRule<FlowEvent<P, V, L>>);

impl<P: Label, V: Label, L: Label> FlowRule<P, V, L> {
    /// Wraps a caller-built trace rule with its diagnostic.
    pub const fn custom(rule: TraceRule<FlowEvent<P, V, L>>) -> Self {
        Self(rule)
    }

    /// Forbids passing a tainted value to any of `sinks` until it is declassified.
    ///
    /// Reading or receiving `tainted` data establishes taint for the same principal
    /// and handle as the candidate contact. Only declassifying that label for that
    /// principal and handle clears it. Returns one rule per sink label.
    pub fn no_contact_after_read(tainted: L, sinks: &[L]) -> RuleSet<FlowEvent<P, V, L>> {
        let taint = TestExpr::and([
            component_is(Component(0), PRINCIPAL_VAR, Comparison::Eq),
            component_is(Component(1), HANDLE_VAR, Comparison::Eq),
            TestExpr::or([
                component_equals(
                    Component(2),
                    FlowComponent::Action(FlowAction::Read),
                    Comparison::Eq,
                ),
                component_equals(
                    Component(2),
                    FlowComponent::Action(FlowAction::Receive),
                    Comparison::Eq,
                ),
            ]),
            component_equals(Component(3), FlowComponent::Label(tainted), Comparison::Eq),
        ]);
        let kept = TestExpr::or([
            component_is(Component(0), PRINCIPAL_VAR, Comparison::Neq),
            component_is(Component(1), HANDLE_VAR, Comparison::Neq),
            component_equals(
                Component(2),
                FlowComponent::Action(FlowAction::Declassify),
                Comparison::Neq,
            ),
            component_equals(Component(3), FlowComponent::Label(tainted), Comparison::Neq),
        ]);
        let tail = last_state_change(taint, kept);
        RuleSet::new(
            sinks
                .iter()
                .map(|&sink| {
                    TraceRule::new(
                        Rule::new(
                            RuleMode::Forbid,
                            Head::new([
                                ComponentPattern::variable(PRINCIPAL_VAR),
                                ComponentPattern::variable(HANDLE_VAR),
                                ComponentPattern::constant(FlowComponent::Action(FlowAction::Contact)),
                                ComponentPattern::constant(FlowComponent::Label(sink)),
                            ]),
                            tail.clone(),
                        ),
                        move |event: &FlowEvent<P, V, L>| {
                            (
                                format!(
                                    "{} passed {} to a {sink} sink after receiving {tainted} data",
                                    event.principal, event.handle
                                ),
                                vec![format!(
                                    "declassify {tainted} for {}'s copy of {}, or pass a value not derived from {tainted} data",
                                    event.principal, event.handle
                                )],
                            )
                        },
                    )
                })
                .collect(),
        )
    }
}

impl<P: Label, V: Label, L: Label> From<FlowRule<P, V, L>> for RuleSet<FlowEvent<P, V, L>> {
    fn from(rule: FlowRule<P, V, L>) -> Self {
        Self::new(vec![rule.0])
    }
}

#[cfg(test)]
mod tests;
