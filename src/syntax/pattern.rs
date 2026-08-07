//! Public source language for candidate heads, one-event tests, and rule modes.
//!
//! Source values own constants and variable names. Compilation validates their typed variable
//! scope and transforms them into immutable arena-backed patterns before hashconsing.

use crate::model::{Action, Principal, Resource};

/// Constant-or-variable pattern for one statically selected product component.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ComponentPattern<T, Variable = String> {
    /// Match one structurally equal component value.
    Constant(T),
    /// Bind or resolve a named component value.
    Variable(Variable),
}

impl<T> ComponentPattern<T, String> {
    /// Creates a constant pattern from a value convertible to `T`.
    pub fn constant(value: impl Into<T>) -> Self {
        Self::Constant(value.into())
    }

    /// Creates a named variable pattern.
    pub fn variable(name: impl Into<String>) -> Self {
        Self::Variable(name.into())
    }
}

/// Candidate-only pattern over the capability product.
///
/// A successful head match yields the substitution used by the tail. The candidate itself is not
/// part of the history evaluated by that tail.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Head {
    /// Principal constant or variable.
    pub principal: ComponentPattern<Principal>,
    /// Action constant or variable.
    pub action: ComponentPattern<Action>,
    /// Resource constant or variable.
    pub resource: ComponentPattern<Resource>,
}

impl Head {
    /// Creates a typed `(principal, action, resource)` head.
    pub fn new(
        principal: ComponentPattern<Principal>,
        action: ComponentPattern<Action>,
        resource: ComponentPattern<Resource>,
    ) -> Self {
        Self {
            principal,
            action,
            resource,
        }
    }
}

/// Coordinate of the capability product.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Component {
    /// Principal coordinate.
    Principal,
    /// Action coordinate.
    Action,
    /// Resource coordinate.
    Resource,
}

/// Comparison applied by a one-event atom.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Comparison {
    /// Accept when the event component equals the constant or bound variable.
    Eq,
    /// Accept when the event component differs from the constant or bound variable.
    Neq,
}

/// Typed one-event component pattern.
///
/// The generic parameters allow the same enum shape to represent owned source values and compiled
/// arena-backed values. Compiled atoms remain a concrete `Hash + Eq` enum so they can be hashconsed
/// structurally without trait-object indirection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtomPattern<
    PrincipalValue = Principal,
    ActionValue = Action,
    ResourceValue = Resource,
    Variable = String,
> {
    /// Test the event principal.
    Principal(ComponentPattern<PrincipalValue, Variable>),
    /// Test the event action.
    Action(ComponentPattern<ActionValue, Variable>),
    /// Test the event resource.
    Resource(ComponentPattern<ResourceValue, Variable>),
}

impl<PrincipalValue, ActionValue, ResourceValue, Variable>
    AtomPattern<PrincipalValue, ActionValue, ResourceValue, Variable>
{
    /// Returns the product coordinate selected by this atom.
    pub fn component(&self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

/// Relationship required between committed history and a matching rule tail.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    /// Deny when committed history is outside the tail language.
    Require,
    /// Deny when committed history is inside the tail language.
    Forbid,
}
