use crate::model::{Action, Principal, Resource};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ComponentPattern<T, Variable = String> {
    Constant(T),
    Variable(Variable),
}

impl<T> ComponentPattern<T, String> {
    pub fn constant(value: impl Into<T>) -> Self {
        Self::Constant(value.into())
    }

    pub fn variable(name: impl Into<String>) -> Self {
        Self::Variable(name.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Head {
    pub principal: ComponentPattern<Principal>,
    pub action: ComponentPattern<Action>,
    pub resource: ComponentPattern<Resource>,
}

impl Head {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Component {
    Principal,
    Action,
    Resource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Comparison {
    Eq,
    Neq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtomPattern<
    PrincipalValue = Principal,
    ActionValue = Action,
    ResourceValue = Resource,
    Variable = String,
> {
    Principal(ComponentPattern<PrincipalValue, Variable>),
    Action(ComponentPattern<ActionValue, Variable>),
    Resource(ComponentPattern<ResourceValue, Variable>),
}

impl<PrincipalValue, ActionValue, ResourceValue, Variable>
    AtomPattern<PrincipalValue, ActionValue, ResourceValue, Variable>
{
    pub fn component(&self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    Require,
    Forbid,
}
