use std::collections::HashMap;

use string_interner::DefaultSymbol;

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::CompileError;

use super::node::CompiledAction;
use super::pattern::{Component, ComponentPattern};

#[derive(Clone, Copy, Debug)]
pub(super) enum BoundValue<'event> {
    Principal(&'event Principal),
    Action(&'event Action),
    Resource(&'event Resource),
}

impl BoundValue<'_> {
    pub(super) fn equals(self, other: Self) -> bool {
        match (self, other) {
            (Self::Principal(left), Self::Principal(right)) => left == right,
            (Self::Action(left), Self::Action(right)) => left == right,
            (Self::Resource(left), Self::Resource(right)) => left == right,
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Bindings<'event> {
    values: HashMap<DefaultSymbol, BoundValue<'event>>,
}

impl<'event> Bindings<'event> {
    pub(super) fn bind(&mut self, symbol: DefaultSymbol, value: BoundValue<'event>) -> bool {
        match self.values.get(&symbol).copied() {
            Some(existing) => existing.equals(value),
            None => {
                self.values.insert(symbol, value);
                true
            }
        }
    }

    pub(super) fn get(&self, symbol: DefaultSymbol) -> BoundValue<'event> {
        self.values
            .get(&symbol)
            .copied()
            .expect("compiled head binds every tail variable")
    }
}

pub(super) fn resource_matches(expected: &[&str], actual: &Resource) -> bool {
    expected.len() == actual.segments().len()
        && expected
            .iter()
            .zip(actual.segments())
            .all(|(left, right)| *left == right)
}

fn match_head_pattern<'event, Constant: Copy, Actual>(
    pattern: ComponentPattern<Constant, DefaultSymbol>,
    actual: &Actual,
    bound: BoundValue<'event>,
    bindings: &mut Bindings<'event>,
    constant_matches: impl FnOnce(Constant, &Actual) -> bool,
) -> bool {
    match pattern {
        ComponentPattern::Constant(expected) => constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => bindings.bind(symbol, bound),
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CompiledHead<'a> {
    pub(super) principal: ComponentPattern<&'a str, DefaultSymbol>,
    pub(super) action: ComponentPattern<CompiledAction<'a>, DefaultSymbol>,
    pub(super) resource: ComponentPattern<&'a [&'a str], DefaultSymbol>,
}

impl<'a> CompiledHead<'a> {
    pub(crate) fn matches<'event>(&self, event: &'event Event) -> Option<Bindings<'event>> {
        let mut bindings = Bindings::default();
        if !match_head_pattern(
            self.principal,
            &event.principal,
            BoundValue::Principal(&event.principal),
            &mut bindings,
            |expected, actual| actual.as_str() == expected,
        ) || !match_head_pattern(
            self.action,
            &event.action,
            BoundValue::Action(&event.action),
            &mut bindings,
            |expected, actual| expected.matches(actual),
        ) || !match_head_pattern(
            self.resource,
            &event.resource,
            BoundValue::Resource(&event.resource),
            &mut bindings,
            resource_matches,
        ) {
            return None;
        }
        Some(bindings)
    }
}

#[derive(Default)]
pub(super) struct Scope {
    variables: HashMap<DefaultSymbol, Component>,
}

impl Scope {
    pub(super) fn bind(
        &mut self,
        rule: usize,
        name: &str,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), CompileError> {
        if let Some(&bound_component) = self.variables.get(&symbol) {
            if bound_component != component {
                return Err(CompileError::VariableComponentConflict {
                    rule,
                    name: name.to_owned(),
                });
            }
            return Ok(());
        }
        self.variables.insert(symbol, component);
        Ok(())
    }

    pub(super) fn resolve(
        &self,
        rule: usize,
        name: &str,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), CompileError> {
        let Some(&bound_component) = self.variables.get(&symbol) else {
            return Err(CompileError::UnboundVariable {
                rule,
                name: name.to_owned(),
            });
        };
        if bound_component != component {
            return Err(CompileError::VariableComponentConflict {
                rule,
                name: name.to_owned(),
            });
        }
        Ok(())
    }
}
