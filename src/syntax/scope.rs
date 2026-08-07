//! Rule-local variable scope, candidate bindings, and compiled-head evaluation.
//!
//! Names are interned globally by `SyntaxContext`, but a `Scope` records the component domain in
//! which each name is valid for one rule. At runtime a successful head match produces `Bindings`
//! that borrow the candidate event. Tail evaluation can read those references without allocating
//! or copying event components.

use std::collections::HashMap;

use string_interner::DefaultSymbol;

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::{CompileError, RuleIndex};

use super::component::{BoundValue, CompiledPattern, Match};
use super::pattern::{Component, ComponentPattern};

/// Candidate values bound to the variables of one matching rule head.
#[derive(Debug, Default)]
pub(crate) struct Bindings<'event> {
    values: HashMap<DefaultSymbol, BoundValue<'event>>,
}

impl<'event> Bindings<'event> {
    /// Binds an unbound name, or checks that a repeated occurrence denotes the same typed value.
    fn bind(&mut self, symbol: DefaultSymbol, value: BoundValue<'event>) -> bool {
        match self.values.get(&symbol).copied() {
            Some(existing) => existing.equals(value),
            None => {
                self.values.insert(symbol, value);
                true
            }
        }
    }

    /// Resolves a name proven by compilation to be bound by the head.
    pub(super) fn get(&self, symbol: DefaultSymbol) -> BoundValue<'event> {
        self.values
            .get(&symbol)
            .copied()
            .expect("compiled head binds every tail variable")
    }
}

/// Matches one typed head coordinate and updates the candidate substitution.
///
/// The associated `Compiled` type, constant comparison, and binding conversion all come from
/// `Match`; the helper no longer needs separate constant/actual generic parameters, an erased value
/// argument, or a comparison closure.
fn match_head_pattern<'arena, 'event, ComponentType: Match<'arena>>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
    bindings: &mut Bindings<'event>,
) -> bool {
    match pattern {
        ComponentPattern::Constant(expected) => ComponentType::constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => bindings.bind(symbol, ComponentType::bound(actual)),
    }
}

/// Arena-backed head patterns for the fixed `(principal, action, resource)` product.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CompiledHead<'arena> {
    pub(super) principal: CompiledPattern<'arena, Principal>,
    pub(super) action: CompiledPattern<'arena, Action>,
    pub(super) resource: CompiledPattern<'arena, Resource>,
}

impl<'arena> CompiledHead<'arena> {
    /// Matches the candidate only; the returned substitution is then used over pre-candidate
    /// committed history. Failure does not allocate or mutate policy state.
    pub(crate) fn matches<'event>(&self, event: &'event Event) -> Option<Bindings<'event>> {
        let mut bindings = Bindings::default();
        if !match_head_pattern(self.principal, &event.principal, &mut bindings)
            || !match_head_pattern(self.action, &event.action, &mut bindings)
            || !match_head_pattern(self.resource, &event.resource, &mut bindings)
        {
            return None;
        }
        Some(bindings)
    }
}

/// Component-domain declarations for variables bound by one source head.
#[derive(Default)]
pub(super) struct Scope {
    variables: HashMap<DefaultSymbol, Component>,
}

impl Scope {
    /// Records one head occurrence and rejects reuse in another component domain.
    pub(super) fn bind(
        &mut self,
        rule: RuleIndex,
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

    /// Verifies that a tail occurrence is bound by the head in the same component domain.
    pub(super) fn resolve(
        &self,
        rule: RuleIndex,
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
