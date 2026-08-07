//! Compile-time variable typing and per-candidate runtime substitution.
//!
//! A [`VariableEnvironment`] is created from one source head and exists only while that rule is
//! compiled. A [`CandidateSubstitution`] is created when the resulting compiled head matches one
//! candidate. Neither object is stored in source expressions or canonical syntax nodes.

use std::collections::HashMap;

use string_interner::DefaultSymbol;

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::{CompileError, RuleIndex};

use super::component::{BoundValue, CompiledPattern, Match};
use super::source::{Component, ComponentPattern};

/// Concrete candidate values assigned to head variables during one rule evaluation.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'event> {
    values: HashMap<DefaultSymbol, BoundValue<'event>>,
}

impl<'event> CandidateSubstitution<'event> {
    /// Binds an unbound name, or checks that a repeated occurrence denotes the same typed value.
    fn bind(&mut self, symbol: DefaultSymbol, value: BoundValue<'event>) -> bool {
        match self.values.get(&symbol).copied() {
            Some(existing) => existing == value,
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
fn match_head_pattern<'arena, 'event, ComponentType: Match<'arena>>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
    substitution: &mut CandidateSubstitution<'event>,
) -> bool {
    match pattern {
        ComponentPattern::Constant(expected) => ComponentType::constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => {
            substitution.bind(symbol, ComponentType::bound(actual))
        }
    }
}

/// Arena-backed head patterns stored in one compiled rule.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CompiledHead<'arena> {
    pub(super) principal: CompiledPattern<'arena, Principal>,
    pub(super) action: CompiledPattern<'arena, Action>,
    pub(super) resource: CompiledPattern<'arena, Resource>,
}

impl<'arena> CompiledHead<'arena> {
    /// Matches the candidate and returns its rule-local substitution.
    pub(crate) fn match_candidate<'event>(
        &self,
        event: &'event Event,
    ) -> Option<CandidateSubstitution<'event>> {
        let mut substitution = CandidateSubstitution::default();
        if !match_head_pattern(self.principal, &event.principal, &mut substitution)
            || !match_head_pattern(self.action, &event.action, &mut substitution)
            || !match_head_pattern(self.resource, &event.resource, &mut substitution)
        {
            return None;
        }
        Some(substitution)
    }
}

/// Rule-local type environment declared by a source head.
///
/// The map records which interned names exist and the product component occupied by each name. It
/// is a transient compiler input and is dropped after the tail has been compiled.
#[derive(Default)]
pub(crate) struct VariableEnvironment {
    variables: HashMap<DefaultSymbol, Component>,
}

impl VariableEnvironment {
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

    /// Verifies that a tail occurrence is declared by the head in the same component domain.
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
