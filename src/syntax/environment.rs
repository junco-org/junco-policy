//! Compile-time variable typing and per-candidate runtime substitution.
//!
//! A [`VariableEnvironment`] is created from one source head and exists only while that rule is
//! compiled. A [`CandidateSubstitution`] is created when the resulting compiled head matches one
//! candidate. Neither object is stored in source expressions or canonical syntax nodes.

use std::collections::HashMap;

use string_interner::DefaultSymbol;

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::{CompileError, RuleIndex};

use super::component::{CandidateSubstitution, CompiledPattern, ComponentDomain};
use super::source::{Component, ComponentPattern};

/// Matches one typed head coordinate and updates the candidate substitution.
fn match_head_pattern<'arena, 'event, ComponentType>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
    substitution: &mut CandidateSubstitution<'event>,
) -> bool
where
    ComponentType: ComponentDomain<'arena> + 'event,
{
    match pattern {
        ComponentPattern::Constant(expected) => ComponentType::constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => {
            match ComponentType::bindings_mut(substitution)
                .get(&symbol)
                .copied()
            {
                Some(existing) => existing == actual,
                None => {
                    ComponentType::bindings_mut(substitution).insert(symbol, actual);
                    true
                }
            }
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
