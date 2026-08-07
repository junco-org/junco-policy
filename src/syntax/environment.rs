//! Compile-time variable typing and per-candidate runtime substitution.
//!
//! A [`VariableEnvironment`] is created from one source head and exists only while that rule is
//! compiled. A [`CandidateSubstitution`] is created when the resulting compiled head matches one
//! candidate. Neither object is stored in source expressions or canonical syntax nodes.

use std::collections::HashMap;

use string_interner::DefaultSymbol;

use crate::model::{Action, Event, Principal, Resource};

use super::component::{CandidateSubstitution, CompiledPattern, ComponentDomain};
use super::source::{Component, ComponentPattern};

/// Matches one typed head coordinate and returns its partial substitution.
fn match_head_pattern<'arena, 'event, ComponentType>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
) -> Option<CandidateSubstitution<'event>>
where
    ComponentType: ComponentDomain<'arena> + 'event,
{
    match pattern {
        ComponentPattern::Constant(expected) => {
            ComponentType::constant_matches(expected, actual).then(CandidateSubstitution::default)
        }
        ComponentPattern::Variable(symbol) => {
            let mut substitution = CandidateSubstitution::default();
            ComponentType::bindings_mut(&mut substitution).insert(symbol, actual);
            Some(substitution)
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
    /// Matches the candidate and merges the three compatible partial substitutions.
    pub(crate) fn match_candidate<'event>(
        &self,
        event: &'event Event,
    ) -> Option<CandidateSubstitution<'event>> {
        match_head_pattern(self.principal, &event.principal)
            .and_then(|principal| {
                match_head_pattern(self.action, &event.action)
                    .and_then(|action| principal.merge(action))
            })
            .and_then(|principal_action| {
                match_head_pattern(self.resource, &event.resource)
                    .and_then(|resource| principal_action.merge(resource))
            })
    }
}

/// Structural failure while resolving a compiled variable symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ResolveError {
    /// The rule head did not declare the symbol.
    Unbound,
    /// The head declared the symbol in another component domain.
    ComponentConflict,
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
    /// Records one head occurrence.
    ///
    /// Returns the existing component when the symbol was previously bound in a different domain;
    /// the compiler caller owns source names, rule indexes, and diagnostic construction.
    pub(super) fn bind(
        &mut self,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), Component> {
        match self.variables.get(&symbol).copied() {
            Some(bound_component) if bound_component != component => Err(bound_component),
            Some(_) => Ok(()),
            None => {
                self.variables.insert(symbol, component);
                Ok(())
            }
        }
    }

    /// Verifies that a tail occurrence is declared by the head in the same component domain.
    pub(super) fn resolve(
        &self,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), ResolveError> {
        match self.variables.get(&symbol).copied() {
            Some(bound_component) if bound_component != component => {
                Err(ResolveError::ComponentConflict)
            }
            Some(_) => Ok(()),
            None => Err(ResolveError::Unbound),
        }
    }
}
