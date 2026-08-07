//! Compile-time variable typing and per-candidate runtime substitution.
//!
//! A [`VariableEnvironment`] is created from one source head and exists only while that rule is
//! compiled. A [`CandidateSubstitution`] interns values from one matching candidate into the
//! canonical value store. Neither object is stored in source expressions or canonical syntax nodes.

use std::collections::HashMap;

use crate::model::{Action, Event, Principal, Resource};

use super::component::{CandidateSubstitution, CompiledPattern, ComponentDomain};
use super::source::{Component, ComponentPattern};
use super::store::CanonicalStore;
use super::variable::VariableSymbol;

/// Matches one typed head coordinate and returns its partial substitution.
fn match_head_pattern<'arena, ComponentType>(
    store: &mut CanonicalStore<'arena>,
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &ComponentType,
) -> Option<CandidateSubstitution<'arena>>
where
    ComponentType: ComponentDomain<'arena>,
{
    match pattern.into_inner() {
        ComponentPattern::Constant(expected) => {
            ComponentType::compiled_matches(&store.values, expected, actual)
                .then(CandidateSubstitution::default)
        }
        ComponentPattern::Variable(variable) => {
            let mut substitution = CandidateSubstitution::default();
            let value = ComponentType::compile(&mut store.values, actual);
            ComponentType::bindings_mut(&mut substitution).insert(variable, value);
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
    /// Matches the candidate, interns variable bindings, and merges partial substitutions.
    pub(crate) fn match_candidate(
        &self,
        store: &mut CanonicalStore<'arena>,
        event: &Event,
    ) -> Option<CandidateSubstitution<'arena>> {
        match_head_pattern(store, self.principal, &event.principal)
            .and_then(|principal| {
                match_head_pattern(store, self.action, &event.action)
                    .map(|action| principal.merge(action))
            })
            .and_then(|principal_action| {
                match_head_pattern(store, self.resource, &event.resource)
                    .map(|resource| principal_action.merge(resource))
            })
    }
}

/// Structural failure while resolving a compiled variable reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ResolveError {
    /// The rule head did not declare the variable.
    Unbound,
    /// The head declared the variable in another component domain.
    ComponentConflict,
}

/// Rule-local type environment declared by a source head.
///
/// The map records which arena-backed names exist and the product component occupied by each name. It
/// is a transient compiler input and is dropped after the tail has been compiled.
#[derive(Default)]
pub(crate) struct VariableEnvironment {
    variables: HashMap<VariableSymbol, Component>,
}

impl VariableEnvironment {
    /// Records one head occurrence.
    ///
    /// Returns the existing component when the variable was previously bound in a different domain;
    /// the compiler caller owns source names and diagnostic construction.
    pub(super) fn bind(
        &mut self,
        variable: VariableSymbol,
        component: Component,
    ) -> Result<(), Component> {
        match self.variables.get(&variable) {
            Some(&bound_component) if bound_component != component => Err(bound_component),
            Some(_) => Ok(()),
            None => {
                self.variables.insert(variable, component);
                Ok(())
            }
        }
    }

    /// Verifies that a tail occurrence is declared by the head in the same component domain.
    pub(super) fn resolve(
        &self,
        variable: VariableSymbol,
        component: Component,
    ) -> Result<(), ResolveError> {
        match self.variables.get(&variable) {
            Some(&bound_component) if bound_component != component => {
                Err(ResolveError::ComponentConflict)
            }
            Some(_) => Ok(()),
            None => Err(ResolveError::Unbound),
        }
    }
}
