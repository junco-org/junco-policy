//! Variable typing and per-candidate substitution.
//!
//! A [`VariableEnvironment`] validates one source head while its patterns are compiled. A matching
//! [`CompiledHead`] copies candidate component values into a temporary [`CandidateSubstitution`].
//! Neither object is stored in source expressions or canonical syntax nodes.

use std::collections::HashMap;
use string_interner::DefaultSymbol;

use crate::model::Event;

use super::component::{CandidateSubstitution, CompiledPattern, ResolvedValue};
use super::source::{Component, ComponentPattern};

/// Matches one typed head coordinate and returns its partial substitution.
///
/// `tag` places a bound value in the coordinate selected by the caller.
fn match_head_pattern<E: Event, T: Copy + Eq>(
    pattern: CompiledPattern<T>,
    actual: T,
    tag: impl FnOnce(T) -> ResolvedValue<E>,
) -> Option<CandidateSubstitution<E>> {
    match pattern {
        ComponentPattern::Constant(expected) => {
            (expected == actual).then(CandidateSubstitution::default)
        }
        ComponentPattern::Variable(variable) => {
            Some(CandidateSubstitution::singleton(variable, tag(actual)))
        }
    }
}

/// Compiled head patterns stored in one runtime rule.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CompiledHead<E: Event> {
    pub(super) principal: CompiledPattern<E::Principal>,
    pub(super) action: CompiledPattern<E::Action>,
    pub(super) resource: CompiledPattern<E::Resource>,
}

impl<E: Event> CompiledHead<E> {
    /// Matches the candidate's projected components and merges their partial substitutions.
    pub(crate) fn match_candidate(&self, event: &E) -> Option<CandidateSubstitution<E>> {
        let principal = match_head_pattern(
            self.principal,
            event.principal(),
            ResolvedValue::<E>::Principal,
        )?;
        let action = match_head_pattern(self.action, event.action(), ResolvedValue::<E>::Action)?;
        let principal_action = principal.merge(&action)?;
        let resource = match_head_pattern(
            self.resource,
            event.resource(),
            ResolvedValue::<E>::Resource,
        )?;
        principal_action.merge(&resource)
    }
}

/// Structural failure while resolving an interned variable symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ResolveError {
    /// The rule head did not declare the variable.
    Unbound,
    /// The head declared the variable in another component domain.
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
    /// Returns the existing component when the variable was previously bound in a different domain;
    /// the compiler caller owns source names and diagnostic construction.
    pub(super) fn bind(
        &mut self,
        variable: DefaultSymbol,
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
        variable: DefaultSymbol,
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
