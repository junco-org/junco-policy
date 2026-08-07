//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with both its arena-backed constant representation and
//! its borrowed candidate-binding representation. Each implementation also selects the matching
//! typed map in [`CandidateSubstitution`]. Principal matching therefore cannot accidentally produce
//! or retrieve a resource binding.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use bumpalo::Bump;
use string_interner::DefaultSymbol;

use crate::model::{Action, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern, PatternRepresentation};

/// Arena-backed action value used by compiled patterns.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum CompiledAction<'arena> {
    Read,
    Edit,
    Stage,
    Unstage,
    Commit(Option<&'arena str>),
    Checkout,
    Stash,
    Diff,
    History,
}

/// Candidate values assigned to head variables during one rule evaluation.
///
/// Separate maps preserve the component type through storage and lookup. The map choice is an
/// associated operation of [`ComponentDomain`], rather than an erased enum returned by component code.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'event> {
    principals: HashMap<DefaultSymbol, &'event Principal>,
    actions: HashMap<DefaultSymbol, &'event Action>,
    resources: HashMap<DefaultSymbol, &'event Resource>,
}

/// Compiles and matches one capability-product component.
///
/// `Compiled` is stored in hashconsed atom nodes. Runtime bindings are always `&Self` and live in
/// the typed substitution map selected by the implementation, so no separate binding conversion
/// or associated binding type is needed.
pub(super) trait ComponentDomain<'arena>: Sized + Eq {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Immutable arena-backed representation embedded in compiled patterns.
    type Compiled: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Copies `value` into the validator arena when ownership or stable borrowing requires it.
    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled;

    /// Compares one compiled constant with an event component.
    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool;

    /// Returns the immutable substitution map belonging to this component.
    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, &'event Self>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, &'event Self>;
}

impl<'arena> ComponentDomain<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = &'arena str;

    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled {
        arena.alloc_str(value.as_str())
    }

    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool {
        actual.as_str() == expected
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, &'event Self> {
        &substitution.principals
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, &'event Self> {
        &mut substitution.principals
    }
}

impl<'arena> ComponentDomain<'arena> for Action {
    const COMPONENT: Component = Component::Action;
    type Compiled = CompiledAction<'arena>;

    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled {
        match value {
            Action::Read => CompiledAction::Read,
            Action::Edit => CompiledAction::Edit,
            Action::Stage => CompiledAction::Stage,
            Action::Unstage => CompiledAction::Unstage,
            Action::Commit { message } => CompiledAction::Commit(
                message
                    .as_deref()
                    .map(|message| arena.alloc_str(message) as &str),
            ),
            Action::Checkout => CompiledAction::Checkout,
            Action::Stash => CompiledAction::Stash,
            Action::Diff => CompiledAction::Diff,
            Action::History => CompiledAction::History,
        }
    }

    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool {
        match (expected, actual) {
            (CompiledAction::Read, Action::Read)
            | (CompiledAction::Edit, Action::Edit)
            | (CompiledAction::Stage, Action::Stage)
            | (CompiledAction::Unstage, Action::Unstage)
            | (CompiledAction::Checkout, Action::Checkout)
            | (CompiledAction::Stash, Action::Stash)
            | (CompiledAction::Diff, Action::Diff)
            | (CompiledAction::History, Action::History) => true,
            (CompiledAction::Commit(expected), Action::Commit { message }) => {
                expected == message.as_deref()
            }
            _ => false,
        }
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, &'event Self> {
        &substitution.actions
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, &'event Self> {
        &mut substitution.actions
    }
}

impl<'arena> ComponentDomain<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Compiled = &'arena [&'arena str];

    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled {
        let segments: Vec<&'arena str> = value
            .segments()
            .iter()
            .map(|segment| arena.alloc_str(segment) as &str)
            .collect();
        arena.alloc_slice_copy(&segments)
    }

    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool {
        expected.len() == actual.segments().len()
            && expected
                .iter()
                .zip(actual.segments())
                .all(|(left, right)| *left == right)
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, &'event Self> {
        &substitution.resources
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, &'event Self> {
        &mut substitution.resources
    }
}

/// Arena-backed representation used by compiled atom patterns.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct CompiledRepresentation<'arena>(PhantomData<&'arena ()>);

impl<'arena> PatternRepresentation for CompiledRepresentation<'arena> {
    type PrincipalValue = <Principal as ComponentDomain<'arena>>::Compiled;
    type ActionValue = <Action as ComponentDomain<'arena>>::Compiled;
    type ResourceValue = <Resource as ComponentDomain<'arena>>::Compiled;
    type Variable = DefaultSymbol;
}

/// Compiled pattern for one statically selected component type.
pub(super) type CompiledPattern<'arena, ComponentType> =
    ComponentPattern<<ComponentType as ComponentDomain<'arena>>::Compiled, DefaultSymbol>;

/// Concrete, structurally hashable atom representation stored in [`TestNode`](super::node::TestNode).
pub(super) type CompiledAtomPattern<'arena> = AtomPattern<CompiledRepresentation<'arena>>;
