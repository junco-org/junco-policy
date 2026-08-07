//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`Match`] associates each model component with both its arena-backed constant representation and
//! its borrowed candidate-binding representation. Each implementation also selects the matching
//! typed map in [`CandidateSubstitution`]. Principal matching therefore cannot accidentally produce
//! or retrieve a resource binding.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use bumpalo::Bump;
use string_interner::DefaultSymbol;

use crate::model::{Action, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern};

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
/// associated operation of [`Match`], rather than an erased enum returned by component code.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'event> {
    principals: HashMap<DefaultSymbol, &'event Principal>,
    actions: HashMap<DefaultSymbol, &'event Action>,
    resources: HashMap<DefaultSymbol, &'event Resource>,
}

/// Compiles and matches one capability-product component.
///
/// Both associated types are structural: `Compiled` is stored in hashconsed atom nodes, while
/// `Bound` is stored in the corresponding typed substitution map. Implementations are statically
/// dispatched and intentionally unavailable as trait objects inside the canonical DAG.
pub(super) trait Match<'arena>: Sized {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Immutable arena-backed representation embedded in compiled patterns.
    type Compiled: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Borrowed candidate value stored for a variable of this component.
    type Bound<'event>: Clone + Copy + Debug + PartialEq + Eq
    where
        Self: 'event;

    /// Copies `value` into the validator arena when ownership or stable borrowing requires it.
    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled;

    /// Compares one compiled constant with an event component.
    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool;

    /// Converts an event component to its typed borrowed binding.
    fn bound<'event>(actual: &'event Self) -> Self::Bound<'event>;

    /// Returns the immutable substitution map belonging to this component.
    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Bound<'event>>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Bound<'event>>;
}

impl<'arena> Match<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = &'arena str;
    type Bound<'event> = &'event Principal;

    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled {
        arena.alloc_str(value.as_str())
    }

    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool {
        actual.as_str() == expected
    }

    fn bound<'event>(actual: &'event Self) -> Self::Bound<'event> {
        actual
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Bound<'event>> {
        &substitution.principals
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Bound<'event>> {
        &mut substitution.principals
    }
}

impl<'arena> Match<'arena> for Action {
    const COMPONENT: Component = Component::Action;
    type Compiled = CompiledAction<'arena>;
    type Bound<'event> = &'event Action;

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

    fn bound<'event>(actual: &'event Self) -> Self::Bound<'event> {
        actual
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Bound<'event>> {
        &substitution.actions
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Bound<'event>> {
        &mut substitution.actions
    }
}

impl<'arena> Match<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Compiled = &'arena [&'arena str];
    type Bound<'event> = &'event Resource;

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

    fn bound<'event>(actual: &'event Self) -> Self::Bound<'event> {
        actual
    }

    fn bindings<'substitution, 'event>(
        substitution: &'substitution CandidateSubstitution<'event>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Bound<'event>> {
        &substitution.resources
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'event>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Bound<'event>> {
        &mut substitution.resources
    }
}

/// Compiled pattern for one statically selected component type.
pub(super) type CompiledPattern<'arena, ComponentType> =
    ComponentPattern<<ComponentType as Match<'arena>>::Compiled, DefaultSymbol>;

/// Concrete, structurally hashable atom representation stored in [`TestNode`](super::node::TestNode).
pub(super) type CompiledAtomPattern<'arena> = AtomPattern<
    <Principal as Match<'arena>>::Compiled,
    <Action as Match<'arena>>::Compiled,
    <Resource as Match<'arena>>::Compiled,
    DefaultSymbol,
>;
