//! Component-specific compilation and matching behind one associated-type trait.
//!
//! [`Match`] associates each model component with its arena-backed representation. Generic head
//! and atom evaluators therefore do not need separate constant/actual type parameters, an erased
//! value argument, and a comparison closure. The trait is statically dispatched: principal,
//! action, and resource matching remain inlineable and introduce no trait-object indirection.

use std::fmt::Debug;
use std::hash::Hash;

use bumpalo::Bump;
use string_interner::DefaultSymbol;

use crate::model::{Action, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern};

/// Arena-backed action value used by compiled patterns.
///
/// Only commit messages need arena storage; all other variants are fieldless and copied directly.
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

/// Type-tagged reference bound by a head variable.
///
/// The variants keep the three component domains disjoint. Reusing one variable name in different
/// component positions is therefore a mismatch rather than a comparison of rendered values.
#[derive(Clone, Copy, Debug)]
pub(super) enum BoundValue<'event> {
    Principal(&'event Principal),
    Action(&'event Action),
    Resource(&'event Resource),
}

impl BoundValue<'_> {
    /// Compares values only when both bindings belong to the same component domain.
    pub(super) fn equals(self, other: Self) -> bool {
        match (self, other) {
            (Self::Principal(left), Self::Principal(right)) => left == right,
            (Self::Action(left), Self::Action(right)) => left == right,
            (Self::Resource(left), Self::Resource(right)) => left == right,
            _ => false,
        }
    }
}

/// Compiles and matches one capability-product component.
///
/// `Compiled` must support structural hashing because compiled atom patterns are payloads of
/// hashconsed test nodes. Implementations are static; this trait is intentionally not used as a
/// trait object inside the canonical syntax DAG.
pub(super) trait Match<'arena>: Sized {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Immutable arena-backed representation embedded in compiled patterns.
    type Compiled: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Copies `value` into the validator arena when ownership or stable borrowing requires it.
    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled;

    /// Compares one compiled constant with an event component.
    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool;

    /// Erases an event component into a tagged variable binding.
    fn bound<'event>(actual: &'event Self) -> BoundValue<'event>;
}

impl<'arena> Match<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = &'arena str;

    fn compile(arena: &'arena Bump, value: &Self) -> Self::Compiled {
        arena.alloc_str(value.as_str())
    }

    fn constant_matches(expected: Self::Compiled, actual: &Self) -> bool {
        actual.as_str() == expected
    }

    fn bound<'event>(actual: &'event Self) -> BoundValue<'event> {
        BoundValue::Principal(actual)
    }
}

impl<'arena> Match<'arena> for Action {
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

    fn bound<'event>(actual: &'event Self) -> BoundValue<'event> {
        BoundValue::Action(actual)
    }
}

impl<'arena> Match<'arena> for Resource {
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

    fn bound<'event>(actual: &'event Self) -> BoundValue<'event> {
        BoundValue::Resource(actual)
    }
}

/// Compiled pattern for one statically selected component type.
pub(super) type CompiledPattern<'arena, ComponentType> =
    ComponentPattern<<ComponentType as Match<'arena>>::Compiled, DefaultSymbol>;

/// Concrete, structurally hashable atom representation stored in [`TestNode`](super::node::TestNode).
///
/// Keeping this as an enum rather than `dyn Pattern` is what lets hashconsing use derived equality
/// and hashing without pointer-identity or virtual structural-comparison machinery.
pub(super) type CompiledAtomPattern<'arena> = AtomPattern<
    <Principal as Match<'arena>>::Compiled,
    <Action as Match<'arena>>::Compiled,
    <Resource as Match<'arena>>::Compiled,
    DefaultSymbol,
>;
