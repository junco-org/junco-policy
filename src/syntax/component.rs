//! Typed component values, compiled patterns, and candidate substitution storage.
//!
//! Event components are the caller's compact `Copy` values and are compared directly. Only source
//! variable names are interned; constants and candidate bindings are copied into compiled syntax
//! and substitutions without allocation. [`ResolvedValue`] tags every value with its product
//! coordinate, so principal and resource values stay distinct even when they share a Rust type.

use smallvec::{SmallVec, smallvec};
use string_interner::{DefaultSymbol, Symbol};

use crate::model::Event;

use super::source::{Component, ComponentPattern};

/// Event component value tagged with its product coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ResolvedValue<E: Event> {
    Principal(E::Principal),
    Action(E::Action),
    Resource(E::Resource),
}

impl<E: Event> ResolvedValue<E> {
    /// Product coordinate occupied by this value.
    fn component(&self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }

    /// Compares this value with the same coordinate projected from `event`.
    pub(super) fn matches(&self, event: &E) -> bool {
        match *self {
            Self::Principal(expected) => expected == event.principal(),
            Self::Action(expected) => expected == event.action(),
            Self::Resource(expected) => expected == event.resource(),
        }
    }
}

/// Candidate values assigned to variables during one rule evaluation.
///
/// Entries are sorted by [`Symbol::to_usize`] and hold each variable at most once, so equal
/// binding sets have one representation usable directly as a cache key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CandidateSubstitution<E: Event> {
    values: SmallVec<[(DefaultSymbol, ResolvedValue<E>); 3]>,
}

impl<E: Event> Default for CandidateSubstitution<E> {
    fn default() -> Self {
        Self {
            values: SmallVec::new(),
        }
    }
}

impl<E: Event> CandidateSubstitution<E> {
    /// Creates one partial substitution assignment.
    pub(super) fn singleton(variable: DefaultSymbol, value: ResolvedValue<E>) -> Self {
        Self {
            values: smallvec![(variable, value)],
        }
    }

    /// Returns a new compatible union without modifying either input substitution.
    ///
    /// A variable bound to different values, including values of different coordinates, conflicts.
    pub(super) fn merge(&self, other: &Self) -> Option<Self> {
        let mut values = self.values.clone();
        for &(variable, value) in &other.values {
            match values.binary_search_by_key(&variable.to_usize(), |(bound, _)| bound.to_usize()) {
                Ok(index) if values[index].1 != value => return None,
                Ok(_) => {}
                Err(index) => values.insert(index, (variable, value)),
            }
        }
        Some(Self { values })
    }

    /// Returns the value bound to `variable` when it occupies `component`.
    fn get(&self, variable: DefaultSymbol, component: Component) -> Option<ResolvedValue<E>> {
        self.values
            .iter()
            .find(|(bound, _)| *bound == variable)
            .map(|(_, value)| *value)
            .filter(|value| value.component() == component)
    }
}

/// Compiled pattern over one component type with interned variable names.
pub(super) type CompiledPattern<T> = ComponentPattern<T, DefaultSymbol>;

/// Compiled, structurally hashable atom pattern stored in [`TestNode`](super::node::TestNode).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum CompiledAtomPattern<E: Event> {
    Principal(CompiledPattern<E::Principal>),
    Action(CompiledPattern<E::Action>),
    Resource(CompiledPattern<E::Resource>),
}

impl<E: Event> CompiledAtomPattern<E> {
    /// Applies candidate bindings and returns the variable-free tagged value.
    pub(super) fn subst(
        &self,
        substitution: &CandidateSubstitution<E>,
    ) -> Option<ResolvedValue<E>> {
        match *self {
            Self::Principal(ComponentPattern::Constant(value)) => {
                Some(ResolvedValue::Principal(value))
            }
            Self::Action(ComponentPattern::Constant(value)) => Some(ResolvedValue::Action(value)),
            Self::Resource(ComponentPattern::Constant(value)) => {
                Some(ResolvedValue::Resource(value))
            }
            Self::Principal(ComponentPattern::Variable(variable)) => {
                substitution.get(variable, Component::Principal)
            }
            Self::Action(ComponentPattern::Variable(variable)) => {
                substitution.get(variable, Component::Action)
            }
            Self::Resource(ComponentPattern::Variable(variable)) => {
                substitution.get(variable, Component::Resource)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Action, GitEvent, git_event};
    use string_interner::DefaultStringInterner;

    /// Deliberately shared principal and resource type: coordinate tags alone must separate them.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Id(u32);

    fn principal(id: u32) -> ResolvedValue<GitEvent<Id, Id>> {
        ResolvedValue::Principal(Id(id))
    }

    #[test]
    fn merge_combines_partial_head_substitutions() {
        let mut variables = <DefaultStringInterner>::with_capacity(128);
        let actor = variables.get_or_intern("actor");
        let operation = variables.get_or_intern("operation");
        let read = ResolvedValue::Action(Action::Read);

        let left = CandidateSubstitution::singleton(actor, principal(1));
        let right = CandidateSubstitution::singleton(operation, read)
            .merge(&CandidateSubstitution::singleton(actor, principal(1)))
            .expect("distinct variables agree");

        let merged = left.merge(&right).expect("bindings agree");
        assert_eq!(merged.get(actor, Component::Principal), Some(principal(1)));
        assert_eq!(merged.get(operation, Component::Action), Some(read));
        assert_eq!(left.get(operation, Component::Action), None);
        assert_eq!(right.get(operation, Component::Action), Some(read));
        assert_eq!(merged, right.merge(&left).expect("bindings agree"));
        assert_eq!(merged, right, "agreeing duplicates are stored once");
    }

    #[test]
    fn merge_rejects_conflicting_same_domain_bindings() {
        let mut variables = <DefaultStringInterner>::with_capacity(128);
        let actor = variables.get_or_intern("actor");
        let left = CandidateSubstitution::singleton(actor, principal(1));
        let right = CandidateSubstitution::singleton(actor, principal(2));

        assert!(left.merge(&right).is_none());
        assert_eq!(left.get(actor, Component::Principal), Some(principal(1)));
    }

    #[test]
    fn merge_rejects_cross_domain_bindings_with_equal_scalars() {
        let mut variables = <DefaultStringInterner>::with_capacity(128);
        let value = variables.get_or_intern("value");
        let left = CandidateSubstitution::singleton(value, principal(1));
        let right = CandidateSubstitution::singleton(value, ResolvedValue::Resource(Id(1)));

        assert!(left.merge(&right).is_none());
    }

    #[test]
    fn subst_resolves_typed_values_and_matches_their_coordinate() {
        let mut variables = <DefaultStringInterner>::with_capacity(128);
        let actor = variables.get_or_intern("actor");
        let substitution = CandidateSubstitution::singleton(actor, principal(1));
        let event = git_event(Id(1), Action::Read, Id(2));

        let constant: CompiledAtomPattern<GitEvent<Id, Id>> =
            CompiledAtomPattern::Principal(ComponentPattern::Constant(Id(1)));
        assert_eq!(constant.subst(&substitution), Some(principal(1)));
        let variable: CompiledAtomPattern<GitEvent<Id, Id>> =
            CompiledAtomPattern::Principal(ComponentPattern::Variable(actor));
        let bound = variable
            .subst(&substitution)
            .expect("the candidate bound actor");
        assert_eq!(bound, principal(1));
        assert!(bound.matches(&event));

        let cross_domain: CompiledAtomPattern<GitEvent<Id, Id>> =
            CompiledAtomPattern::Resource(ComponentPattern::Variable(actor));
        assert_eq!(cross_domain.subst(&substitution), None);

        assert!(!ResolvedValue::Resource(Id(1)).matches(&event));
        assert!(ResolvedValue::Resource(Id(2)).matches(&event));
        assert!(!principal(2).matches(&event));
        assert!(ResolvedValue::Action(Action::Read).matches(&event));
        assert!(!ResolvedValue::Action(Action::Edit).matches(&event));
    }
}
