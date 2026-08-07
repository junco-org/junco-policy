//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with both its arena-backed constant representation and
//! its borrowed candidate-binding representation. Each implementation also selects the matching
//! typed map in [`CandidateSubstitution`]. Principal matching therefore cannot accidentally produce
//! or retrieve a resource binding.

use std::collections::{HashMap, hash_map::Entry};
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

/// Result of applying a candidate substitution to one compiled component pattern.
///
/// Constants retain their arena-backed representation; variables resolve to a borrowed candidate
/// component. `PartialEq<ComponentType>` hides that representation distinction from evaluation.
pub(super) enum AppliedPattern<'arena, 'event, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    Constant(ComponentType::Compiled),
    Bound(&'event ComponentType),
}

impl<'arena, 'event, ComponentType> PartialEq<ComponentType>
    for AppliedPattern<'arena, 'event, ComponentType>
where
    ComponentType: ComponentDomain<'arena> + 'event,
{
    fn eq(&self, actual: &ComponentType) -> bool {
        match self {
            Self::Constant(expected) => ComponentType::constant_matches(*expected, actual),
            Self::Bound(expected) => *expected == actual,
        }
    }
}

impl<'event> CandidateSubstitution<'event> {
    /// Applies this substitution to a constant-or-variable compiled component pattern.
    pub(super) fn apply<'arena, ComponentType>(
        &self,
        pattern: CompiledPattern<'arena, ComponentType>,
    ) -> Option<AppliedPattern<'arena, 'event, ComponentType>>
    where
        ComponentType: ComponentDomain<'arena> + 'event,
    {
        match pattern {
            ComponentPattern::Constant(expected) => Some(AppliedPattern::Constant(expected)),
            ComponentPattern::Variable(symbol) => ComponentType::bindings(self)
                .get(&symbol)
                .copied()
                .map(AppliedPattern::Bound),
        }
    }
}

/// Returns whether two maps assign any common variable symbol, regardless of value type.
fn symbols_overlap<Left, Right>(
    left: &HashMap<DefaultSymbol, Left>,
    right: &HashMap<DefaultSymbol, Right>,
) -> bool {
    left.keys().any(|symbol| right.contains_key(symbol))
}

/// Extends `target` with `source` when common keys have equal values.
fn merge_map<Key, Value>(target: &mut HashMap<Key, Value>, source: HashMap<Key, Value>) -> bool
where
    Key: Eq + Hash,
    Value: Eq,
{
    if target.is_empty() {
        *target = source;
        return true;
    }
    for (key, value) in source {
        match target.entry(key) {
            Entry::Vacant(entry) => {
                entry.insert(value);
            }
            Entry::Occupied(entry) if entry.get() == &value => {}
            Entry::Occupied(_) => return false,
        }
    }
    true
}

impl<'event> CandidateSubstitution<'event> {
    /// Returns whether no symbol is assigned in more than one component domain.
    fn is_well_typed(&self) -> bool {
        !symbols_overlap(&self.principals, &self.actions)
            && !symbols_overlap(&self.principals, &self.resources)
            && !symbols_overlap(&self.actions, &self.resources)
    }

    /// Combines two substitutions when overlapping assignments are equal and have the same domain.
    ///
    /// The method consumes both inputs. A failed merge cannot expose a partially combined value.
    pub(super) fn merge(mut self, other: Self) -> Option<Self> {
        let cross_domain_conflict = symbols_overlap(&self.principals, &other.actions)
            || symbols_overlap(&self.principals, &other.resources)
            || symbols_overlap(&self.actions, &other.principals)
            || symbols_overlap(&self.actions, &other.resources)
            || symbols_overlap(&self.resources, &other.principals)
            || symbols_overlap(&self.resources, &other.actions);
        if !self.is_well_typed() || !other.is_well_typed() || cross_domain_conflict {
            return None;
        }

        let Self {
            principals,
            actions,
            resources,
        } = other;
        if !merge_map(&mut self.principals, principals)
            || !merge_map(&mut self.actions, actions)
            || !merge_map(&mut self.resources, resources)
        {
            return None;
        }
        Some(self)
    }
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

#[cfg(test)]
mod tests {
    use string_interner::DefaultStringInterner;

    use super::*;

    #[test]
    fn merge_accepts_disjoint_and_equal_assignments() {
        let mut symbols = DefaultStringInterner::default();
        let actor = symbols.get_or_intern("actor");
        let operation = symbols.get_or_intern("operation");
        let alice = Principal::new("alice");
        let same_alice = Principal::new("alice");
        let read = Action::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, &alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, &same_alice);
        right.actions.insert(operation, &read);

        let merged = left.merge(right).expect("assignments are compatible");
        assert_eq!(merged.principals.get(&actor), Some(&&alice));
        assert_eq!(merged.actions.get(&operation), Some(&&read));
    }

    #[test]
    fn merge_rejects_unequal_assignments_in_one_domain() {
        let mut symbols = DefaultStringInterner::default();
        let actor = symbols.get_or_intern("actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, &alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, &bob);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn merge_rejects_one_symbol_in_different_domains() {
        let mut symbols = DefaultStringInterner::default();
        let value = symbols.get_or_intern("value");
        let alice = Principal::new("alice");
        let read = Action::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(value, &alice);
        let mut right = CandidateSubstitution::default();
        right.actions.insert(value, &read);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn apply_resolves_constants_and_variables() {
        let mut symbols = DefaultStringInterner::default();
        let actor = symbols.get_or_intern("actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let mut substitution = CandidateSubstitution::default();
        substitution.principals.insert(actor, &alice);

        let constant = substitution
            .apply::<Principal>(ComponentPattern::Constant("alice"))
            .expect("constants always apply");
        assert!(constant.eq(&alice));
        assert!(!constant.eq(&bob));

        let variable = substitution
            .apply::<Principal>(ComponentPattern::Variable(actor))
            .expect("the candidate bound actor");
        assert!(variable.eq(&alice));
        assert!(!variable.eq(&bob));
    }
}
