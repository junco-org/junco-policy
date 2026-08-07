//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with both its arena-backed constant representation and
//! its borrowed candidate-binding representation. Each implementation also selects the matching
//! typed map in [`CandidateSubstitution`]. Principal matching therefore cannot accidentally produce
//! or retrieve a resource binding.

use std::collections::{HashMap, hash_map::Entry};
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use bumpalo::Bump;

use crate::model::{Action, Event, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern, PatternRepresentation};
use super::variable::VariableName;

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
pub(crate) struct CandidateSubstitution<'arena, 'event> {
    principals: HashMap<VariableName<'arena>, &'event Principal>,
    actions: HashMap<VariableName<'arena>, &'event Action>,
    resources: HashMap<VariableName<'arena>, &'event Resource>,
}

/// Structural application of a substitution to a pattern-like value.
pub(super) trait Subst<Substitution> {
    /// Variable-free value produced by successful substitution.
    type Concrete;

    /// Applies `substitution`, returning `None` when a referenced variable is unbound.
    fn subst(&self, substitution: &Substitution) -> Option<Self::Concrete>;
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

/// Compiled component pattern carrying its component domain in the type.
pub(super) struct CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    inner: ComponentPattern<ComponentType::Compiled, VariableName<'arena>>,
    component: PhantomData<fn() -> ComponentType>,
}

impl<'arena, ComponentType> CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    /// Wraps the structurally stored compiled pattern with its component-domain marker.
    pub(super) fn new(
        inner: ComponentPattern<ComponentType::Compiled, VariableName<'arena>>,
    ) -> Self {
        Self {
            inner,
            component: PhantomData,
        }
    }

    /// Returns the structural representation stored by compiled atom nodes.
    pub(super) fn into_inner(
        self,
    ) -> ComponentPattern<ComponentType::Compiled, VariableName<'arena>> {
        self.inner
    }
}

impl<'arena, ComponentType> Clone for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<'arena, ComponentType> Copy for CompiledComponentPattern<'arena, ComponentType> where
    ComponentType: ComponentDomain<'arena>
{
}

impl<'arena, ComponentType> fmt::Debug for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(formatter)
    }
}

impl<'arena, ComponentType> PartialEq for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<'arena, ComponentType> Eq for CompiledComponentPattern<'arena, ComponentType> where
    ComponentType: ComponentDomain<'arena>
{
}

impl<'arena, ComponentType> Hash for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    fn hash<HasherType: Hasher>(&self, state: &mut HasherType) {
        self.inner.hash(state);
    }
}

/// Returns whether two maps assign any common variable, regardless of value type.
fn variables_overlap<'arena, Left, Right>(
    left: &HashMap<VariableName<'arena>, Left>,
    right: &HashMap<VariableName<'arena>, Right>,
) -> bool {
    left.keys().any(|variable| right.contains_key(variable))
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

impl<'arena, 'event> CandidateSubstitution<'arena, 'event> {
    /// Returns whether no variable is assigned in more than one component domain.
    fn is_well_typed(&self) -> bool {
        !variables_overlap(&self.principals, &self.actions)
            && !variables_overlap(&self.principals, &self.resources)
            && !variables_overlap(&self.actions, &self.resources)
    }

    /// Combines two substitutions when overlapping assignments are equal and have the same domain.
    ///
    /// The method consumes both inputs. A failed merge cannot expose a partially combined value.
    pub(super) fn merge(mut self, other: Self) -> Option<Self> {
        let cross_domain_conflict = variables_overlap(&self.principals, &other.actions)
            || variables_overlap(&self.principals, &other.resources)
            || variables_overlap(&self.actions, &other.principals)
            || variables_overlap(&self.actions, &other.resources)
            || variables_overlap(&self.resources, &other.principals)
            || variables_overlap(&self.resources, &other.actions);
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
        substitution: &'substitution CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution HashMap<VariableName<'arena>, &'event Self>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, &'event Self>;
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
        substitution: &'substitution CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution HashMap<VariableName<'arena>, &'event Self> {
        &substitution.principals
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, &'event Self> {
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
        substitution: &'substitution CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution HashMap<VariableName<'arena>, &'event Self> {
        &substitution.actions
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, &'event Self> {
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
        substitution: &'substitution CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution HashMap<VariableName<'arena>, &'event Self> {
        &substitution.resources
    }

    fn bindings_mut<'substitution, 'event>(
        substitution: &'substitution mut CandidateSubstitution<'arena, 'event>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, &'event Self> {
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
    type Variable = VariableName<'arena>;
}

/// Compiled pattern for one statically selected component type.
pub(super) type CompiledPattern<'arena, ComponentType> =
    CompiledComponentPattern<'arena, ComponentType>;

/// Concrete, structurally hashable atom representation stored in [`TestNode`](super::node::TestNode).
pub(super) type CompiledAtomPattern<'arena> = AtomPattern<CompiledRepresentation<'arena>>;

/// Variable-free atom produced by applying a candidate substitution.
pub(super) enum ConcreteAtom<'arena, 'event> {
    Principal(AppliedPattern<'arena, 'event, Principal>),
    Action(AppliedPattern<'arena, 'event, Action>),
    Resource(AppliedPattern<'arena, 'event, Resource>),
}

impl PartialEq<Event> for ConcreteAtom<'_, '_> {
    fn eq(&self, event: &Event) -> bool {
        match self {
            Self::Principal(expected) => expected.eq(&event.principal),
            Self::Action(expected) => expected.eq(&event.action),
            Self::Resource(expected) => expected.eq(&event.resource),
        }
    }
}

impl<'arena, 'event, ComponentType> Subst<CandidateSubstitution<'arena, 'event>>
    for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena> + 'event,
{
    type Concrete = AppliedPattern<'arena, 'event, ComponentType>;

    fn subst(
        &self,
        substitution: &CandidateSubstitution<'arena, 'event>,
    ) -> Option<Self::Concrete> {
        match self.inner {
            ComponentPattern::Constant(expected) => Some(AppliedPattern::Constant(expected)),
            ComponentPattern::Variable(variable) => ComponentType::bindings(substitution)
                .get(&variable)
                .copied()
                .map(AppliedPattern::Bound),
        }
    }
}

impl<'arena, 'event> Subst<CandidateSubstitution<'arena, 'event>> for CompiledAtomPattern<'arena> {
    type Concrete = ConcreteAtom<'arena, 'event>;

    fn subst(
        &self,
        substitution: &CandidateSubstitution<'arena, 'event>,
    ) -> Option<Self::Concrete> {
        match self {
            AtomPattern::Principal(pattern) => CompiledComponentPattern::<Principal>::new(*pattern)
                .subst(substitution)
                .map(ConcreteAtom::Principal),
            AtomPattern::Action(pattern) => CompiledComponentPattern::<Action>::new(*pattern)
                .subst(substitution)
                .map(ConcreteAtom::Action),
            AtomPattern::Resource(pattern) => CompiledComponentPattern::<Resource>::new(*pattern)
                .subst(substitution)
                .map(ConcreteAtom::Resource),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn merge_accepts_disjoint_and_equal_assignments() {
        let actor = VariableName::new("actor");
        let operation = VariableName::new("operation");
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
        let actor = VariableName::new("actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, &alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, &bob);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn merge_rejects_one_variable_in_different_domains() {
        let value = VariableName::new("value");
        let alice = Principal::new("alice");
        let read = Action::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(value, &alice);
        let mut right = CandidateSubstitution::default();
        right.actions.insert(value, &read);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn subst_resolves_components_and_atoms() {
        let actor = VariableName::new("actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let mut substitution = CandidateSubstitution::default();
        substitution.principals.insert(actor, &alice);

        let constant =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Constant("alice"))
                .subst(&substitution)
                .expect("constants always substitute");
        assert!(constant.eq(&alice));
        assert!(!constant.eq(&bob));

        let variable =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Variable(actor))
                .subst(&substitution)
                .expect("the candidate bound actor");
        assert!(variable.eq(&alice));
        assert!(!variable.eq(&bob));

        let atom: CompiledAtomPattern<'_> =
            AtomPattern::Principal(ComponentPattern::Variable(actor));
        let event = Event::new("alice", Action::Read, ["a"]);
        assert!(
            atom.subst(&substitution)
                .is_some_and(|concrete| concrete.eq(&event))
        );
    }
}
