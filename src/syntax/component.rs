//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with one canonical arena-backed
//! representation used by both policy constants and candidate bindings. Each implementation also
//! selects its typed map in [`CandidateSubstitution`], so domains cannot be mixed.

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet, hash_map::Entry};
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

/// Arena-backed resource segments shared by constants and candidate bindings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct CompiledResource<'arena>(&'arena [&'arena str]);

impl<'arena> Borrow<[&'arena str]> for CompiledResource<'arena> {
    fn borrow(&self) -> &[&'arena str] {
        self.0
    }
}

/// Monotonic interner for component values used by compiled constants and runtime substitutions.
///
/// Values from denied as well as granted candidates remain until the validator arena is dropped.
/// This intentionally trades input-cardinality-dependent memory retention for one uniform,
/// zero-copy representation during substitution and comparison.
pub(super) struct ComponentValues<'arena> {
    arena: &'arena Bump,
    strings: HashSet<&'arena str>,
    resources: HashSet<CompiledResource<'arena>>,
}

impl<'arena> ComponentValues<'arena> {
    /// Creates empty value pools backed by `arena`.
    pub(super) fn new(arena: &'arena Bump) -> Self {
        Self {
            arena,
            strings: HashSet::with_capacity(128),
            resources: HashSet::with_capacity(64),
        }
    }

    /// Interns one string by content.
    pub(super) fn intern_string(&mut self, value: &str) -> &'arena str {
        if let Some(&interned) = self.strings.get(value) {
            return interned;
        }
        let interned = self.arena.alloc_str(value) as &str;
        self.strings.insert(interned);
        interned
    }

    /// Interns one structurally compared resource after interning every segment.
    pub(super) fn intern_resource(&mut self, value: &Resource) -> CompiledResource<'arena> {
        let segments: Vec<&'arena str> = value
            .segments()
            .iter()
            .map(|segment| self.intern_string(segment))
            .collect();
        if let Some(&interned) = self.resources.get(segments.as_slice()) {
            return interned;
        }
        let interned = CompiledResource(self.arena.alloc_slice_copy(&segments));
        self.resources.insert(interned);
        interned
    }

    /// Number of distinct interned strings, used to verify value reuse.
    #[cfg(test)]
    pub(super) fn string_count(&self) -> usize {
        self.strings.len()
    }
}

/// Interned candidate values assigned to head variables during one rule evaluation.
///
/// Every map stores the same compiled representation used by constant patterns.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'arena> {
    principals: HashMap<VariableName<'arena>, <Principal as ComponentDomain<'arena>>::Compiled>,
    actions: HashMap<VariableName<'arena>, <Action as ComponentDomain<'arena>>::Compiled>,
    resources: HashMap<VariableName<'arena>, <Resource as ComponentDomain<'arena>>::Compiled>,
}

/// Structural application of a substitution to a pattern-like value.
pub(super) trait Subst<Substitution> {
    /// Variable-free value produced by successful substitution.
    type Concrete;

    /// Applies `substitution`, returning `None` when a referenced variable is unbound.
    fn subst(&self, substitution: &Substitution) -> Option<Self::Concrete>;
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

impl<'arena> CandidateSubstitution<'arena> {
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

/// Compiles, interns, and compares one capability-product component domain.
pub(super) trait ComponentDomain<'arena>: Sized + Eq {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Canonical arena-backed representation used by constants and substitutions.
    type Compiled: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Interns `value` into the validator's monotonic component-value store.
    fn intern(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled;

    /// Compares one canonical compiled value with a model value.
    fn compiled_matches(expected: Self::Compiled, actual: &Self) -> bool;

    /// Returns the immutable substitution map belonging to this component.
    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableName<'arena>, Self::Compiled>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, Self::Compiled>;
}

impl<'arena> ComponentDomain<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = &'arena str;

    fn intern(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
        values.intern_string(value.as_str())
    }

    fn compiled_matches(expected: Self::Compiled, actual: &Self) -> bool {
        actual.as_str() == expected
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableName<'arena>, Self::Compiled> {
        &substitution.principals
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, Self::Compiled> {
        &mut substitution.principals
    }
}

impl<'arena> ComponentDomain<'arena> for Action {
    const COMPONENT: Component = Component::Action;
    type Compiled = CompiledAction<'arena>;

    fn intern(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
        match value {
            Action::Read => CompiledAction::Read,
            Action::Edit => CompiledAction::Edit,
            Action::Stage => CompiledAction::Stage,
            Action::Unstage => CompiledAction::Unstage,
            Action::Commit { message } => CompiledAction::Commit(
                message
                    .as_deref()
                    .map(|message| values.intern_string(message)),
            ),
            Action::Checkout => CompiledAction::Checkout,
            Action::Stash => CompiledAction::Stash,
            Action::Diff => CompiledAction::Diff,
            Action::History => CompiledAction::History,
        }
    }

    fn compiled_matches(expected: Self::Compiled, actual: &Self) -> bool {
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

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableName<'arena>, Self::Compiled> {
        &substitution.actions
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, Self::Compiled> {
        &mut substitution.actions
    }
}

impl<'arena> ComponentDomain<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Compiled = CompiledResource<'arena>;

    fn intern(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
        values.intern_resource(value)
    }

    fn compiled_matches(expected: Self::Compiled, actual: &Self) -> bool {
        expected.0.len() == actual.segments().len()
            && expected
                .0
                .iter()
                .zip(actual.segments())
                .all(|(left, right)| *left == right)
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableName<'arena>, Self::Compiled> {
        &substitution.resources
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableName<'arena>, Self::Compiled> {
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

/// Variable-free atom whose values use the same canonical representation as compiled constants.
pub(super) enum ConcreteAtom<'arena> {
    Principal(<Principal as ComponentDomain<'arena>>::Compiled),
    Action(<Action as ComponentDomain<'arena>>::Compiled),
    Resource(<Resource as ComponentDomain<'arena>>::Compiled),
}

impl PartialEq<Event> for ConcreteAtom<'_> {
    fn eq(&self, event: &Event) -> bool {
        match self {
            Self::Principal(expected) => Principal::compiled_matches(*expected, &event.principal),
            Self::Action(expected) => Action::compiled_matches(*expected, &event.action),
            Self::Resource(expected) => Resource::compiled_matches(*expected, &event.resource),
        }
    }
}

impl<'arena, ComponentType> Subst<CandidateSubstitution<'arena>>
    for CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    type Concrete = ComponentType::Compiled;

    fn subst(&self, substitution: &CandidateSubstitution<'arena>) -> Option<Self::Concrete> {
        match self.inner {
            ComponentPattern::Constant(expected) => Some(expected),
            ComponentPattern::Variable(variable) => ComponentType::bindings(substitution)
                .get(&variable)
                .copied(),
        }
    }
}

impl<'arena> Subst<CandidateSubstitution<'arena>> for CompiledAtomPattern<'arena> {
    type Concrete = ConcreteAtom<'arena>;

    fn subst(&self, substitution: &CandidateSubstitution<'arena>) -> Option<Self::Concrete> {
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
    fn component_values_intern_constants_and_candidates_uniformly() {
        let arena = Bump::new();
        let mut values = ComponentValues::new(&arena);

        let constant_principal = Principal::intern(&mut values, &Principal::new("alice"));
        let candidate_principal = Principal::intern(&mut values, &Principal::new("alice"));
        assert!(std::ptr::eq(constant_principal, candidate_principal));

        let constant_resource = Resource::intern(&mut values, &Resource::new(["src", "a.rs"]));
        let candidate_resource = Resource::intern(&mut values, &Resource::new(["src", "a.rs"]));
        assert_eq!(constant_resource, candidate_resource);
        assert!(std::ptr::eq(constant_resource.0, candidate_resource.0));

        let constant_action = Action::intern(&mut values, &Action::commit("ship"));
        let candidate_action = Action::intern(&mut values, &Action::commit("ship"));
        assert_eq!(constant_action, candidate_action);
        let (
            CompiledAction::Commit(Some(constant_message)),
            CompiledAction::Commit(Some(candidate_message)),
        ) = (constant_action, candidate_action)
        else {
            panic!("commit action was not compiled as a commit")
        };
        assert!(std::ptr::eq(constant_message, candidate_message));
    }

    #[test]
    fn merge_accepts_disjoint_and_equal_assignments() {
        let actor = VariableName::new("actor");
        let operation = VariableName::new("operation");
        let alice = "alice";
        let same_alice = "alice";
        let read = CompiledAction::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, same_alice);
        right.actions.insert(operation, read);

        let merged = left.merge(right).expect("assignments are compatible");
        assert_eq!(merged.principals.get(&actor), Some(&alice));
        assert_eq!(merged.actions.get(&operation), Some(&read));
    }

    #[test]
    fn merge_rejects_unequal_assignments_in_one_domain() {
        let actor = VariableName::new("actor");
        let alice = "alice";
        let bob = "bob";

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, bob);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn merge_rejects_one_variable_in_different_domains() {
        let value = VariableName::new("value");
        let alice = "alice";
        let read = CompiledAction::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(value, alice);
        let mut right = CandidateSubstitution::default();
        right.actions.insert(value, read);

        assert!(left.merge(right).is_none());
    }

    #[test]
    fn subst_resolves_components_and_atoms() {
        let actor = VariableName::new("actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let mut substitution = CandidateSubstitution::default();
        substitution.principals.insert(actor, "alice");

        let constant =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Constant("alice"))
                .subst(&substitution)
                .expect("constants always substitute");
        assert!(Principal::compiled_matches(constant, &alice));
        assert!(!Principal::compiled_matches(constant, &bob));

        let variable =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Variable(actor))
                .subst(&substitution)
                .expect("the candidate bound actor");
        assert!(Principal::compiled_matches(variable, &alice));
        assert!(!Principal::compiled_matches(variable, &bob));

        let atom: CompiledAtomPattern<'_> =
            AtomPattern::Principal(ComponentPattern::Variable(actor));
        let event = Event::new("alice", Action::Read, ["a"]);
        assert!(
            atom.subst(&substitution)
                .is_some_and(|concrete| concrete.eq(&event))
        );
    }
}
