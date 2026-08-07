//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with one canonical arena-backed
//! representation used by both policy constants and candidate bindings. Each implementation also
//! selects its typed map in [`CandidateSubstitution`], so domains cannot be mixed.

use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use bumpalo::Bump;
use string_interner::{DefaultStringInterner, DefaultSymbol};

use crate::model::{Action, Event, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern, PatternRepresentation};
use super::variable::VariableSymbol;

/// Canonical action representation using string-interner symbols for commit messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum CompiledAction {
    Read,
    Edit,
    Stage,
    Unstage,
    Commit(Option<DefaultSymbol>),
    Checkout,
    Stash,
    Diff,
    History,
}

/// Arena-backed sequence of interned resource-segment symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct CompiledResource<'arena>(&'arena [DefaultSymbol]);

/// Black-box string interner and arena allocation for compiled compound values.
///
/// The `string-interner` crate owns all string deduplication and symbol validity. Resource
/// sequences are copied directly into the arena; they are structurally comparable but not interned
/// as complete sequences.
pub(super) struct ComponentValues<'arena> {
    arena: &'arena Bump,
    strings: DefaultStringInterner,
}

impl<'arena> ComponentValues<'arena> {
    /// Creates a string interner and compound-value allocator backed by `arena`.
    pub(super) fn new(arena: &'arena Bump) -> Self {
        Self {
            arena,
            strings: DefaultStringInterner::with_capacity(128),
        }
    }

    /// Interns one string through the black-box string interner.
    pub(super) fn intern_string(&mut self, value: &str) -> DefaultSymbol {
        self.strings.get_or_intern(value)
    }

    /// Resolves one valid symbol through the black-box string interner.
    pub(super) fn resolve_string(&self, symbol: DefaultSymbol) -> &str {
        self.strings
            .resolve(symbol)
            .expect("component symbols originate from this interner")
    }

    /// Compiles one ordered resource sequence after interning every segment string.
    pub(super) fn compile_resource(&mut self, value: &Resource) -> CompiledResource<'arena> {
        let segments: Vec<DefaultSymbol> = value
            .segments()
            .iter()
            .map(|segment| self.intern_string(segment))
            .collect();
        CompiledResource(self.arena.alloc_slice_copy(&segments))
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
    principals: HashMap<VariableSymbol, <Principal as ComponentDomain<'arena>>::Compiled>,
    actions: HashMap<VariableSymbol, <Action as ComponentDomain<'arena>>::Compiled>,
    resources: HashMap<VariableSymbol, <Resource as ComponentDomain<'arena>>::Compiled>,
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
    inner: ComponentPattern<ComponentType::Compiled, VariableSymbol>,
    component: PhantomData<fn() -> ComponentType>,
}

impl<'arena, ComponentType> CompiledComponentPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    /// Wraps the structurally stored compiled pattern with its component-domain marker.
    pub(super) fn new(inner: ComponentPattern<ComponentType::Compiled, VariableSymbol>) -> Self {
        Self {
            inner,
            component: PhantomData,
        }
    }

    /// Returns the structural representation stored by compiled atom nodes.
    pub(super) fn into_inner(self) -> ComponentPattern<ComponentType::Compiled, VariableSymbol> {
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

impl<'arena> CandidateSubstitution<'arena> {
    /// Combines partial substitutions produced by distinct, statically typed head coordinates.
    ///
    /// `VariableEnvironment` has already rejected cross-domain variable reuse, and a head has only
    /// one coordinate per domain, so compatibility is guaranteed for every compiled head.
    pub(super) fn merge(mut self, other: Self) -> Self {
        self.principals.extend(other.principals);
        self.actions.extend(other.actions);
        self.resources.extend(other.resources);
        self
    }
}

/// Compiles, interns, and compares one capability-product component domain.
pub(super) trait ComponentDomain<'arena>: Sized + Eq {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Canonical arena-backed representation used by constants and substitutions.
    type Compiled: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Compiles `value` into the representation shared by constants and substitutions.
    fn compile(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled;

    /// Compares one canonical compiled value with a model value through the value store.
    fn compiled_matches(
        values: &ComponentValues<'arena>,
        expected: Self::Compiled,
        actual: &Self,
    ) -> bool;

    /// Returns the immutable substitution map belonging to this component.
    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableSymbol, Self::Compiled>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableSymbol, Self::Compiled>;
}

impl<'arena> ComponentDomain<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = DefaultSymbol;

    fn compile(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
        values.intern_string(value.as_str())
    }

    fn compiled_matches(
        values: &ComponentValues<'arena>,
        expected: Self::Compiled,
        actual: &Self,
    ) -> bool {
        values.resolve_string(expected) == actual.as_str()
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableSymbol, Self::Compiled> {
        &substitution.principals
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableSymbol, Self::Compiled> {
        &mut substitution.principals
    }
}

impl<'arena> ComponentDomain<'arena> for Action {
    const COMPONENT: Component = Component::Action;
    type Compiled = CompiledAction;

    fn compile(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
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

    fn compiled_matches(
        values: &ComponentValues<'arena>,
        expected: Self::Compiled,
        actual: &Self,
    ) -> bool {
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
                expected.map(|symbol| values.resolve_string(symbol)) == message.as_deref()
            }
            _ => false,
        }
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableSymbol, Self::Compiled> {
        &substitution.actions
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableSymbol, Self::Compiled> {
        &mut substitution.actions
    }
}

impl<'arena> ComponentDomain<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Compiled = CompiledResource<'arena>;

    fn compile(values: &mut ComponentValues<'arena>, value: &Self) -> Self::Compiled {
        values.compile_resource(value)
    }

    fn compiled_matches(
        values: &ComponentValues<'arena>,
        expected: Self::Compiled,
        actual: &Self,
    ) -> bool {
        expected.0.len() == actual.segments().len()
            && expected
                .0
                .iter()
                .zip(actual.segments())
                .all(|(left, right)| values.resolve_string(*left) == right)
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<VariableSymbol, Self::Compiled> {
        &substitution.resources
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<VariableSymbol, Self::Compiled> {
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
    type Variable = VariableSymbol;
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

impl<'arena> ConcreteAtom<'arena> {
    /// Compares this canonical atom with a model event through the string interner.
    pub(super) fn matches(&self, values: &ComponentValues<'arena>, event: &Event) -> bool {
        match self {
            Self::Principal(expected) => {
                Principal::compiled_matches(values, *expected, &event.principal)
            }
            Self::Action(expected) => Action::compiled_matches(values, *expected, &event.action),
            Self::Resource(expected) => {
                Resource::compiled_matches(values, *expected, &event.resource)
            }
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

    fn variable(values: &mut ComponentValues<'_>, name: &str) -> VariableSymbol {
        VariableSymbol::new(values.intern_string(name))
    }

    #[test]
    fn component_values_compile_constants_and_candidates_uniformly() {
        let arena = Bump::new();
        let mut values = ComponentValues::new(&arena);

        let constant_principal = Principal::compile(&mut values, &Principal::new("alice"));
        let candidate_principal = Principal::compile(&mut values, &Principal::new("alice"));
        assert_eq!(constant_principal, candidate_principal);
        assert_eq!(values.resolve_string(constant_principal), "alice");

        let constant_resource = Resource::compile(&mut values, &Resource::new(["src", "a.rs"]));
        let candidate_resource = Resource::compile(&mut values, &Resource::new(["src", "a.rs"]));
        assert_eq!(constant_resource, candidate_resource);

        let constant_action = Action::compile(&mut values, &Action::commit("ship"));
        let candidate_action = Action::compile(&mut values, &Action::commit("ship"));
        assert_eq!(constant_action, candidate_action);
    }

    #[test]
    fn merge_combines_partial_head_substitutions() {
        let arena = Bump::new();
        let mut values = ComponentValues::new(&arena);
        let actor = variable(&mut values, "actor");
        let operation = variable(&mut values, "operation");
        let alice = values.intern_string("alice");
        let same_alice = values.intern_string("alice");
        let read = CompiledAction::Read;

        let mut left = CandidateSubstitution::default();
        left.principals.insert(actor, alice);
        let mut right = CandidateSubstitution::default();
        right.principals.insert(actor, same_alice);
        right.actions.insert(operation, read);

        let merged = left.merge(right);
        assert_eq!(merged.principals.get(&actor), Some(&alice));
        assert_eq!(merged.actions.get(&operation), Some(&read));
    }

    #[test]
    fn subst_resolves_components_and_atoms() {
        let arena = Bump::new();
        let mut values = ComponentValues::new(&arena);
        let actor = variable(&mut values, "actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let alice_symbol = values.intern_string("alice");
        let mut substitution = CandidateSubstitution::default();
        substitution.principals.insert(actor, alice_symbol);

        let constant =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Constant(alice_symbol))
                .subst(&substitution)
                .expect("constants always substitute");
        assert!(Principal::compiled_matches(&values, constant, &alice));
        assert!(!Principal::compiled_matches(&values, constant, &bob));

        let variable =
            CompiledComponentPattern::<Principal>::new(ComponentPattern::Variable(actor))
                .subst(&substitution)
                .expect("the candidate bound actor");
        assert!(Principal::compiled_matches(&values, variable, &alice));
        assert!(!Principal::compiled_matches(&values, variable, &bob));

        let atom: CompiledAtomPattern<'_> =
            AtomPattern::Principal(ComponentPattern::Variable(actor));
        let event = Event::new("alice", Action::Read, ["a"]);
        assert!(
            atom.subst(&substitution)
                .is_some_and(|concrete| concrete.matches(&values, &event))
        );
    }
}
