//! Component-specific compilation, matching, and typed substitution storage.
//!
//! [`ComponentDomain`] associates each model component with one canonical arena-backed
//! representation used by both policy constants and candidate bindings. Each implementation also
//! selects its typed map in [`CandidateSubstitution`], so domains cannot be mixed.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use bumpalo::Bump;
use string_interner::{DefaultStringInterner, DefaultSymbol};

use crate::model::{Action, Event, Principal, Resource};

use super::source::{AtomPattern, Component, ComponentPattern, PatternRepresentation};

/// Resolved action value using string-interner symbols for commit messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum ResolvedAction {
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

/// Resolved resource value represented as an arena-backed sequence of segment symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct ResolvedResource<'arena>(&'arena [DefaultSymbol]);

/// Resolves model values using a black-box string interner and arena allocation.
pub(super) struct ComponentResolver<'arena> {
    arena: &'arena Bump,
    strings: DefaultStringInterner,
}

impl<'arena> ComponentResolver<'arena> {
    /// Creates a resolver backed by `arena`.
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

    /// Resolves one ordered resource sequence after interning every segment string.
    pub(super) fn resolve_resource(&mut self, value: &Resource) -> ResolvedResource<'arena> {
        let segments: Vec<DefaultSymbol> = value
            .segments()
            .iter()
            .map(|segment| self.intern_string(segment))
            .collect();
        ResolvedResource(self.arena.alloc_slice_copy(&segments))
    }

    /// Number of distinct interned strings, used to verify value reuse.
    #[cfg(test)]
    pub(super) fn string_count(&self) -> usize {
        self.strings.len()
    }
}

/// Resolved candidate values assigned to head variables during one rule evaluation.
///
/// Every map stores the same resolved representation used by constant patterns.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'arena> {
    principals: HashMap<DefaultSymbol, <Principal as ComponentDomain<'arena>>::Resolved>,
    actions: HashMap<DefaultSymbol, <Action as ComponentDomain<'arena>>::Resolved>,
    resources: HashMap<DefaultSymbol, <Resource as ComponentDomain<'arena>>::Resolved>,
}

/// Structural application of a substitution to a pattern-like value.
pub(super) trait Subst<Substitution, Domain = ()> {
    /// Variable-free value produced by successful substitution.
    type Concrete;

    /// Applies `substitution`, returning `None` when a referenced variable is unbound.
    fn subst(&self, substitution: &Substitution) -> Option<Self::Concrete>;
}

impl<'arena> CandidateSubstitution<'arena> {
    /// Combines partial substitutions produced by distinct, statically typed head coordinates.
    ///
    /// `VariableEnvironment` has already rejected cross-domain variable reuse, and a head has only
    /// one coordinate per domain, so compatibility is guaranteed for every interned head.
    pub(super) fn merge(mut self, other: Self) -> Self {
        self.principals.extend(other.principals);
        self.actions.extend(other.actions);
        self.resources.extend(other.resources);
        self
    }
}

/// Resolves and compares one capability-product component domain.
pub(super) trait ComponentDomain<'arena>: Sized + Eq {
    /// Product coordinate occupied by this component.
    const COMPONENT: Component;

    /// Variable-free representation produced by resolution.
    type Resolved: Clone + Copy + Debug + PartialEq + Eq + Hash;

    /// Resolves a model value into the representation shared by constants and substitutions.
    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved;

    /// Compares one resolved value with a model value through the resolver.
    fn resolved_matches(
        resolver: &ComponentResolver<'arena>,
        expected: Self::Resolved,
        actual: &Self,
    ) -> bool;

    /// Returns the immutable substitution map belonging to this component.
    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Resolved>;

    /// Returns the mutable substitution map belonging to this component.
    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Resolved>;
}

impl<'arena> ComponentDomain<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Resolved = DefaultSymbol;

    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved {
        resolver.intern_string(value.as_str())
    }

    fn resolved_matches(
        resolver: &ComponentResolver<'arena>,
        expected: Self::Resolved,
        actual: &Self,
    ) -> bool {
        resolver.resolve_string(expected) == actual.as_str()
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Resolved> {
        &substitution.principals
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Resolved> {
        &mut substitution.principals
    }
}

impl<'arena> ComponentDomain<'arena> for Action {
    const COMPONENT: Component = Component::Action;
    type Resolved = ResolvedAction;

    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved {
        match value {
            Action::Read => ResolvedAction::Read,
            Action::Edit => ResolvedAction::Edit,
            Action::Stage => ResolvedAction::Stage,
            Action::Unstage => ResolvedAction::Unstage,
            Action::Commit { message } => ResolvedAction::Commit(
                message
                    .as_deref()
                    .map(|message| resolver.intern_string(message)),
            ),
            Action::Checkout => ResolvedAction::Checkout,
            Action::Stash => ResolvedAction::Stash,
            Action::Diff => ResolvedAction::Diff,
            Action::History => ResolvedAction::History,
        }
    }

    fn resolved_matches(
        resolver: &ComponentResolver<'arena>,
        expected: Self::Resolved,
        actual: &Self,
    ) -> bool {
        match (expected, actual) {
            (ResolvedAction::Read, Action::Read)
            | (ResolvedAction::Edit, Action::Edit)
            | (ResolvedAction::Stage, Action::Stage)
            | (ResolvedAction::Unstage, Action::Unstage)
            | (ResolvedAction::Checkout, Action::Checkout)
            | (ResolvedAction::Stash, Action::Stash)
            | (ResolvedAction::Diff, Action::Diff)
            | (ResolvedAction::History, Action::History) => true,
            (ResolvedAction::Commit(expected), Action::Commit { message }) => {
                expected.map(|symbol| resolver.resolve_string(symbol)) == message.as_deref()
            }
            _ => false,
        }
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Resolved> {
        &substitution.actions
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Resolved> {
        &mut substitution.actions
    }
}

impl<'arena> ComponentDomain<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Resolved = ResolvedResource<'arena>;

    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved {
        resolver.resolve_resource(value)
    }

    fn resolved_matches(
        resolver: &ComponentResolver<'arena>,
        expected: Self::Resolved,
        actual: &Self,
    ) -> bool {
        expected.0.len() == actual.segments().len()
            && expected
                .0
                .iter()
                .zip(actual.segments())
                .all(|(left, right)| resolver.resolve_string(*left) == right)
    }

    fn bindings<'substitution>(
        substitution: &'substitution CandidateSubstitution<'arena>,
    ) -> &'substitution HashMap<DefaultSymbol, Self::Resolved> {
        &substitution.resources
    }

    fn bindings_mut<'substitution>(
        substitution: &'substitution mut CandidateSubstitution<'arena>,
    ) -> &'substitution mut HashMap<DefaultSymbol, Self::Resolved> {
        &mut substitution.resources
    }
}

/// Interned representation used by runtime atom patterns before substitution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct InternedRepresentation<'arena>(PhantomData<&'arena ()>);

impl<'arena> PatternRepresentation for InternedRepresentation<'arena> {
    type PrincipalValue = <Principal as ComponentDomain<'arena>>::Resolved;
    type ActionValue = <Action as ComponentDomain<'arena>>::Resolved;
    type ResourceValue = <Resource as ComponentDomain<'arena>>::Resolved;
    type Variable = DefaultSymbol;
}

/// Interned pattern for one statically selected component domain.
pub(super) type InternedPattern<'arena, ComponentType> =
    ComponentPattern<<ComponentType as ComponentDomain<'arena>>::Resolved, DefaultSymbol>;

/// Interned, structurally hashable atom pattern stored in [`TestNode`](super::node::TestNode).
pub(super) type InternedAtomPattern<'arena> = AtomPattern<InternedRepresentation<'arena>>;

/// Variable-free atom produced by applying a substitution to an interned atom pattern.
pub(super) enum ResolvedAtom<'arena> {
    Principal(<Principal as ComponentDomain<'arena>>::Resolved),
    Action(<Action as ComponentDomain<'arena>>::Resolved),
    Resource(<Resource as ComponentDomain<'arena>>::Resolved),
}

impl<'arena> ResolvedAtom<'arena> {
    /// Compares this resolved atom with a model event through the component resolver.
    pub(super) fn matches(&self, resolver: &ComponentResolver<'arena>, event: &Event) -> bool {
        match self {
            Self::Principal(expected) => {
                Principal::resolved_matches(resolver, *expected, &event.principal)
            }
            Self::Action(expected) => Action::resolved_matches(resolver, *expected, &event.action),
            Self::Resource(expected) => {
                Resource::resolved_matches(resolver, *expected, &event.resource)
            }
        }
    }
}

impl<'arena, ComponentType> Subst<CandidateSubstitution<'arena>, ComponentType>
    for InternedPattern<'arena, ComponentType>
where
    ComponentType: ComponentDomain<'arena>,
{
    type Concrete = ComponentType::Resolved;

    fn subst(&self, substitution: &CandidateSubstitution<'arena>) -> Option<Self::Concrete> {
        match self {
            ComponentPattern::Constant(expected) => Some(*expected),
            ComponentPattern::Variable(variable) => {
                ComponentType::bindings(substitution).get(variable).copied()
            }
        }
    }
}

fn subst_component<'arena, ComponentType>(
    pattern: &InternedPattern<'arena, ComponentType>,
    substitution: &CandidateSubstitution<'arena>,
) -> Option<ComponentType::Resolved>
where
    ComponentType: ComponentDomain<'arena>,
{
    <InternedPattern<'arena, ComponentType> as Subst<
        CandidateSubstitution<'arena>,
        ComponentType,
    >>::subst(pattern, substitution)
}

impl<'arena> Subst<CandidateSubstitution<'arena>> for InternedAtomPattern<'arena> {
    type Concrete = ResolvedAtom<'arena>;

    fn subst(&self, substitution: &CandidateSubstitution<'arena>) -> Option<Self::Concrete> {
        match self {
            AtomPattern::Principal(pattern) => {
                subst_component::<Principal>(pattern, substitution).map(ResolvedAtom::Principal)
            }
            AtomPattern::Action(pattern) => {
                subst_component::<Action>(pattern, substitution).map(ResolvedAtom::Action)
            }
            AtomPattern::Resource(pattern) => {
                subst_component::<Resource>(pattern, substitution).map(ResolvedAtom::Resource)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variable(resolver: &mut ComponentResolver<'_>, name: &str) -> DefaultSymbol {
        resolver.intern_string(name)
    }

    #[test]
    fn component_resolver_unifies_constants_and_candidates() {
        let arena = Bump::new();
        let mut resolver = ComponentResolver::new(&arena);

        let constant_principal = Principal::resolve(&mut resolver, &Principal::new("alice"));
        let candidate_principal = Principal::resolve(&mut resolver, &Principal::new("alice"));
        assert_eq!(constant_principal, candidate_principal);
        assert_eq!(resolver.resolve_string(constant_principal), "alice");

        let constant_resource = Resource::resolve(&mut resolver, &Resource::new(["src", "a.rs"]));
        let candidate_resource = Resource::resolve(&mut resolver, &Resource::new(["src", "a.rs"]));
        assert_eq!(constant_resource, candidate_resource);

        let constant_action = Action::resolve(&mut resolver, &Action::commit("ship"));
        let candidate_action = Action::resolve(&mut resolver, &Action::commit("ship"));
        assert_eq!(constant_action, candidate_action);
    }

    #[test]
    fn merge_combines_partial_head_substitutions() {
        let arena = Bump::new();
        let mut resolver = ComponentResolver::new(&arena);
        let actor = variable(&mut resolver, "actor");
        let operation = variable(&mut resolver, "operation");
        let alice = resolver.intern_string("alice");
        let same_alice = resolver.intern_string("alice");
        let read = ResolvedAction::Read;

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
        let mut resolver = ComponentResolver::new(&arena);
        let actor = variable(&mut resolver, "actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let alice_symbol = resolver.intern_string("alice");
        let mut substitution = CandidateSubstitution::default();
        substitution.principals.insert(actor, alice_symbol);

        let constant: InternedPattern<'_, Principal> = ComponentPattern::Constant(alice_symbol);
        let constant = subst_component::<Principal>(&constant, &substitution)
            .expect("constants always substitute");
        assert!(Principal::resolved_matches(&resolver, constant, &alice));
        assert!(!Principal::resolved_matches(&resolver, constant, &bob));

        let variable: InternedPattern<'_, Principal> = ComponentPattern::Variable(actor);
        let variable = subst_component::<Principal>(&variable, &substitution)
            .expect("the candidate bound actor");
        assert!(Principal::resolved_matches(&resolver, variable, &alice));
        assert!(!Principal::resolved_matches(&resolver, variable, &bob));

        let atom: InternedAtomPattern<'_> =
            AtomPattern::Principal(ComponentPattern::Variable(actor));
        let event = Event::new("alice", Action::Read, ["a"]);
        assert!(
            atom.subst(&substitution)
                .is_some_and(|resolved| resolved.matches(&resolver, &event))
        );
    }
}
