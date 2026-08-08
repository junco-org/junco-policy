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

/// Heterogeneous resolved value stored in a candidate substitution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum ResolvedValue<'arena> {
    Principal(<Principal as ComponentDomain<'arena>>::Resolved),
    Action(<Action as ComponentDomain<'arena>>::Resolved),
    Resource(<Resource as ComponentDomain<'arena>>::Resolved),
}

/// Resolved candidate values assigned to variables during one rule evaluation.
#[derive(Debug, Default)]
pub(crate) struct CandidateSubstitution<'arena> {
    values: HashMap<DefaultSymbol, ResolvedValue<'arena>>,
}

/// Structural application of a substitution to a pattern-like value.
pub(super) trait Subst<Substitution> {
    /// Variable-free value produced by successful substitution.
    type Concrete;

    /// Applies `substitution`, returning `None` when a referenced variable is unbound.
    fn subst(&self, substitution: &Substitution) -> Option<Self::Concrete>;
}

/// Returns the compatible union of two maps without modifying either input.
fn merge_map<Key, Value>(
    left: &HashMap<Key, Value>,
    right: &HashMap<Key, Value>,
) -> Option<HashMap<Key, Value>>
where
    Key: Clone + Eq + Hash,
    Value: Clone + Eq,
{
    if right
        .iter()
        .any(|(key, value)| left.get(key).is_some_and(|existing| existing != value))
    {
        return None;
    }
    let mut merged = left.clone();
    merged.extend(right.clone());
    Some(merged)
}

impl<'arena> CandidateSubstitution<'arena> {
    /// Creates one partial substitution assignment.
    pub(super) fn singleton(variable: DefaultSymbol, value: ResolvedValue<'arena>) -> Self {
        Self {
            values: HashMap::from([(variable, value)]),
        }
    }

    /// Returns a new compatible union without modifying either input substitution.
    pub(super) fn merge(&self, other: &Self) -> Option<Self> {
        Some(Self {
            values: merge_map(&self.values, &other.values)?,
        })
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

    /// Injects one domain value into the heterogeneous substitution range.
    fn inject(value: Self::Resolved) -> ResolvedValue<'arena>;

    /// Projects this domain from the heterogeneous substitution range.
    fn project(value: ResolvedValue<'arena>) -> Option<Self::Resolved>;
}

impl<'arena> ComponentDomain<'arena> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Resolved = DefaultSymbol;

    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved {
        resolver.intern_string(value.as_str())
    }

    fn inject(value: Self::Resolved) -> ResolvedValue<'arena> {
        ResolvedValue::Principal(value)
    }

    fn project(value: ResolvedValue<'arena>) -> Option<Self::Resolved> {
        match value {
            ResolvedValue::Principal(value) => Some(value),
            _ => None,
        }
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

    fn inject(value: Self::Resolved) -> ResolvedValue<'arena> {
        ResolvedValue::Action(value)
    }

    fn project(value: ResolvedValue<'arena>) -> Option<Self::Resolved> {
        match value {
            ResolvedValue::Action(value) => Some(value),
            _ => None,
        }
    }
}

impl<'arena> ComponentDomain<'arena> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Resolved = ResolvedResource<'arena>;

    fn resolve(resolver: &mut ComponentResolver<'arena>, value: &Self) -> Self::Resolved {
        resolver.resolve_resource(value)
    }

    fn inject(value: Self::Resolved) -> ResolvedValue<'arena> {
        ResolvedValue::Resource(value)
    }

    fn project(value: ResolvedValue<'arena>) -> Option<Self::Resolved> {
        match value {
            ResolvedValue::Resource(value) => Some(value),
            _ => None,
        }
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
    /// Resolves the event component and compares it with this resolved atom value.
    pub(super) fn matches(&self, resolver: &mut ComponentResolver<'arena>, event: &Event) -> bool {
        match self {
            Self::Principal(expected) => {
                *expected == Principal::resolve(resolver, &event.principal)
            }
            Self::Action(expected) => *expected == Action::resolve(resolver, &event.action),
            Self::Resource(expected) => *expected == Resource::resolve(resolver, &event.resource),
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
    match pattern {
        ComponentPattern::Constant(expected) => Some(*expected),
        ComponentPattern::Variable(variable) => substitution
            .values
            .get(variable)
            .copied()
            .and_then(ComponentType::project),
    }
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
        left.values.insert(actor, ResolvedValue::Principal(alice));
        let mut right = CandidateSubstitution::default();
        right
            .values
            .insert(actor, ResolvedValue::Principal(same_alice));
        right.values.insert(operation, ResolvedValue::Action(read));

        let merged = left.merge(&right).expect("bindings agree");
        assert_eq!(
            merged.values.get(&actor),
            Some(&ResolvedValue::Principal(alice))
        );
        assert_eq!(
            merged.values.get(&operation),
            Some(&ResolvedValue::Action(read))
        );
        assert!(!left.values.contains_key(&operation));
        assert!(right.values.contains_key(&operation));
    }

    #[test]
    fn merge_rejects_conflicting_same_domain_bindings() {
        let arena = Bump::new();
        let mut resolver = ComponentResolver::new(&arena);
        let actor = variable(&mut resolver, "actor");
        let alice = resolver.intern_string("alice");
        let bob = resolver.intern_string("bob");

        let mut left = CandidateSubstitution::default();
        left.values.insert(actor, ResolvedValue::Principal(alice));
        let mut right = CandidateSubstitution::default();
        right.values.insert(actor, ResolvedValue::Principal(bob));

        assert!(left.merge(&right).is_none());
        assert_eq!(
            left.values.get(&actor),
            Some(&ResolvedValue::Principal(alice))
        );
    }

    #[test]
    fn merge_rejects_cross_domain_bindings() {
        let arena = Bump::new();
        let mut resolver = ComponentResolver::new(&arena);
        let value = variable(&mut resolver, "value");
        let alice = resolver.intern_string("alice");

        let mut left = CandidateSubstitution::default();
        left.values.insert(value, ResolvedValue::Principal(alice));
        let mut right = CandidateSubstitution::default();
        right
            .values
            .insert(value, ResolvedValue::Action(ResolvedAction::Read));

        assert!(left.merge(&right).is_none());
    }

    #[test]
    fn subst_resolves_components_and_atoms() {
        let arena = Bump::new();
        let mut resolver = ComponentResolver::new(&arena);
        let actor = variable(&mut resolver, "actor");
        let alice = Principal::new("alice");
        let bob = Principal::new("bob");
        let alice_symbol = resolver.intern_string("alice");
        let alice_resolved = Principal::resolve(&mut resolver, &alice);
        let bob_resolved = Principal::resolve(&mut resolver, &bob);
        let mut substitution = CandidateSubstitution::default();
        substitution
            .values
            .insert(actor, ResolvedValue::Principal(alice_symbol));

        let constant: InternedPattern<'_, Principal> = ComponentPattern::Constant(alice_symbol);
        let constant = subst_component::<Principal>(&constant, &substitution)
            .expect("constants always substitute");
        assert_eq!(constant, alice_resolved);
        assert_ne!(constant, bob_resolved);

        let variable: InternedPattern<'_, Principal> = ComponentPattern::Variable(actor);
        let variable = subst_component::<Principal>(&variable, &substitution)
            .expect("the candidate bound actor");
        assert_eq!(variable, alice_resolved);
        assert_ne!(variable, bob_resolved);

        let atom: InternedAtomPattern<'_> =
            AtomPattern::Principal(ComponentPattern::Variable(actor));
        let event = Event::new("alice", Action::Read, ["a"]);
        assert!(
            atom.subst(&substitution)
                .is_some_and(|resolved| resolved.matches(&mut resolver, &event))
        );
    }
}
