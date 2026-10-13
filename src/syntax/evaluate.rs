//! Concrete derivative oracle and shared event-test evaluation.
//!
//! Production matching uses cached symbolic transitions. The concrete derivative implementation is
//! retained only in test builds as a differential oracle.

#[cfg(test)]
use std::hash::{BuildHasher, Hash};

#[cfg(test)]
use hashbrown::HashMap;
#[cfg(test)]
use hashbrown::hash_map::RawEntryMut;
#[cfg(test)]
use smallvec::SmallVec;

use crate::model::Event;

use super::component::CandidateSubstitution;
#[cfg(test)]
use super::node::{RegexId, RegexKind};
use super::node::{TestId, TestNode};
use super::source::Comparison;
#[cfg(test)]
use super::store::CanonicalStore;

/// Concrete complete-history evaluator retained for symbolic differential tests.
#[cfg(test)]
pub(super) fn accepts_direct<'arena, 'event, E: Event + 'arena + 'event>(
    store: &mut CanonicalStore<'arena, E>,
    root: RegexId<'arena, E>,
    history: impl IntoIterator<Item = &'event E>,
    substitution: &CandidateSubstitution<E>,
) -> bool {
    let mut state = root;
    let mut derivatives = DerivativeCache::new();
    for event in history {
        state = derive_cached(store, state, event, substitution, &mut derivatives);
    }
    store.nullable(state)
}

#[cfg(test)]
/// Computes one exact derivative and normalizes every constructed residual through `store`.
pub(super) fn derive<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    regex: RegexId<'arena, E>,
    event: &E,
    substitution: &CandidateSubstitution<E>,
) -> RegexId<'arena, E> {
    derive_cached(
        store,
        regex,
        event,
        substitution,
        &mut DerivativeCache::new(),
    )
}

#[cfg(test)]
pub(super) type DerivativeCache<'arena, 'event, E> =
    HashMap<(RegexId<'arena, E>, &'event E), RegexId<'arena, E>>;

#[cfg(test)]
fn cache_hash<E: Event, Key>(cache: &DerivativeCache<'_, '_, E>, key: &Key) -> u64
where
    Key: Hash,
{
    cache.hasher().hash_one(key)
}

/// Reuses exact concrete derivatives for one fixed candidate substitution.
///
/// Scoping this cache to one [`accepts_direct`] call makes `(state, event)` a complete key while
/// avoiding persistent growth over the unbounded event and substitution domains.
#[cfg(test)]
pub(super) fn derive_cached<'arena, 'event, E: Event + 'arena + 'event>(
    store: &mut CanonicalStore<'arena, E>,
    regex: RegexId<'arena, E>,
    event: &'event E,
    substitution: &CandidateSubstitution<E>,
    derivatives: &mut DerivativeCache<'arena, 'event, E>,
) -> RegexId<'arena, E> {
    let key = (regex, event);
    let hash = cache_hash(derivatives, &key);
    if let Some((_, derivative)) = derivatives.raw_entry().from_key_hashed_nocheck(hash, &key) {
        return *derivative;
    }

    let derivative = match regex.get().kind {
        RegexKind::Empty | RegexKind::Epsilon => store.empty,
        RegexKind::All => store.all,
        RegexKind::Test(test) => {
            if eval_test(test, event, substitution) {
                store.epsilon
            } else {
                store.empty
            }
        }
        RegexKind::Union(children) => {
            let children = children
                .iter()
                .map(|child| derive_cached(store, *child, event, substitution, derivatives))
                .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
            store.regex_union(children)
        }
        RegexKind::Intersect(children) => {
            let children = children
                .iter()
                .map(|child| derive_cached(store, *child, event, substitution, derivatives))
                .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
            store.regex_intersect(children)
        }
        RegexKind::Not(inner) => {
            let inner = derive_cached(store, inner, event, substitution, derivatives);
            store.regex_not(inner)
        }
        RegexKind::Concat(factors) => {
            let mut alternatives = SmallVec::<[RegexId<'arena, E>; 4]>::new();
            let mut remaining = factors;
            while let Some((factor, suffix)) = remaining.split_first() {
                let derivative = derive_cached(store, *factor, event, substitution, derivatives);
                let mut product = SmallVec::<[RegexId<'arena, E>; 4]>::new();
                product.push(derivative);
                product.extend_from_slice(suffix);
                alternatives.push(store.regex_concat(product));
                if !store.nullable(*factor) {
                    break;
                }
                remaining = suffix;
            }
            store.regex_union(alternatives)
        }
        RegexKind::Star(inner) => {
            let inner = derive_cached(store, inner, event, substitution, derivatives);
            store.regex_concat([inner, regex])
        }
    };

    match derivatives
        .raw_entry_mut()
        .from_key_hashed_nocheck(hash, &key)
    {
        RawEntryMut::Occupied(entry) => *entry.get(),
        RawEntryMut::Vacant(entry) => {
            entry.insert_hashed_nocheck(hash, key, derivative);
            derivative
        }
    }
}

/// Evaluates one canonical boolean test against an event and candidate substitution.
pub(super) fn eval_test<'arena, E: Event + 'arena>(
    test: TestId<'arena, E>,
    event: &E,
    substitution: &CandidateSubstitution<E>,
) -> bool {
    match *test.get() {
        TestNode::True => true,
        TestNode::False => false,
        TestNode::Atom {
            comparison,
            pattern,
        } => {
            let equal = pattern
                .subst(substitution)
                .is_some_and(|resolved| resolved.matches(event));
            match comparison {
                Comparison::Eq => equal,
                Comparison::Neq => !equal,
            }
        }
        TestNode::And(children) => children
            .iter()
            .all(|child| eval_test(*child, event, substitution)),
        TestNode::Or(children) => children
            .iter()
            .any(|child| eval_test(*child, event, substitution)),
    }
}
