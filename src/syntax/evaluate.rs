//! Runtime evaluation over canonical syntax.
//!
//! Evaluation receives every dependency explicitly. Concrete derivatives are memoized for one
//! complete-history evaluation, whose candidate substitution is immutable; no evaluator or node
//! retains a rule, scope, store, or validator backreference.

use std::collections::HashMap;

use crate::model::Event;

use super::component::{CandidateSubstitution, ComponentResolver};
use super::node::{RegexId, RegexKind, TestId, TestNode};
use super::source::Comparison;
use super::store::CanonicalStore;

/// Returns whether the complete history belongs to `root` under `substitution`.
pub(crate) fn accepts<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    root: RegexId<'arena>,
    history: impl IntoIterator<Item = &'event Event>,
    substitution: &CandidateSubstitution<'arena>,
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
pub(super) fn derive<'arena>(
    store: &mut CanonicalStore<'arena>,
    regex: RegexId<'arena>,
    event: &Event,
    substitution: &CandidateSubstitution<'arena>,
) -> RegexId<'arena> {
    derive_cached(
        store,
        regex,
        event,
        substitution,
        &mut DerivativeCache::new(),
    )
}

pub(super) type DerivativeCache<'arena, 'event> =
    HashMap<(RegexId<'arena>, &'event Event), RegexId<'arena>>;

/// Reuses exact concrete derivatives for one fixed candidate substitution.
///
/// Scoping this cache to one [`accepts`] call makes `(state, event)` a complete key while avoiding
/// persistent growth over the unbounded event and substitution domains.
pub(super) fn derive_cached<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    regex: RegexId<'arena>,
    event: &'event Event,
    substitution: &CandidateSubstitution<'arena>,
    derivatives: &mut DerivativeCache<'arena, 'event>,
) -> RegexId<'arena> {
    if let Some(derivative) = derivatives.get(&(regex, event)) {
        return *derivative;
    }

    let derivative = match regex.get().kind {
        RegexKind::Empty | RegexKind::Epsilon => store.empty,
        RegexKind::All => store.all,
        RegexKind::Test(test) => {
            if eval_test(test, event, substitution, &mut store.resolver) {
                store.epsilon
            } else {
                store.empty
            }
        }
        RegexKind::Union(children) => {
            let children = children
                .iter()
                .map(|child| derive_cached(store, *child, event, substitution, derivatives))
                .collect();
            store.regex_union(children)
        }
        RegexKind::Intersect(children) => {
            let children = children
                .iter()
                .map(|child| derive_cached(store, *child, event, substitution, derivatives))
                .collect();
            store.regex_intersect(children)
        }
        RegexKind::Not(inner) => {
            let inner = derive_cached(store, inner, event, substitution, derivatives);
            store.regex_not(inner)
        }
        RegexKind::Concat(factors) => {
            let mut alternatives = Vec::new();
            let mut remaining = factors;
            while let Some((factor, suffix)) = remaining.split_first() {
                let derivative = derive_cached(store, *factor, event, substitution, derivatives);
                let mut product = Vec::with_capacity(1 + suffix.len());
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
            store.regex_concat(vec![inner, regex])
        }
    };

    let previous = derivatives.insert((regex, event), derivative);
    debug_assert!(previous.is_none());
    derivative
}

/// Evaluates one canonical boolean test against an event and candidate substitution.
fn eval_test<'arena>(
    test: TestId<'arena>,
    event: &Event,
    substitution: &CandidateSubstitution<'arena>,
    resolver: &mut ComponentResolver<'arena>,
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
                .is_some_and(|resolved| resolved.matches(resolver, event));
            match comparison {
                Comparison::Eq => equal,
                Comparison::Neq => !equal,
            }
        }
        TestNode::And(children) => children
            .iter()
            .all(|child| eval_test(*child, event, substitution, resolver)),
        TestNode::Or(children) => children
            .iter()
            .any(|child| eval_test(*child, event, substitution, resolver)),
    }
}
