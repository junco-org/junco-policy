//! Runtime evaluation over canonical syntax.
//!
//! Evaluation receives every dependency explicitly: canonical store, tail root, committed history,
//! and candidate substitution. No evaluator or node retains a rule, scope, store, or validator
//! backreference.

use crate::model::Event;

use super::component::{CandidateSubstitution, ComponentResolver, Subst};
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
    for event in history {
        state = derive(store, state, event, substitution);
    }
    store.nullable(state)
}

/// Computes one exact derivative and normalizes every constructed residual through `store`.
pub(super) fn derive<'arena>(
    store: &mut CanonicalStore<'arena>,
    regex: RegexId<'arena>,
    event: &Event,
    substitution: &CandidateSubstitution<'arena>,
) -> RegexId<'arena> {
    match regex.get().kind {
        RegexKind::Empty | RegexKind::Epsilon => store.empty,
        RegexKind::All => store.all,
        RegexKind::Test(test) => {
            if eval_test(test, event, substitution, &store.resolver) {
                store.epsilon
            } else {
                store.empty
            }
        }
        RegexKind::Union(children) => {
            let derivatives = children
                .iter()
                .map(|child| derive(store, *child, event, substitution))
                .collect();
            store.regex_union(derivatives)
        }
        RegexKind::Intersect(children) => {
            let derivatives = children
                .iter()
                .map(|child| derive(store, *child, event, substitution))
                .collect();
            store.regex_intersect(derivatives)
        }
        RegexKind::Not(inner) => {
            let derivative = derive(store, inner, event, substitution);
            store.regex_not(derivative)
        }
        RegexKind::Concat(factors) => {
            let mut alternatives = Vec::new();
            let mut remaining = factors;
            while let Some((factor, suffix)) = remaining.split_first() {
                let derivative = derive(store, *factor, event, substitution);
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
            let derivative = derive(store, inner, event, substitution);
            store.regex_concat(vec![derivative, regex])
        }
    }
}

/// Evaluates one canonical boolean test against an event and candidate substitution.
fn eval_test<'arena>(
    test: TestId<'arena>,
    event: &Event,
    substitution: &CandidateSubstitution<'arena>,
    resolver: &ComponentResolver<'arena>,
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
