//! Runtime evaluation over canonical syntax.
//!
//! Evaluation receives every dependency explicitly: canonical store, tail root, committed history,
//! and candidate substitution. No evaluator or node retains a rule, scope, store, or validator
//! backreference.

use crate::model::{Action, Event, Principal, Resource};

use super::component::{
    CandidateSubstitution, CompiledAtomPattern, CompiledPattern, ComponentDomain,
};
use super::node::{RegexId, RegexKind, TestId, TestNode};
use super::source::{AtomPattern, Comparison, ComponentPattern};
use super::store::CanonicalStore;

/// Evaluates one typed constant-or-variable component pattern.
fn eval_component_pattern<'arena, 'event, ComponentType>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
    substitution: &CandidateSubstitution<'event>,
) -> bool
where
    ComponentType: ComponentDomain<'arena> + 'event,
{
    match pattern {
        ComponentPattern::Constant(expected) => ComponentType::constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => {
            let bound = ComponentType::bindings(substitution)
                .get(&symbol)
                .copied()
                .expect("compiled head binds every tail variable");
            bound == actual
        }
    }
}

/// Evaluates the statically typed atom enum without trait-object dispatch.
fn eval_atom<'arena, 'event>(
    pattern: CompiledAtomPattern<'arena>,
    event: &'event Event,
    substitution: &CandidateSubstitution<'event>,
) -> bool {
    match pattern {
        AtomPattern::Principal(pattern) => {
            eval_component_pattern::<Principal>(pattern, &event.principal, substitution)
        }
        AtomPattern::Action(pattern) => {
            eval_component_pattern::<Action>(pattern, &event.action, substitution)
        }
        AtomPattern::Resource(pattern) => {
            eval_component_pattern::<Resource>(pattern, &event.resource, substitution)
        }
    }
}

/// Returns whether the complete history belongs to `root` under `substitution`.
pub(crate) fn accepts<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    root: RegexId<'arena>,
    history: impl IntoIterator<Item = &'event Event>,
    substitution: &CandidateSubstitution<'event>,
) -> bool {
    let mut state = root;
    for event in history {
        state = derive(store, state, event, substitution);
    }
    store.nullable(state)
}

/// Computes one exact derivative and normalizes every constructed residual through `store`.
pub(super) fn derive<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    regex: RegexId<'arena>,
    event: &'event Event,
    substitution: &CandidateSubstitution<'event>,
) -> RegexId<'arena> {
    match regex.get().kind {
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
            for (index, factor) in factors.iter().enumerate() {
                let derivative = derive(store, *factor, event, substitution);
                let mut product = Vec::with_capacity(factors.len() - index);
                product.push(derivative);
                product.extend_from_slice(&factors[index + 1..]);
                alternatives.push(store.regex_concat(product));
                if !store.nullable(*factor) {
                    break;
                }
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
fn eval_test<'arena, 'event>(
    test: TestId<'arena>,
    event: &'event Event,
    substitution: &CandidateSubstitution<'event>,
) -> bool {
    match *test.get() {
        TestNode::True => true,
        TestNode::False => false,
        TestNode::Atom {
            comparison,
            pattern,
        } => {
            let equal = eval_atom(pattern, event, substitution);
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
