//! Event-independent symbolic derivatives and direct transition-DAG interpretation.

use std::collections::HashMap;

use crate::model::Event;

use super::component::CandidateSubstitution;
use super::evaluate::eval_test;
use super::node::{RegexId, RegexKind, TransitionId, TransitionNode};
use super::store::CanonicalStore;

/// Persistent per-rule cache from normalized regex state to normalized symbolic derivative.
pub(crate) type SymbolicDerivativeCache<'arena> = HashMap<RegexId<'arena>, TransitionId<'arena>>;

/// Returns the normalized symbolic derivative of `regex`, independent of bindings and events.
pub(super) fn symbolic_derivative<'arena>(
    store: &mut CanonicalStore<'arena>,
    derivatives: &mut SymbolicDerivativeCache<'arena>,
    regex: RegexId<'arena>,
) -> TransitionId<'arena> {
    if let Some(transition) = derivatives.get(&regex) {
        return *transition;
    }

    let transition = match regex.get().kind {
        RegexKind::Empty | RegexKind::Epsilon => store.transition_empty,
        RegexKind::All => store.transition_all,
        RegexKind::Test(test) => {
            store.transition_if(test, store.transition_epsilon, store.transition_empty)
        }
        RegexKind::Union(children) => {
            let transitions = children
                .iter()
                .map(|child| symbolic_derivative(store, derivatives, *child))
                .collect();
            store.transition_union(transitions)
        }
        RegexKind::Intersect(children) => {
            let transitions = children
                .iter()
                .map(|child| symbolic_derivative(store, derivatives, *child))
                .collect();
            store.transition_intersect(transitions)
        }
        RegexKind::Not(inner) => {
            let transition = symbolic_derivative(store, derivatives, inner);
            store.transition_not(transition)
        }
        RegexKind::Concat(factors) => {
            let mut alternatives = Vec::new();
            let mut remaining = factors;
            while let Some((factor, suffix)) = remaining.split_first() {
                let transition = symbolic_derivative(store, derivatives, *factor);
                alternatives.push(store.transition_append(transition, suffix));
                if !store.nullable(*factor) {
                    break;
                }
                remaining = suffix;
            }
            store.transition_union(alternatives)
        }
        RegexKind::Star(inner) => {
            let transition = symbolic_derivative(store, derivatives, inner);
            store.transition_append(transition, &[regex])
        }
    };

    let previous = derivatives.insert(regex, transition);
    debug_assert!(previous.is_none());
    transition
}

/// Interprets one normalized transition under fixed candidate bindings and one history event.
pub(super) fn eval_transition<'arena>(
    store: &mut CanonicalStore<'arena>,
    transition: TransitionId<'arena>,
    substitution: &CandidateSubstitution<'arena>,
    event: &Event,
) -> RegexId<'arena> {
    match *transition.get() {
        TransitionNode::Const(regex) => regex,
        TransitionNode::If {
            test,
            then_transition,
            else_transition,
        } => {
            let selected = if eval_test(test, event, substitution, &mut store.resolver) {
                then_transition
            } else {
                else_transition
            };
            eval_transition(store, selected, substitution, event)
        }
        TransitionNode::Union(children) => {
            let regexes = children
                .iter()
                .map(|child| eval_transition(store, *child, substitution, event))
                .collect();
            store.regex_union(regexes)
        }
        TransitionNode::Intersect(children) => {
            let regexes = children
                .iter()
                .map(|child| eval_transition(store, *child, substitution, event))
                .collect();
            store.regex_intersect(regexes)
        }
        TransitionNode::Not(inner) => {
            let regex = eval_transition(store, inner, substitution, event);
            store.regex_not(regex)
        }
        TransitionNode::Append { transition, suffix } => {
            let regex = eval_transition(store, transition, substitution, event);
            let mut factors = Vec::with_capacity(1 + suffix.len());
            factors.push(regex);
            factors.extend_from_slice(suffix);
            store.regex_concat(factors)
        }
    }
}

/// Evaluates complete history using event-independent derivatives cached across rule runs.
pub(super) fn accepts<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    derivatives: &mut SymbolicDerivativeCache<'arena>,
    root: RegexId<'arena>,
    history: impl IntoIterator<Item = &'event Event>,
    substitution: &CandidateSubstitution<'arena>,
) -> bool {
    let mut state = root;
    for event in history {
        let transition = symbolic_derivative(store, derivatives, state);
        state = eval_transition(store, transition, substitution, event);
    }
    store.nullable(state)
}
