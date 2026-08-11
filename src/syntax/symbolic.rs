//! Event-independent symbolic derivatives and direct transition-DAG interpretation.

use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;

use crate::model::Event;

use super::component::{CandidateSubstitution, CompiledAtomPattern};
use super::evaluate::eval_test;
use super::node::{RegexId, RegexKind, TestId, TestNode, TransitionId, TransitionNode};
use super::store::CanonicalStore;

/// Persistent event-independent derivatives and their relevant atom sets.
#[derive(Default)]
pub(crate) struct SymbolicDerivativeCache<'arena> {
    derivatives: HashMap<RegexId<'arena>, TransitionId<'arena>>,
    atoms: HashMap<TransitionId<'arena>, Box<[CompiledAtomPattern<'arena>]>>,
}

impl<'arena> SymbolicDerivativeCache<'arena> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.derivatives.len()
    }

    fn atoms(&mut self, transition: TransitionId<'arena>) -> &[CompiledAtomPattern<'arena>] {
        self.atoms.entry(transition).or_insert_with(|| {
            let mut atoms = Vec::new();
            collect_transition_atoms(
                transition,
                &mut HashSet::new(),
                &mut HashSet::new(),
                &mut atoms,
            );
            let mut seen = HashSet::new();
            atoms.retain(|atom| seen.insert(*atom));
            atoms.into_boxed_slice()
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Symbol(SmallVec<[u64; 1]>);

/// Successors selected under one fixed candidate substitution.
pub(super) struct InstantiationCache<'arena, 'event> {
    values: HashMap<(TransitionId<'arena>, Symbol), RegexId<'arena>>,
    last: Option<(TransitionId<'arena>, &'event Event, RegexId<'arena>)>,
}

impl<'arena, 'event> InstantiationCache<'arena, 'event> {
    pub(super) fn new() -> Self {
        Self {
            values: HashMap::new(),
            last: None,
        }
    }

    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.values.len()
    }
}

fn collect_test_atoms<'arena>(
    test: TestId<'arena>,
    visited: &mut HashSet<TestId<'arena>>,
    atoms: &mut Vec<CompiledAtomPattern<'arena>>,
) {
    if !visited.insert(test) {
        return;
    }
    match *test.get() {
        TestNode::True | TestNode::False => {}
        TestNode::Atom { pattern, .. } => atoms.push(pattern),
        TestNode::And(children) | TestNode::Or(children) => {
            for child in children {
                collect_test_atoms(*child, visited, atoms);
            }
        }
    }
}

fn collect_transition_atoms<'arena>(
    transition: TransitionId<'arena>,
    visited_transitions: &mut HashSet<TransitionId<'arena>>,
    visited_tests: &mut HashSet<TestId<'arena>>,
    atoms: &mut Vec<CompiledAtomPattern<'arena>>,
) {
    if !visited_transitions.insert(transition) {
        return;
    }
    match *transition.get() {
        TransitionNode::Const(_) => {}
        TransitionNode::If {
            test,
            then_transition,
            else_transition,
        } => {
            collect_test_atoms(test, visited_tests, atoms);
            collect_transition_atoms(then_transition, visited_transitions, visited_tests, atoms);
            collect_transition_atoms(else_transition, visited_transitions, visited_tests, atoms);
        }
        TransitionNode::Union(children) | TransitionNode::Intersect(children) => {
            for child in children {
                collect_transition_atoms(*child, visited_transitions, visited_tests, atoms);
            }
        }
        TransitionNode::Not(inner) => {
            collect_transition_atoms(inner, visited_transitions, visited_tests, atoms);
        }
        TransitionNode::Append { transition, .. } => {
            collect_transition_atoms(transition, visited_transitions, visited_tests, atoms);
        }
    }
}

/// Returns the normalized symbolic derivative of `regex`, independent of bindings and events.
pub(super) fn symbolic_derivative<'arena>(
    store: &mut CanonicalStore<'arena>,
    derivatives: &mut SymbolicDerivativeCache<'arena>,
    regex: RegexId<'arena>,
) -> TransitionId<'arena> {
    if let Some(transition) = derivatives.derivatives.get(&regex) {
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
                .collect::<SmallVec<[TransitionId<'arena>; 4]>>();
            store.transition_union(transitions)
        }
        RegexKind::Intersect(children) => {
            let transitions = children
                .iter()
                .map(|child| symbolic_derivative(store, derivatives, *child))
                .collect::<SmallVec<[TransitionId<'arena>; 4]>>();
            store.transition_intersect(transitions)
        }
        RegexKind::Not(inner) => {
            let transition = symbolic_derivative(store, derivatives, inner);
            store.transition_not(transition)
        }
        RegexKind::Concat(factors) => {
            let mut alternatives = SmallVec::<[TransitionId<'arena>; 4]>::new();
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

    let previous = derivatives.derivatives.insert(regex, transition);
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
                .collect::<SmallVec<[RegexId<'arena>; 4]>>();
            store.regex_union(regexes)
        }
        TransitionNode::Intersect(children) => {
            let regexes = children
                .iter()
                .map(|child| eval_transition(store, *child, substitution, event))
                .collect::<SmallVec<[RegexId<'arena>; 4]>>();
            store.regex_intersect(regexes)
        }
        TransitionNode::Not(inner) => {
            let regex = eval_transition(store, inner, substitution, event);
            store.regex_not(regex)
        }
        TransitionNode::Append { transition, suffix } => {
            let regex = eval_transition(store, transition, substitution, event);
            let mut factors = SmallVec::<[RegexId<'arena>; 4]>::new();
            factors.push(regex);
            factors.extend_from_slice(suffix);
            store.regex_concat(factors)
        }
    }
}

fn concrete_symbol<'arena>(
    store: &mut CanonicalStore<'arena>,
    atoms: &[CompiledAtomPattern<'arena>],
    substitution: &CandidateSubstitution<'arena>,
    event: &Event,
) -> Symbol {
    let mut words = SmallVec::from_elem(0, atoms.len().div_ceil(64));
    for (index, atom) in atoms.iter().enumerate() {
        let matches = atom
            .subst(substitution)
            .is_some_and(|resolved| resolved.matches(&mut store.resolver, event));
        if matches {
            words[index / 64] |= 1 << (index % 64);
        }
    }
    Symbol(words)
}

/// Instantiates one symbolic transition for a concrete symbol, reusing the fixed-substitution cache.
pub(super) fn instantiate<'arena, 'event>(
    store: &mut CanonicalStore<'arena>,
    derivatives: &mut SymbolicDerivativeCache<'arena>,
    cache: &mut InstantiationCache<'arena, 'event>,
    transition: TransitionId<'arena>,
    substitution: &CandidateSubstitution<'arena>,
    event: &'event Event,
) -> RegexId<'arena> {
    if let Some((previous_transition, previous_event, regex)) = cache.last
        && previous_transition == transition
        && previous_event == event
    {
        return regex;
    }

    let symbol = concrete_symbol(store, derivatives.atoms(transition), substitution, event);
    let regex = match cache.values.entry((transition, symbol)) {
        Entry::Occupied(entry) => *entry.get(),
        Entry::Vacant(entry) => {
            let regex = eval_transition(store, transition, substitution, event);
            *entry.insert(regex)
        }
    };
    cache.last = Some((transition, event, regex));
    regex
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
    let mut previous_derivative = None;
    let mut instances = InstantiationCache::new();
    for event in history {
        let transition = match previous_derivative {
            Some((previous_state, transition)) if previous_state == state => transition,
            _ => symbolic_derivative(store, derivatives, state),
        };
        previous_derivative = Some((state, transition));
        state = instantiate(
            store,
            derivatives,
            &mut instances,
            transition,
            substitution,
            event,
        );
    }
    store.nullable(state)
}
