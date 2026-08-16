//! Event-independent symbolic derivatives and direct transition-DAG interpretation.

use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use smallbitvec::SmallBitVec;
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
    atoms: HashMap<TransitionId<'arena>, Vec<CompiledAtomPattern<'arena>>>,
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
        self.atoms
            .entry(transition)
            .or_insert_with(|| collect_transition_atoms(transition))
    }
}

/// Truth assignment for the atoms of one transition under a fixed substitution.
///
/// Each bit records whether one distinct [`CompiledAtomPattern`] used by the transition matches the
/// current event after applying the candidate substitution. Atom order is the stable first-seen
/// order cached by [`SymbolicDerivativeCache::atoms`]. Equality therefore means that two events
/// induce the same truth assignment for every atom relevant to this transition, even when
/// irrelevant event fields differ.
///
/// The surrounding cache key also includes [`TransitionId`], so assignments based on different atom
/// lists are never compared as the same successor key. [`SmallBitVec`] stores small assignments
/// inline and falls back to packed heap storage for larger truth assignments.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AtomTruthAssignment(SmallBitVec);

/// Successors selected under one fixed candidate substitution.
struct InstantiationCache<'arena, 'event> {
    values: HashMap<(TransitionId<'arena>, AtomTruthAssignment), RegexId<'arena>>,
    last: Option<(TransitionId<'arena>, &'event Event, RegexId<'arena>)>,
}

impl<'arena, 'event> InstantiationCache<'arena, 'event> {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
            last: None,
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.values.len()
    }
}

/// Per-history symbolic evaluator with all mutable matcher state in one place.
///
/// The canonical store and derivative cache are retained by the validator and runtime rule,
/// respectively. The instantiation cache is owned here because its event references and truth
/// assignments are valid only for the current fixed-substitution history replay.
pub(super) struct SymbolicMatcher<'state, 'arena, 'event> {
    store: &'state mut CanonicalStore<'arena>,
    derivatives: &'state mut SymbolicDerivativeCache<'arena>,
    instances: InstantiationCache<'arena, 'event>,
}

impl<'state, 'arena, 'event> SymbolicMatcher<'state, 'arena, 'event> {
    /// Packages the shared canonical store and persistent derivative cache with a fresh
    /// fixed-substitution instantiation cache.
    pub(super) fn new(
        store: &'state mut CanonicalStore<'arena>,
        derivatives: &'state mut SymbolicDerivativeCache<'arena>,
    ) -> Self {
        Self {
            store,
            derivatives,
            instances: InstantiationCache::new(),
        }
    }

    /// Returns the cached normalized symbolic derivative of `regex`.
    pub(super) fn derivative(&mut self, regex: RegexId<'arena>) -> TransitionId<'arena> {
        symbolic_derivative(self.store, self.derivatives, regex)
    }

    /// Interprets one normalized transition without consulting the instantiation cache.
    #[cfg(test)]
    pub(super) fn evaluate(
        &mut self,
        transition: TransitionId<'arena>,
        substitution: &CandidateSubstitution<'arena>,
        event: &Event,
    ) -> RegexId<'arena> {
        eval_transition(self.store, transition, substitution, event)
    }

    /// Instantiates one transition, reusing equivalent atom truth assignments.
    pub(super) fn instantiate(
        &mut self,
        transition: TransitionId<'arena>,
        substitution: &CandidateSubstitution<'arena>,
        event: &'event Event,
    ) -> RegexId<'arena> {
        instantiate_transition(
            self.store,
            self.derivatives,
            &mut self.instances,
            transition,
            substitution,
            event,
        )
    }

    /// Evaluates complete history using event-independent derivatives cached across rule runs.
    pub(super) fn accepts(
        &mut self,
        root: RegexId<'arena>,
        history: impl IntoIterator<Item = &'event Event>,
        substitution: &CandidateSubstitution<'arena>,
    ) -> bool {
        let mut state = root;
        let mut previous_derivative = None;
        for event in history {
            let transition = match previous_derivative {
                Some((previous_state, transition)) if previous_state == state => transition,
                _ => self.derivative(state),
            };
            previous_derivative = Some((state, transition));
            state = self.instantiate(transition, substitution, event);
        }
        self.store.nullable(state)
    }

    /// Number of distinct transition/truth-assignment successors retained in this replay.
    #[cfg(test)]
    pub(super) fn instantiation_count(&self) -> usize {
        self.instances.len()
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

/// Collects the distinct component patterns tested by a transition DAG.
///
/// # Preconditions
/// `transition` must be a canonical transition from the current syntax store.
pub(super) fn collect_transition_atoms<'arena>(
    transition: TransitionId<'arena>,
) -> Vec<CompiledAtomPattern<'arena>> {
    let mut atoms = Vec::new();
    collect_transition_atoms_into(
        transition,
        &mut HashSet::new(),
        &mut HashSet::new(),
        &mut atoms,
    );
    let mut seen = HashSet::new();
    atoms.retain(|atom| seen.insert(*atom));
    atoms
}

fn collect_transition_atoms_into<'arena>(
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
            collect_transition_atoms_into(
                then_transition,
                visited_transitions,
                visited_tests,
                atoms,
            );
            collect_transition_atoms_into(
                else_transition,
                visited_transitions,
                visited_tests,
                atoms,
            );
        }
        TransitionNode::Union(children) | TransitionNode::Intersect(children) => {
            for child in children {
                collect_transition_atoms_into(*child, visited_transitions, visited_tests, atoms);
            }
        }
        TransitionNode::Not(inner) => {
            collect_transition_atoms_into(inner, visited_transitions, visited_tests, atoms);
        }
        TransitionNode::Append { transition, .. } => {
            collect_transition_atoms_into(transition, visited_transitions, visited_tests, atoms);
        }
    }
}

/// Returns the normalized symbolic derivative of `regex`, independent of bindings and events.
fn symbolic_derivative<'arena>(
    store: &mut CanonicalStore<'arena>,
    derivatives: &mut SymbolicDerivativeCache<'arena>,
    regex: RegexId<'arena>,
) -> TransitionId<'arena> {
    // A vacant entry cannot remain borrowed while recursively deriving children from the same map.
    match derivatives.derivatives.entry(regex) {
        Entry::Occupied(entry) => return *entry.get(),
        Entry::Vacant(_) => {}
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

    *derivatives.derivatives.entry(regex).or_insert(transition)
}

/// Interprets one normalized transition under fixed candidate bindings and one history event.
fn eval_transition<'arena>(
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

fn atom_truth_assignment<'arena>(
    store: &mut CanonicalStore<'arena>,
    atoms: &[CompiledAtomPattern<'arena>],
    substitution: &CandidateSubstitution<'arena>,
    event: &Event,
) -> AtomTruthAssignment {
    AtomTruthAssignment(
        atoms
            .iter()
            .map(|atom| {
                atom.subst(substitution)
                    .is_some_and(|resolved| resolved.matches(&mut store.resolver, event))
            })
            .collect(),
    )
}

/// Instantiates one symbolic transition for an atom truth assignment.
fn instantiate_transition<'arena, 'event>(
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

    let assignment =
        atom_truth_assignment(store, derivatives.atoms(transition), substitution, event);
    let regex = match cache.values.entry((transition, assignment)) {
        Entry::Occupied(entry) => *entry.get(),
        Entry::Vacant(entry) => {
            let regex = eval_transition(store, transition, substitution, event);
            *entry.insert(regex)
        }
    };
    cache.last = Some((transition, event, regex));
    regex
}
