//! Event-independent symbolic derivatives and direct transition-DAG interpretation.

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

    /// Returns the normalized symbolic derivative of `regex`, independent of bindings and events.
    pub(super) fn derivative(&mut self, regex: RegexId<'arena>) -> TransitionId<'arena> {
        if let Some(transition) = self.derivatives.derivatives.get(&regex) {
            return *transition;
        }

        let transition = match regex.get().kind {
            RegexKind::Empty | RegexKind::Epsilon => self.store.transition_empty,
            RegexKind::All => self.store.transition_all,
            RegexKind::Test(test) => self.store.transition_if(
                test,
                self.store.transition_epsilon,
                self.store.transition_empty,
            ),
            RegexKind::Union(children) => {
                let transitions = children
                    .iter()
                    .map(|child| self.derivative(*child))
                    .collect::<SmallVec<[TransitionId<'arena>; 4]>>();
                self.store.transition_union(transitions)
            }
            RegexKind::Intersect(children) => {
                let transitions = children
                    .iter()
                    .map(|child| self.derivative(*child))
                    .collect::<SmallVec<[TransitionId<'arena>; 4]>>();
                self.store.transition_intersect(transitions)
            }
            RegexKind::Not(inner) => {
                let transition = self.derivative(inner);
                self.store.transition_not(transition)
            }
            RegexKind::Concat(factors) => {
                let mut alternatives = SmallVec::<[TransitionId<'arena>; 4]>::new();
                let mut remaining = factors;
                while let Some((factor, suffix)) = remaining.split_first() {
                    let transition = self.derivative(*factor);
                    alternatives.push(self.store.transition_append(transition, suffix));
                    if !self.store.nullable(*factor) {
                        break;
                    }
                    remaining = suffix;
                }
                self.store.transition_union(alternatives)
            }
            RegexKind::Star(inner) => {
                let transition = self.derivative(inner);
                self.store.transition_append(transition, &[regex])
            }
        };

        let previous = self.derivatives.derivatives.insert(regex, transition);
        debug_assert!(previous.is_none());
        transition
    }

    /// Interprets one normalized transition under fixed candidate bindings and one history event.
    pub(super) fn evaluate(
        &mut self,
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
                let selected = if eval_test(test, event, substitution, &mut self.store.resolver) {
                    then_transition
                } else {
                    else_transition
                };
                self.evaluate(selected, substitution, event)
            }
            TransitionNode::Union(children) => {
                let regexes = children
                    .iter()
                    .map(|child| self.evaluate(*child, substitution, event))
                    .collect::<SmallVec<[RegexId<'arena>; 4]>>();
                self.store.regex_union(regexes)
            }
            TransitionNode::Intersect(children) => {
                let regexes = children
                    .iter()
                    .map(|child| self.evaluate(*child, substitution, event))
                    .collect::<SmallVec<[RegexId<'arena>; 4]>>();
                self.store.regex_intersect(regexes)
            }
            TransitionNode::Not(inner) => {
                let regex = self.evaluate(inner, substitution, event);
                self.store.regex_not(regex)
            }
            TransitionNode::Append { transition, suffix } => {
                let regex = self.evaluate(transition, substitution, event);
                let mut factors = SmallVec::<[RegexId<'arena>; 4]>::new();
                factors.push(regex);
                factors.extend_from_slice(suffix);
                self.store.regex_concat(factors)
            }
        }
    }

    fn atom_truth_assignment(
        &mut self,
        transition: TransitionId<'arena>,
        substitution: &CandidateSubstitution<'arena>,
        event: &Event,
    ) -> AtomTruthAssignment {
        let atoms = self.derivatives.atoms(transition);
        let resolver = &mut self.store.resolver;
        AtomTruthAssignment(
            atoms
                .iter()
                .map(|atom| {
                    atom.subst(substitution)
                        .is_some_and(|resolved| resolved.matches(resolver, event))
                })
                .collect(),
        )
    }

    /// Instantiates one transition, reusing equivalent atom truth assignments.
    pub(super) fn instantiate(
        &mut self,
        transition: TransitionId<'arena>,
        substitution: &CandidateSubstitution<'arena>,
        event: &'event Event,
    ) -> RegexId<'arena> {
        if let Some((previous_transition, previous_event, regex)) = self.instances.last
            && previous_transition == transition
            && previous_event == event
        {
            return regex;
        }

        let assignment = self.atom_truth_assignment(transition, substitution, event);
        let key = (transition, assignment);
        let regex = if let Some(regex) = self.instances.values.get(&key) {
            *regex
        } else {
            let regex = self.evaluate(transition, substitution, event);
            let previous = self.instances.values.insert(key, regex);
            debug_assert!(previous.is_none());
            regex
        };
        self.instances.last = Some((transition, event, regex));
        regex
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
