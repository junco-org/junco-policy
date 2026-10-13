//! Event-independent symbolic derivatives and direct transition-DAG interpretation.

use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};
use smallbitvec::SmallBitVec;
use smallvec::SmallVec;

use crate::model::Event;

use super::component::{CandidateSubstitution, CompiledAtomPattern};
use super::evaluate::eval_test;
use super::node::{RegexId, RegexKind, TestId, TestNode, TransitionId, TransitionNode};
use super::source::Comparison;
use super::store::CanonicalStore;

/// Maximum atoms expanded into one dense minterm table.
///
/// Larger symbolic alphabets retain the direct transition-DAG fallback rather than paying
/// exponential compilation cost.
pub(super) const MAX_PRECOMPILED_ATOMS: usize = 12;
/// Global per-rule budget for eagerly compiled minterm successors.
const MAX_PRECOMPILED_MINTERMS: usize = 4_096;
/// Global per-rule budget for eagerly explored DFA states.
pub(super) const MAX_PRECOMPILED_STATES: usize = 64;

/// Dense successor table indexed by the truth values of one transition's relevant atoms.
struct CompiledMinterms<'arena, E: Event + 'arena> {
    successors: Box<[RegexId<'arena, E>]>,
}

/// Persistent event-independent derivatives, atom alphabets, and precompiled minterm tables.
pub(crate) struct SymbolicDerivativeCache<'arena, E: Event + 'arena> {
    derivatives: HashMap<RegexId<'arena, E>, TransitionId<'arena, E>>,
    atoms: HashMap<TransitionId<'arena, E>, Vec<CompiledAtomPattern<E>>>,
    minterms: HashMap<TransitionId<'arena, E>, CompiledMinterms<'arena, E>>,
}

impl<'arena, E: Event + 'arena> SymbolicDerivativeCache<'arena, E> {
    pub(crate) fn new() -> Self {
        Self {
            derivatives: HashMap::new(),
            atoms: HashMap::new(),
            minterms: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.derivatives.len()
    }

    #[cfg(test)]
    pub(crate) fn precompiled_len(&self) -> usize {
        self.minterms.len()
    }

    fn atoms(&mut self, transition: TransitionId<'arena, E>) -> &[CompiledAtomPattern<E>] {
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
struct InstantiationCache<'arena, 'event, E: Event + 'arena + 'event> {
    values: HashMap<(TransitionId<'arena, E>, AtomTruthAssignment), RegexId<'arena, E>>,
    last: Option<(TransitionId<'arena, E>, &'event E, RegexId<'arena, E>)>,
}

impl<'arena, 'event, E: Event + 'arena + 'event> InstantiationCache<'arena, 'event, E> {
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
pub(super) struct SymbolicMatcher<'state, 'arena, 'event, E: Event + 'arena + 'event> {
    store: &'state mut CanonicalStore<'arena, E>,
    derivatives: &'state mut SymbolicDerivativeCache<'arena, E>,
    instances: InstantiationCache<'arena, 'event, E>,
}

impl<'state, 'arena, 'event, E: Event + 'arena + 'event>
    SymbolicMatcher<'state, 'arena, 'event, E>
{
    /// Packages the shared canonical store and persistent derivative cache with a fresh
    /// fixed-substitution instantiation cache.
    pub(super) fn new(
        store: &'state mut CanonicalStore<'arena, E>,
        derivatives: &'state mut SymbolicDerivativeCache<'arena, E>,
    ) -> Self {
        Self {
            store,
            derivatives,
            instances: InstantiationCache::new(),
        }
    }

    /// Returns the normalized symbolic derivative of `regex`, independent of bindings and events.
    pub(super) fn derivative(&mut self, regex: RegexId<'arena, E>) -> TransitionId<'arena, E> {
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
                    .collect::<SmallVec<[TransitionId<'arena, E>; 4]>>();
                self.store.transition_union(transitions)
            }
            RegexKind::Intersect(children) => {
                let transitions = children
                    .iter()
                    .map(|child| self.derivative(*child))
                    .collect::<SmallVec<[TransitionId<'arena, E>; 4]>>();
                self.store.transition_intersect(transitions)
            }
            RegexKind::Not(inner) => {
                let transition = self.derivative(inner);
                self.store.transition_not(transition)
            }
            RegexKind::Concat(factors) => {
                let mut alternatives = SmallVec::<[TransitionId<'arena, E>; 4]>::new();
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

    /// Eagerly explores the reachable symbolic DFA and compiles small transition alphabets into
    /// dense minterm tables.
    ///
    /// The budgets make compilation predictable for wide policies. A transition that exceeds a
    /// budget remains executable through the exact transition-DAG fallback.
    pub(super) fn precompile(&mut self, root: RegexId<'arena, E>) {
        let mut pending = VecDeque::from([root]);
        let mut seen = HashSet::new();
        let mut compiled_minterms = 0;

        while seen.len() < MAX_PRECOMPILED_STATES
            && let Some(regex) = pending.pop_front()
        {
            if !seen.insert(regex) {
                continue;
            }
            let transition = self.derivative(regex);
            if matches!(*transition.get(), TransitionNode::Const(_)) {
                continue;
            }
            if let Some(compiled) = self.derivatives.minterms.get(&transition) {
                pending.extend(compiled.successors.iter().copied());
                continue;
            }

            let atoms = self.derivatives.atoms(transition).to_vec();
            if atoms.len() > MAX_PRECOMPILED_ATOMS {
                continue;
            }
            let minterm_count = 1_usize << atoms.len();
            if compiled_minterms + minterm_count > MAX_PRECOMPILED_MINTERMS {
                continue;
            }
            let successors = (0..minterm_count)
                .map(|minterm| self.evaluate_minterm(transition, &atoms, minterm))
                .collect::<Vec<_>>();
            pending.extend(successors.iter().copied());
            compiled_minterms += minterm_count;
            let previous = self.derivatives.minterms.insert(
                transition,
                CompiledMinterms {
                    successors: successors.into_boxed_slice(),
                },
            );
            debug_assert!(previous.is_none());
        }
    }

    /// Interprets one symbolic transition under a precomputed atom minterm.
    fn evaluate_minterm(
        &mut self,
        transition: TransitionId<'arena, E>,
        atoms: &[CompiledAtomPattern<E>],
        minterm: usize,
    ) -> RegexId<'arena, E> {
        match *transition.get() {
            TransitionNode::Const(regex) => regex,
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => {
                let selected = if eval_test_minterm(test, atoms, minterm) {
                    then_transition
                } else {
                    else_transition
                };
                self.evaluate_minterm(selected, atoms, minterm)
            }
            TransitionNode::Union(children) => {
                let regexes = children
                    .iter()
                    .map(|child| self.evaluate_minterm(*child, atoms, minterm))
                    .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
                self.store.regex_union(regexes)
            }
            TransitionNode::Intersect(children) => {
                let regexes = children
                    .iter()
                    .map(|child| self.evaluate_minterm(*child, atoms, minterm))
                    .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
                self.store.regex_intersect(regexes)
            }
            TransitionNode::Not(inner) => {
                let regex = self.evaluate_minterm(inner, atoms, minterm);
                self.store.regex_not(regex)
            }
            TransitionNode::Append { transition, suffix } => {
                let regex = self.evaluate_minterm(transition, atoms, minterm);
                let mut factors = SmallVec::<[RegexId<'arena, E>; 4]>::new();
                factors.push(regex);
                factors.extend_from_slice(suffix);
                self.store.regex_concat(factors)
            }
        }
    }

    /// Interprets one normalized transition under fixed candidate bindings and one history event.
    pub(super) fn evaluate(
        &mut self,
        transition: TransitionId<'arena, E>,
        substitution: &CandidateSubstitution<E>,
        event: &E,
    ) -> RegexId<'arena, E> {
        match *transition.get() {
            TransitionNode::Const(regex) => regex,
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => {
                let selected = if eval_test(test, event, substitution) {
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
                    .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
                self.store.regex_union(regexes)
            }
            TransitionNode::Intersect(children) => {
                let regexes = children
                    .iter()
                    .map(|child| self.evaluate(*child, substitution, event))
                    .collect::<SmallVec<[RegexId<'arena, E>; 4]>>();
                self.store.regex_intersect(regexes)
            }
            TransitionNode::Not(inner) => {
                let regex = self.evaluate(inner, substitution, event);
                self.store.regex_not(regex)
            }
            TransitionNode::Append { transition, suffix } => {
                let regex = self.evaluate(transition, substitution, event);
                let mut factors = SmallVec::<[RegexId<'arena, E>; 4]>::new();
                factors.push(regex);
                factors.extend_from_slice(suffix);
                self.store.regex_concat(factors)
            }
        }
    }

    fn atom_truth_assignment(
        &mut self,
        transition: TransitionId<'arena, E>,
        substitution: &CandidateSubstitution<E>,
        event: &E,
    ) -> AtomTruthAssignment {
        let atoms = self.derivatives.atoms(transition);
        AtomTruthAssignment(
            atoms
                .iter()
                .map(|atom| {
                    atom.subst(substitution)
                        .is_some_and(|resolved| resolved.matches(event))
                })
                .collect(),
        )
    }

    /// Instantiates one transition, reusing equivalent atom truth assignments.
    pub(super) fn instantiate(
        &mut self,
        transition: TransitionId<'arena, E>,
        substitution: &CandidateSubstitution<E>,
        event: &'event E,
    ) -> RegexId<'arena, E> {
        if let TransitionNode::Const(regex) = *transition.get() {
            return regex;
        }
        if let Some((previous_transition, previous_event, regex)) = self.instances.last
            && previous_transition == transition
            && previous_event == event
        {
            return regex;
        }

        if let Some(compiled) = self.derivatives.minterms.get(&transition) {
            let atoms = self
                .derivatives
                .atoms
                .get(&transition)
                .expect("precompiled transition retains its atom order");
            let minterm = atoms
                .iter()
                .enumerate()
                .fold(0_usize, |assignment, (index, atom)| {
                    let matches = atom
                        .subst(substitution)
                        .is_some_and(|resolved| resolved.matches(event));
                    assignment | (usize::from(matches) << index)
                });
            let regex = compiled.successors[minterm];
            self.instances.last = Some((transition, event, regex));
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

    /// Folds `events` from `state` using precompiled symbolic derivatives and minterm successors,
    /// returning the exact residual. The absorbing `All` and `Empty` residuals end the fold early.
    pub(super) fn residual(
        &mut self,
        mut state: RegexId<'arena, E>,
        events: impl IntoIterator<Item = &'event E>,
        substitution: &CandidateSubstitution<E>,
    ) -> RegexId<'arena, E> {
        let mut previous_derivative = None;
        for event in events {
            if state == self.store.all || state == self.store.empty {
                break;
            }
            let transition = match previous_derivative {
                Some((previous_state, transition)) if previous_state == state => transition,
                _ => self.derivative(state),
            };
            previous_derivative = Some((state, transition));
            state = self.instantiate(transition, substitution, event);
        }
        state
    }

    /// Number of distinct transition/truth-assignment successors retained in this replay.
    #[cfg(test)]
    pub(super) fn instantiation_count(&self) -> usize {
        self.instances.len()
    }
}

/// Evaluates one canonical event test from a dense atom truth assignment.
fn eval_test_minterm<'arena, E: Event + 'arena>(
    test: TestId<'arena, E>,
    atoms: &[CompiledAtomPattern<E>],
    minterm: usize,
) -> bool {
    match *test.get() {
        TestNode::True => true,
        TestNode::False => false,
        TestNode::Atom {
            comparison,
            pattern,
        } => {
            let index = atoms
                .iter()
                .position(|atom| *atom == pattern)
                .expect("compiled minterm contains every transition atom");
            let equal = minterm & (1_usize << index) != 0;
            match comparison {
                Comparison::Eq => equal,
                Comparison::Neq => !equal,
            }
        }
        TestNode::And(children) => children
            .iter()
            .all(|child| eval_test_minterm(*child, atoms, minterm)),
        TestNode::Or(children) => children
            .iter()
            .any(|child| eval_test_minterm(*child, atoms, minterm)),
    }
}

fn collect_test_atoms<'arena, E: Event + 'arena>(
    test: TestId<'arena, E>,
    visited: &mut HashSet<TestId<'arena, E>>,
    atoms: &mut Vec<CompiledAtomPattern<E>>,
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
pub(super) fn collect_transition_atoms<'arena, E: Event + 'arena>(
    transition: TransitionId<'arena, E>,
) -> Vec<CompiledAtomPattern<E>> {
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

fn collect_transition_atoms_into<'arena, E: Event + 'arena>(
    transition: TransitionId<'arena, E>,
    visited_transitions: &mut HashSet<TransitionId<'arena, E>>,
    visited_tests: &mut HashSet<TestId<'arena, E>>,
    atoms: &mut Vec<CompiledAtomPattern<E>>,
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
