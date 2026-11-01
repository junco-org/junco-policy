//! Boolean residual formulas over a finite basis of residual states, and the inclusion search over
//! them.
//!
//! A residual state denotes a language: `{ε}`, the one-event histories of a test, `u*`, or a
//! continuation `[C; t]` whose histories split into a prefix in the cube `C` and a suffix in `t`.
//! A search item pairs a constraint with a canonical Boolean formula over states. Deriving a formula
//! by a letter substitutes every state's derivative simultaneously, so intersection and complement
//! are Boolean operations at every step. A continuation attaches its suffix to a whole cube: the
//! cube's members must accept the same prefix, which `(u ∩ v)·t ≠ u·t ∩ v·t` requires.

use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};
use smallbitvec::SmallBitVec;

use super::super::component::CompiledAtomPattern;
use super::super::node::{RegexId, RegexKind, TestId};
use super::super::store::CanonicalStore;
use super::super::symbolic::eval_test_assignment;
use super::bdd::{Bdd, FALSE, Formula, TRUE};
use super::constraint::{Constraint, ConstraintId, ConstraintTable, Letter, steps};
use super::search::{Refutation, SearchOutcome};
use super::term::{Atoms, distinct, test_atoms};
use super::{SearchOptions, SearchStats, Subsumption};

/// Literal of a cube: a state variable and its polarity.
type Literal = (u32, bool);

/// Identity of a residual state.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StateKey<'arena> {
    /// `{ε}`.
    Epsilon,
    /// The one-event histories satisfying a test.
    Test(TestId<'arena>),
    /// `u*`, keyed by the star regex.
    Star(RegexId<'arena>),
    /// `[C; t]`: a prefix in cube `C`, then a suffix in regex `t`.
    Continuation(Box<[Literal]>, RegexId<'arena>),
}

struct State<'arena> {
    key: StateKey<'arena>,
    /// Whether the state's language contains `ε`.
    nullable: bool,
    /// Atoms that the state's derivative evaluates.
    first: Atoms<'arena>,
}

/// Interned states, formulas, and their derivatives; valid for one canonical store.
#[derive(Default)]
pub(super) struct Residuals<'arena> {
    bdd: Bdd,
    states: Vec<State<'arena>>,
    ids: HashMap<StateKey<'arena>, u32>,
    initial: HashMap<RegexId<'arena>, Formula>,
    transitions: HashMap<(u32, SmallBitVec), Formula>,
    nullable: HashMap<Formula, bool>,
    first: HashMap<Formula, Atoms<'arena>>,
}

/// Inserted item with its parent link for counterexample reconstruction.
struct Node<'arena> {
    constraint: ConstraintId,
    formula: Formula,
    parent: Option<(usize, Letter<'arena>)>,
}

impl<'arena> Residuals<'arena> {
    /// The variable of the state with `key`, interning the state on first use.
    fn state(&mut self, store: &mut CanonicalStore<'arena>, key: StateKey<'arena>) -> u32 {
        if let Some(id) = self.ids.get(&key) {
            return *id;
        }
        let (nullable, first) = match &key {
            StateKey::Epsilon => (true, distinct(Vec::new())),
            StateKey::Test(test) => {
                let mut atoms = Vec::new();
                test_atoms(*test, &mut atoms);
                (false, distinct(atoms))
            }
            StateKey::Star(star) => {
                let RegexKind::Star(inner) = star.get().kind else {
                    unreachable!("star states are keyed by star regexes");
                };
                let inner = self.initial(store, inner);
                (true, self.formula_first(inner))
            }
            StateKey::Continuation(cube, suffix) => {
                let cube_nullable = self.cube_nullable(cube);
                let suffix = self.initial(store, *suffix);
                let mut atoms = self.cube_first(cube);
                if cube_nullable {
                    atoms.extend(self.formula_first(suffix).iter().copied());
                }
                (
                    cube_nullable && self.formula_nullable(suffix),
                    distinct(atoms),
                )
            }
        };
        let id = u32::try_from(self.states.len()).expect("state ids fit in u32");
        self.states.push(State {
            key: key.clone(),
            nullable,
            first,
        });
        self.ids.insert(key, id);
        id
    }

    fn state_formula(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        key: StateKey<'arena>,
    ) -> Formula {
        let state = self.state(store, key);
        self.bdd.variable(state)
    }

    /// `ι_r`: the formula denoting `r`.
    fn initial(&mut self, store: &mut CanonicalStore<'arena>, regex: RegexId<'arena>) -> Formula {
        if let Some(formula) = self.initial.get(&regex) {
            return *formula;
        }
        let formula = match regex.get().kind {
            RegexKind::Empty => FALSE,
            RegexKind::All => TRUE,
            RegexKind::Epsilon => self.state_formula(store, StateKey::Epsilon),
            RegexKind::Test(test) => self.state_formula(store, StateKey::Test(test)),
            RegexKind::Union(children) => children.iter().fold(FALSE, |formula, child| {
                let child = self.initial(store, *child);
                self.bdd.or(formula, child)
            }),
            RegexKind::Intersect(children) => children.iter().fold(TRUE, |formula, child| {
                let child = self.initial(store, *child);
                self.bdd.and(formula, child)
            }),
            RegexKind::Not(inner) => {
                let inner = self.initial(store, inner);
                self.bdd.not(inner)
            }
            RegexKind::Concat(factors) => {
                let (head, suffix) = factors.split_first().expect("concatenations have factors");
                let head = self.initial(store, *head);
                let suffix = store.regex_concat(suffix.iter().copied());
                self.push(store, head, suffix)
            }
            RegexKind::Star(_) => self.state_formula(store, StateKey::Star(regex)),
        };
        self.initial.insert(regex, formula);
        formula
    }

    /// `push_t(F)`: the disjunction of `[C; t]` over the cubes `C` of `F`'s cover.
    fn push(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        formula: Formula,
        suffix: RegexId<'arena>,
    ) -> Formula {
        let mut result = FALSE;
        for cube in self.bdd.cover(formula) {
            let continuation = self.state_formula(store, StateKey::Continuation(cube, suffix));
            result = self.bdd.or(result, continuation);
        }
        result
    }

    fn cube_nullable(&self, cube: &[Literal]) -> bool {
        cube.iter()
            .all(|(state, polarity)| self.states[*state as usize].nullable == *polarity)
    }

    fn cube_first(&self, cube: &[Literal]) -> Vec<CompiledAtomPattern<'arena>> {
        cube.iter()
            .flat_map(|(state, _)| self.states[*state as usize].first.iter().copied())
            .collect()
    }

    /// Whether the formula's language contains `ε`.
    fn formula_nullable(&mut self, formula: Formula) -> bool {
        if let Some(nullable) = self.nullable.get(&formula) {
            return *nullable;
        }
        let states = &self.states;
        let nullable = self
            .bdd
            .evaluate(formula, |state| states[state as usize].nullable);
        self.nullable.insert(formula, nullable);
        nullable
    }

    /// `fst(F)`: the atoms that the derivatives of the formula's states evaluate.
    fn formula_first(&mut self, formula: Formula) -> Atoms<'arena> {
        if let Some(atoms) = self.first.get(&formula) {
            return atoms.clone();
        }
        let atoms = distinct(
            self.bdd
                .support(formula)
                .into_iter()
                .flat_map(|state| self.states[state as usize].first.iter().copied())
                .collect(),
        );
        self.first.insert(formula, atoms.clone());
        atoms
    }

    /// `D_ℓ q` for the state `q`.
    fn transition(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        state: u32,
        letter: &Letter<'arena>,
    ) -> Formula {
        let key = (
            state,
            self.states[state as usize]
                .first
                .iter()
                .map(|atom| letter.holds(*atom))
                .collect::<SmallBitVec>(),
        );
        if let Some(formula) = self.transitions.get(&key) {
            return *formula;
        }
        let formula = match self.states[state as usize].key.clone() {
            StateKey::Epsilon => FALSE,
            StateKey::Test(test) => {
                if eval_test_assignment(test, &mut |atom| letter.holds(atom)) {
                    self.state_formula(store, StateKey::Epsilon)
                } else {
                    FALSE
                }
            }
            StateKey::Star(star) => {
                let RegexKind::Star(inner) = star.get().kind else {
                    unreachable!("star states are keyed by star regexes");
                };
                let inner = self.initial(store, inner);
                let derivative = self.derive(store, inner, letter);
                self.push(store, derivative, star)
            }
            StateKey::Continuation(cube, suffix) => {
                let mut prefix = TRUE;
                for (state, polarity) in cube.iter() {
                    let mut derivative = self.transition(store, *state, letter);
                    if !polarity {
                        derivative = self.bdd.not(derivative);
                    }
                    prefix = self.bdd.and(prefix, derivative);
                }
                let mut formula = self.push(store, prefix, suffix);
                if self.cube_nullable(&cube) {
                    let suffix = self.initial(store, suffix);
                    let started = self.derive(store, suffix, letter);
                    formula = self.bdd.or(formula, started);
                }
                formula
            }
        };
        self.transitions.insert(key, formula);
        formula
    }

    /// `D_ℓ F`: simultaneous substitution of every state's derivative.
    fn derive(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        formula: Formula,
        letter: &Letter<'arena>,
    ) -> Formula {
        let substitution = self
            .bdd
            .support(formula)
            .into_iter()
            .map(|state| (state, self.transition(store, state, letter)))
            .collect::<HashMap<_, _>>();
        self.bdd.compose(formula, &substitution)
    }

    /// Decides `left ⊑_constraint right` by breadth-first search from `ι_left ∧ ¬ι_right`.
    pub(super) fn includes(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        constraint: Constraint<'arena>,
        left: RegexId<'arena>,
        right: RegexId<'arena>,
        options: SearchOptions,
        stats: &mut SearchStats,
    ) -> SearchOutcome<'arena> {
        let left = self.initial(store, left);
        let right = self.initial(store, right);
        let excluded = self.bdd.not(right);
        let formula = self.bdd.and(left, excluded);
        if formula == FALSE {
            stats.dead += 1;
            return SearchOutcome::Holds;
        }
        let mut search = Search {
            residuals: self,
            store,
            options,
            stats,
            constraints: ConstraintTable::default(),
            nodes: Vec::new(),
            seen: HashSet::new(),
            groups: HashMap::new(),
            queue: VecDeque::new(),
        };
        let constraint = search.constraints.intern(constraint);
        search.insert(constraint, formula, None);
        search.run()
    }
}

struct Search<'search, 'arena> {
    residuals: &'search mut Residuals<'arena>,
    store: &'search mut CanonicalStore<'arena>,
    options: SearchOptions,
    stats: &'search mut SearchStats,
    constraints: ConstraintTable<'arena>,
    nodes: Vec<Node<'arena>>,
    seen: HashSet<(ConstraintId, Formula)>,
    /// Inserted formulas by constraint, for implication coverage.
    groups: HashMap<ConstraintId, Vec<Formula>>,
    queue: VecDeque<usize>,
}

impl<'arena> Search<'_, 'arena> {
    fn run(&mut self) -> SearchOutcome<'arena> {
        while let Some(index) = self.queue.pop_front() {
            let formula = self.nodes[index].formula;
            if self.residuals.formula_nullable(formula) {
                return self.counterexample(index);
            }
            if self
                .options
                .max_items
                .is_some_and(|budget| self.nodes.len() > budget)
            {
                return SearchOutcome::Exhausted;
            }
            self.expand(index);
        }
        SearchOutcome::Holds
    }

    fn expand(&mut self, index: usize) {
        self.stats.expanded += 1;
        let Node {
            constraint,
            formula,
            ..
        } = self.nodes[index];
        let atoms = self.residuals.formula_first(formula);
        self.stats.assignments = self
            .stats
            .assignments
            .saturating_add(1_u64.checked_shl(atoms.len() as u32).unwrap_or(u64::MAX));
        let current = self.constraints.get(constraint).clone();
        for (refined, letters) in steps(&current, &atoms, self.options.alphabet) {
            let refined = self.constraints.intern(refined);
            for letter in letters {
                self.stats.steps += 1;
                self.stats.generated += 1;
                let successor = self.residuals.derive(self.store, formula, &letter);
                if successor == FALSE {
                    self.stats.dead += 1;
                    continue;
                }
                self.insert(refined, successor, Some((index, letter)));
            }
        }
    }

    fn insert(
        &mut self,
        constraint: ConstraintId,
        formula: Formula,
        parent: Option<(usize, Letter<'arena>)>,
    ) {
        if !self.seen.insert((constraint, formula)) {
            self.stats.repeated += 1;
            return;
        }
        if self.options.subsumption == Subsumption::Implication {
            let residuals = &mut *self.residuals;
            let constraints = &mut self.constraints;
            let covered = self.groups.iter().any(|(other, formulas)| {
                constraints.entails(constraint, *other)
                    && formulas
                        .iter()
                        .any(|covering| residuals.bdd.implies(formula, *covering))
            });
            if covered {
                self.stats.subsumed += 1;
                return;
            }
        }
        self.groups.entry(constraint).or_default().push(formula);
        self.nodes.push(Node {
            constraint,
            formula,
            parent,
        });
        self.queue.push_back(self.nodes.len() - 1);
        self.stats.inserted += 1;
    }

    fn counterexample(&self, index: usize) -> SearchOutcome<'arena> {
        let constraint = self.constraints.get(self.nodes[index].constraint).clone();
        let mut letters = Vec::new();
        let mut current = index;
        while let Some((parent, letter)) = self.nodes[current].parent {
            letters.push(letter);
            current = parent;
        }
        letters.reverse();
        SearchOutcome::Refuted(Box::new(Refutation {
            constraint,
            letters,
        }))
    }
}
