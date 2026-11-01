//! The breadth-first search for a counterexample.
//!
//! A search state pairs a constraint on the candidate with a residual of the runtime's
//! [`SymbolicLanguage`]. Expanding a state derives its residual once, splits the constraint and
//! builds letters from the atoms the derivative tests, and interprets the derivative under each
//! letter's truth values. A successor is discarded if its residual is `∅` or the same state was
//! inserted before. The first expanded state whose residual accepts the empty history ends the
//! search, and its parent chain yields a counterexample of minimum length.

use alloc::boxed::Box;
use alloc::vec::Vec;
use hashbrown::HashSet;
use history_semantics::SymbolicLanguage;
use junco_core::HistoryError;
use junco_core::kernel::{Primitive, RegexId, Term};
use smallvec::{SmallVec, smallvec};

use crate::constraint::{
    Atom, ConstId, Constraint, ConstraintId, ConstraintTable, Letter, Operand, Universes, steps,
};

/// Search configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct SearchOptions {
    /// Stop with [`Inclusion::Exhausted`](crate::Inclusion::Exhausted) once one search has
    /// inserted more states than this.
    pub max_items: Option<usize>,
}

/// Work done by one analysis query, summed over its inclusion searches.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct SearchStats {
    /// Inclusion searches run; policy questions split into one search per head case.
    pub searches: usize,
    /// Successor states built.
    pub generated: usize,
    /// States inserted into the visited set.
    pub inserted: usize,
    /// States expanded.
    pub expanded: usize,
    /// States discarded because their residual is empty.
    pub dead: usize,
    /// States discarded because an equal state was inserted before.
    pub repeated: usize,
    /// Letters expanded, summed over expanded states.
    pub steps: usize,
}

/// Result of one search.
pub(crate) enum SearchOutcome {
    /// No valuation satisfying the constraint admits a history in the residual.
    Holds,
    /// A counterexample exists.
    Refuted(Box<Refutation>),
    /// The search inserted more states than the budget allows.
    Exhausted,
}

/// A symbolic counterexample: any valuation satisfying `constraint`, with one event from each
/// letter in order.
pub(crate) struct Refutation {
    pub(crate) constraint: Constraint,
    pub(crate) letters: Vec<Letter>,
}

/// Searches breadth-first for a history in `language` under some valuation satisfying
/// `constraint`.
pub(crate) fn search(
    language: &mut SymbolicLanguage,
    universes: &Universes,
    constraint: Constraint,
    options: SearchOptions,
    stats: &mut SearchStats,
) -> Result<SearchOutcome, HistoryError> {
    stats.searches += 1;
    let mut search = Search {
        language,
        universes,
        options,
        stats,
        constraints: ConstraintTable::default(),
        items: Vec::new(),
        seen: HashSet::new(),
    };
    let constraint = search.constraints.intern(constraint);
    let root = search.language.root();
    search.insert(constraint, root, None);
    search.run()
}

/// Inserted search state with its parent link, for counterexample reconstruction.
#[derive(Clone, Copy)]
struct Item {
    constraint: ConstraintId,
    residual: RegexId,
    parent: Option<(usize, Letter)>,
}

struct Search<'search> {
    language: &'search mut SymbolicLanguage,
    universes: &'search Universes,
    options: SearchOptions,
    stats: &'search mut SearchStats,
    constraints: ConstraintTable,
    /// Inserted states, in insertion order, which is also the order of expansion.
    items: Vec<Item>,
    seen: HashSet<(ConstraintId, RegexId)>,
}

impl Search<'_> {
    fn run(&mut self) -> Result<SearchOutcome, HistoryError> {
        let mut next = 0;
        while next < self.items.len() {
            if self.language.nullable(self.items[next].residual)? {
                return Ok(self.counterexample(next));
            }
            if self
                .options
                .max_items
                .is_some_and(|budget| self.items.len() > budget)
            {
                return Ok(SearchOutcome::Exhausted);
            }
            self.expand(next)?;
            next += 1;
        }
        Ok(SearchOutcome::Holds)
    }

    /// Inserts the successor of the item by each step of its constraint and the atoms its
    /// derivative tests.
    fn expand(&mut self, index: usize) -> Result<(), HistoryError> {
        self.stats.expanded += 1;
        let Item {
            constraint,
            residual,
            ..
        } = self.items[index];
        let (transition, primitives) = self.language.derive(residual)?;
        let atoms = primitives
            .into_iter()
            .map(atom)
            .collect::<Result<Vec<_>, _>>()?;
        let branches = steps(self.constraints.get(constraint), &atoms, self.universes);
        for (refined, letters) in branches {
            let refined = self.constraints.intern(refined);
            for letter in letters {
                self.stats.steps += 1;
                self.stats.generated += 1;
                let successor = self
                    .language
                    .successor(transition, &truth(&atoms, &letter))?;
                self.insert(refined, successor, Some((index, letter)));
            }
        }
        Ok(())
    }

    /// Queues a state unless its residual is `∅` or the same state was inserted before.
    fn insert(
        &mut self,
        constraint: ConstraintId,
        residual: RegexId,
        parent: Option<(usize, Letter)>,
    ) {
        if self.language.is_empty(residual) {
            self.stats.dead += 1;
            return;
        }
        if !self.seen.insert((constraint, residual)) {
            self.stats.repeated += 1;
            return;
        }
        self.items.push(Item {
            constraint,
            residual,
            parent,
        });
        self.stats.inserted += 1;
    }

    fn counterexample(&self, index: usize) -> SearchOutcome {
        let constraint = self.constraints.get(self.items[index].constraint).clone();
        let mut letters = Vec::new();
        let mut current = index;
        while let Some((parent, letter)) = self.items[current].parent {
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

/// The atom of a compiled primitive. Compiled tails encode each constant as its constant id, and
/// a tail variable names the candidate's value of its own component.
fn atom(primitive: Primitive) -> Result<Atom, HistoryError> {
    let Primitive::Eq { field, term } = primitive;
    let operand = match term {
        Term::Constant(code) => Operand::Constant(
            ConstId::try_from(code)
                .map_err(|_| HistoryError::invariant("constant code is not a constant id"))?,
        ),
        Term::Variable(component) if component == field => Operand::Register,
        Term::Variable(_) => {
            return Err(HistoryError::invariant(
                "tail variable compared with another component",
            ));
        }
    };
    Ok(Atom {
        component: field.index(),
        operand,
    })
}

/// Truth words of `atoms` under `letter`: bit `i % 64` of word `i / 64` is atom `i`.
fn truth(atoms: &[Atom], letter: &Letter) -> SmallVec<[u64; 2]> {
    let mut words: SmallVec<[u64; 2]> = smallvec![0; atoms.len().div_ceil(64)];
    for (index, atom) in atoms.iter().enumerate() {
        if letter.holds(*atom) {
            words[index / 64] |= 1 << (index % 64);
        }
    }
    words
}
