//! The breadth-first search for a counterexample.
//!
//! A search state pairs a constraint on the candidate with a residual of the runtime's
//! [`SymbolicLanguage`]. Expanding a state derives its residual once, splits the constraint and
//! builds letters from the atoms the derivative tests, and interprets the derivative under each
//! letter's truth values. A successor is discarded if its residual is `∅` or dead, if the same
//! state was inserted before, or if an inserted state subsumes it (see [`crate::prune`]). The
//! first expanded state whose residual accepts the empty history ends the search, and its parent
//! chain yields a counterexample of minimum length.

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
use crate::prune::{Antichain, Decomposition};
use crate::simulation::Simulation;

/// Result of one search.
pub(crate) enum SearchOutcome {
    /// No valuation satisfying the constraint admits a history in the residual.
    Holds,
    /// A counterexample exists.
    Refuted(Box<Refutation>),
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
) -> Result<SearchOutcome, HistoryError> {
    let mut search = Search {
        language,
        universes,
        constraints: ConstraintTable::default(),
        items: Vec::new(),
        seen: HashSet::new(),
        antichain: Antichain::default(),
        simulation: Simulation::default(),
    };
    let constraint = search.constraints.intern(constraint);
    let root = search.language.root();
    search.insert(constraint, root, None)?;
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
    constraints: ConstraintTable,
    /// Inserted states, in insertion order, which is also the order of expansion.
    items: Vec<Item>,
    seen: HashSet<(ConstraintId, RegexId)>,
    /// Inserted states, for subsumption.
    antichain: Antichain,
    /// Simulation between the language's residuals, for the dead test and subsumption.
    simulation: Simulation,
}

impl Search<'_> {
    fn run(&mut self) -> Result<SearchOutcome, HistoryError> {
        let mut next = 0;
        while next < self.items.len() {
            if self.language.nullable(self.items[next].residual)? {
                return Ok(self.counterexample(next));
            }
            self.expand(next)?;
            next += 1;
        }
        Ok(SearchOutcome::Holds)
    }

    /// Inserts the successor of the item by each step of its constraint and the atoms its
    /// derivative tests.
    fn expand(&mut self, index: usize) -> Result<(), HistoryError> {
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
                let successor = self
                    .language
                    .successor(transition, &truth(&atoms, &letter))?;
                self.insert(refined, successor, Some((index, letter)))?;
            }
        }
        Ok(())
    }

    /// Queues a state unless its residual is `∅` or dead, the same state was inserted before, or
    /// an inserted state subsumes it.
    fn insert(
        &mut self,
        constraint: ConstraintId,
        residual: RegexId,
        parent: Option<(usize, Letter)>,
    ) -> Result<(), HistoryError> {
        if self.language.is_empty(residual) {
            return Ok(());
        }
        if !self.seen.insert((constraint, residual)) {
            return Ok(());
        }
        let state = Decomposition::of(self.language, residual)?;
        if state.dead(self.language, &mut self.simulation)? {
            return Ok(());
        }
        if self.antichain.subsumes(
            self.language,
            &mut self.simulation,
            &self.constraints,
            constraint,
            &state,
        )? {
            return Ok(());
        }
        self.antichain.insert(constraint, state);
        self.items.push(Item {
            constraint,
            residual,
            parent,
        });
        Ok(())
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
