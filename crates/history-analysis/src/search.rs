//! The breadth-first search for a counterexample.
//!
//! A search state pairs a constraint on the candidate with a normal-form residual. Expanding a
//! state derives its residual once per step of its constraint and first atoms; a successor is
//! discarded if its residual is `∅` or the same state was inserted before. The first expanded
//! state whose residual accepts the empty history ends the search, and its parent chain yields a
//! counterexample of minimum length.

use alloc::boxed::Box;
use alloc::vec::Vec;
use hashbrown::HashSet;

use crate::constraint::{Constraint, ConstraintId, ConstraintTable, Letter, Universes, steps};
use crate::expression::{ExprId, Expressions};

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

/// Searches breadth-first for a history in `residual` under some valuation satisfying
/// `constraint`.
pub(crate) fn search(
    expressions: &mut Expressions,
    universes: &Universes,
    constraint: Constraint,
    residual: ExprId,
    options: SearchOptions,
    stats: &mut SearchStats,
) -> SearchOutcome {
    stats.searches += 1;
    let mut search = Search {
        expressions,
        universes,
        options,
        stats,
        constraints: ConstraintTable::default(),
        items: Vec::new(),
        seen: HashSet::new(),
    };
    let constraint = search.constraints.intern(constraint);
    search.insert(constraint, residual, None);
    search.run()
}

/// Inserted search state with its parent link, for counterexample reconstruction.
#[derive(Clone, Copy)]
struct Item {
    constraint: ConstraintId,
    residual: ExprId,
    parent: Option<(usize, Letter)>,
}

struct Search<'search> {
    expressions: &'search mut Expressions,
    universes: &'search Universes,
    options: SearchOptions,
    stats: &'search mut SearchStats,
    constraints: ConstraintTable,
    /// Inserted states, in insertion order, which is also the order of expansion.
    items: Vec<Item>,
    seen: HashSet<(ConstraintId, ExprId)>,
}

impl Search<'_> {
    fn run(&mut self) -> SearchOutcome {
        let mut next = 0;
        while next < self.items.len() {
            if self.expressions.nullable(self.items[next].residual) {
                return self.counterexample(next);
            }
            if self
                .options
                .max_items
                .is_some_and(|budget| self.items.len() > budget)
            {
                return SearchOutcome::Exhausted;
            }
            self.expand(next);
            next += 1;
        }
        SearchOutcome::Holds
    }

    /// Inserts the derivative of the item by each step of its constraint and first atoms.
    fn expand(&mut self, index: usize) {
        self.stats.expanded += 1;
        let Item {
            constraint,
            residual,
            ..
        } = self.items[index];
        let branches = steps(
            self.constraints.get(constraint),
            self.expressions.first(residual),
            self.universes,
        );
        for (refined, letters) in branches {
            let refined = self.constraints.intern(refined);
            for letter in letters {
                self.stats.steps += 1;
                self.stats.generated += 1;
                let successor = self.expressions.derive(residual, &letter);
                self.insert(refined, successor, Some((index, letter)));
            }
        }
    }

    /// Queues a state unless its residual is `∅` or the same state was inserted before.
    fn insert(
        &mut self,
        constraint: ConstraintId,
        residual: ExprId,
        parent: Option<(usize, Letter)>,
    ) {
        if residual == ExprId::EMPTY {
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
