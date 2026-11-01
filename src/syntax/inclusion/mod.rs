//! Inclusion between rule tails, uniformly over candidates, and the policy questions it answers.
//!
//! A tail may compare history events with the candidate's components, so its language depends on
//! the candidate. [`PolicyAnalyzer`] decides inclusion between such tails for every candidate that a
//! head admits, and reduces rule redundancy, policy strictness and rule vacuity to it. Every search
//! looks for a counterexample breadth-first, branching over finitely many letters per state that are
//! refined by case splits on how the candidate compares with constants. The derivative engines
//! (see [`Strategy`]) are Boolean residual formulas over a finite basis of residual states,
//! Antimirov-style partial derivatives with Brzozowski blocks under intersection and complement,
//! and plain Brzozowski derivatives of `left ∩ ¬right`. Counterexamples are concrete: a candidate
//! and a history.

mod analysis;
mod bdd;
mod constraint;
mod residual;
mod search;
mod simple;
mod simulation;
mod term;

#[cfg(test)]
mod tests;

pub use analysis::{Counterexample, Inclusion, PolicyAnalyzer, RuleId, Verdict};

/// How the search derives the two sides of an inclusion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Strategy {
    /// Boolean formulas over residual states for `left ∧ ¬right`. Intersection and complement are
    /// Boolean operations at every step; concatenation attaches its suffix to whole conjunctive
    /// cubes, so that the cube's members share one split point.
    #[default]
    Residual,
    /// Partial derivatives of the left side against macrostates of the right side, after moving
    /// top-level intersections and complements between the sides; deeper intersections and
    /// complements are blocks advanced by Brzozowski derivatives.
    Antichain,
    /// Brzozowski derivatives of `left ∩ ¬right`, which determinise both sides. A baseline.
    Brzozowski,
    /// Brzozowski derivatives of `left ∩ ¬right`, as [`Strategy::Brzozowski`], but in a syntax
    /// simplified only by local smart constructors, which keep the derivatives finite: flat,
    /// sorted, duplicate-free `∪` and `∩` without their unit, absorbing their absorber and a child
    /// beside its complement; `¬∅`, `¬Σ*` and `¬¬x`; binary concatenation without `∅` or `ε`
    /// factors; `∅*`, `ε*` and `(Σ*)*`. States are compared by identity only, so counterexamples
    /// are shortest; [`SearchOptions::subsumption`] and [`SearchOptions::prune_visited`] do not
    /// apply.
    Simple,
}

/// How visited states are compared beyond exact equality.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Subsumption {
    /// Syntactic identity: equal residual formulas, or the antichain order on partial-derivative
    /// states.
    Identity,
    /// Sufficient conditions for language inclusion: propositional implication between residual
    /// formulas, or a syntactic simulation between partial-derivative terms.
    #[default]
    Implication,
}

/// How each search state's finite alphabet is built.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Alphabet {
    /// One letter per satisfiable class of events, built directly.
    #[default]
    Letters,
    /// The same letters, found by enumerating every truth assignment to the state's atoms. A
    /// baseline whose cost is exponential in the number of atoms.
    Minterms,
}

/// Search configuration. The default is the residual strategy with implication coverage and
/// letters, without pruning or a budget.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct SearchOptions {
    /// How the two sides are derived.
    pub strategy: Strategy,
    /// How visited states are compared, and for partial-derivative states, which obligations are
    /// dead or redundant; ignored by the simple strategy.
    pub subsumption: Subsumption,
    /// Also remove visited states that a newly inserted state subsumes; ignored by the residual
    /// and simple strategies, which keep every inserted state. Counterexamples are then no longer
    /// guaranteed to be shortest.
    pub prune_visited: bool,
    /// How letters are built.
    pub alphabet: Alphabet,
    /// Stop with [`Inclusion::Exhausted`] once one search has inserted more states than this.
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
    /// States discarded because they have no witnesses.
    pub dead: usize,
    /// States discarded because an equal state was inserted before.
    pub repeated: usize,
    /// States discarded because a visited state subsumes them.
    pub subsumed: usize,
    /// Visited states removed because a newly inserted state subsumes them.
    pub pruned: usize,
    /// Letters expanded, summed over expanded states.
    pub steps: usize,
    /// Truth assignments to the atoms of expanded states (`2^|atoms|`, saturating): the alphabet a
    /// minterm enumeration would range over.
    pub assignments: u64,
}
