//! Terms with blocks, their first atoms, and partial derivatives by letters.
//!
//! Terms are Antimirov's partial-derivative terms, except that subexpressions under intersection and
//! complement live in blocks advanced by the symbolic Brzozowski derivatives junco already computes.
//! A term is an optional block followed by a regex suffix read with blocks implicit: an `Intersect`
//! or `Not` node of the suffix becomes a block when it reaches the front.

use std::rc::Rc;

use hashbrown::{HashMap, HashSet};
use smallbitvec::SmallBitVec;
use smallvec::SmallVec;

use super::super::component::CompiledAtomPattern;
use super::super::node::{RegexId, RegexKind, TestId, TestNode};
use super::super::store::CanonicalStore;
use super::super::symbolic::{SymbolicDerivativeCache, SymbolicMatcher, eval_test_assignment};
use super::constraint::Letter;

/// Partial-derivative term: `⟨block⟩ · rest`, or just `rest` without a block.
///
/// The block marker persists even when a derivative no longer has `∩` or `¬` at its root; without
/// it, the derivatives of a block would be re-split into partial derivatives without bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Term<'arena> {
    pub(super) block: Option<RegexId<'arena>>,
    pub(super) rest: RegexId<'arena>,
}

impl<'arena> Term<'arena> {
    /// The term for a regex read with implicit blocks.
    pub(super) const fn regex(rest: RegexId<'arena>) -> Self {
        Self { block: None, rest }
    }

    /// `⟨block⟩ · rest`, identifying blocks holding `∅`, `ε` or `Σ*` with those regexes.
    ///
    /// Returns `None` for the empty language.
    pub(super) fn blocked(
        store: &mut CanonicalStore<'arena>,
        block: RegexId<'arena>,
        rest: RegexId<'arena>,
    ) -> Option<Self> {
        if block == store.empty {
            None
        } else if block == store.epsilon {
            Some(Self::regex(rest))
        } else if block == store.all {
            Some(Self::regex(store.regex_concat([block, rest])))
        } else {
            Some(Self {
                block: Some(block),
                rest,
            })
        }
    }

    /// `self · suffix`, simplifying `ε · suffix` to `suffix`.
    fn append(self, store: &mut CanonicalStore<'arena>, suffix: RegexId<'arena>) -> Self {
        if self.block.is_none() && self.rest == store.epsilon {
            Self::regex(suffix)
        } else {
            Self {
                block: self.block,
                rest: store.regex_concat([self.rest, suffix]),
            }
        }
    }

    /// Whether the term accepts the empty history.
    pub(super) fn nullable(self) -> bool {
        self.block.is_none_or(|block| block.get().nullable()) && self.rest.get().nullable()
    }

    /// Whether the term denotes the empty language.
    pub(super) fn is_empty(self, store: &CanonicalStore<'arena>) -> bool {
        self.block.is_none() && self.rest == store.empty
    }

    /// Whether the term denotes every history.
    pub(super) fn is_universal(self, store: &CanonicalStore<'arena>) -> bool {
        self.block.is_none() && self.rest == store.all
    }
}

/// Atom list shared between caches.
pub(super) type Atoms<'arena> = Rc<[CompiledAtomPattern<'arena>]>;

/// Persistent first-atom and derivative caches, valid for one canonical store.
#[derive(Default)]
pub(super) struct Derivatives<'arena> {
    symbolic: SymbolicDerivativeCache<'arena>,
    first_regex: HashMap<RegexId<'arena>, Atoms<'arena>>,
    first_term: HashMap<Term<'arena>, Atoms<'arena>>,
    partial: HashMap<(Term<'arena>, SmallBitVec), Rc<[Term<'arena>]>>,
}

impl<'arena> Derivatives<'arena> {
    /// `fst(t)`: the atoms a derivative of `term` evaluates, in first-seen order.
    pub(super) fn first(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        term: Term<'arena>,
    ) -> Atoms<'arena> {
        if let Some(atoms) = self.first_term.get(&term) {
            return atoms.clone();
        }
        let atoms = match term.block {
            Some(block) => {
                let mut atoms = self.block_first(store, block).to_vec();
                if block.get().nullable() {
                    atoms.extend(self.first_regex(store, term.rest).iter().copied());
                }
                distinct(atoms)
            }
            None => self.first_regex(store, term.rest),
        };
        self.first_term.insert(term, atoms.clone());
        atoms
    }

    /// Atoms of the symbolic derivative of a block.
    fn block_first(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        block: RegexId<'arena>,
    ) -> Atoms<'arena> {
        let transition = SymbolicMatcher::new(store, &mut self.symbolic).derivative(block);
        Rc::from(self.symbolic.atoms(transition))
    }

    fn first_regex(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        regex: RegexId<'arena>,
    ) -> Atoms<'arena> {
        if let Some(atoms) = self.first_regex.get(&regex) {
            return atoms.clone();
        }
        let atoms = match regex.get().kind {
            RegexKind::Empty | RegexKind::Epsilon | RegexKind::All => Rc::from([]),
            RegexKind::Test(test) => {
                let mut atoms = Vec::new();
                test_atoms(test, &mut atoms);
                distinct(atoms)
            }
            RegexKind::Union(children) => {
                let mut atoms = Vec::new();
                for child in children {
                    atoms.extend(self.first_regex(store, *child).iter().copied());
                }
                distinct(atoms)
            }
            RegexKind::Concat(factors) => {
                let mut atoms = Vec::new();
                for factor in factors {
                    atoms.extend(self.first_regex(store, *factor).iter().copied());
                    if !factor.get().nullable() {
                        break;
                    }
                }
                distinct(atoms)
            }
            RegexKind::Star(inner) => self.first_regex(store, inner),
            RegexKind::Intersect(_) | RegexKind::Not(_) => self.block_first(store, regex),
        };
        self.first_regex.insert(regex, atoms.clone());
        atoms
    }

    /// `∂_ℓ(term)`, sorted and deduplicated.
    pub(super) fn partial(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        term: Term<'arena>,
        letter: &Letter<'arena>,
    ) -> Rc<[Term<'arena>]> {
        let atoms = self.first(store, term);
        let key = (term, atoms.iter().map(|atom| letter.holds(*atom)).collect());
        if let Some(terms) = self.partial.get(&key) {
            return terms.clone();
        }
        let mut truth = |atom| letter.holds(atom);
        let mut terms = SmallVec::<[Term<'arena>; 4]>::new();
        match term.block {
            Some(block) => {
                let derivative = self.brzozowski(store, block, &mut truth);
                terms.extend(Term::blocked(store, derivative, term.rest));
                if block.get().nullable() {
                    self.partial_regex(store, term.rest, &mut truth, &mut terms);
                }
            }
            None => self.partial_regex(store, term.rest, &mut truth, &mut terms),
        }
        terms.sort_unstable();
        terms.dedup();
        let terms: Rc<[Term<'arena>]> = Rc::from(terms.as_slice());
        self.partial.insert(key, terms.clone());
        terms
    }

    /// Partial derivatives of a regex read with implicit blocks.
    fn partial_regex<F>(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        regex: RegexId<'arena>,
        truth: &mut F,
        terms: &mut SmallVec<[Term<'arena>; 4]>,
    ) where
        F: FnMut(CompiledAtomPattern<'arena>) -> bool,
    {
        match regex.get().kind {
            RegexKind::Empty | RegexKind::Epsilon => {}
            RegexKind::All => terms.push(Term::regex(regex)),
            RegexKind::Test(test) => {
                if eval_test_assignment(test, truth) {
                    terms.push(Term::regex(store.epsilon));
                }
            }
            RegexKind::Union(children) => {
                for child in children {
                    self.partial_regex(store, *child, truth, terms);
                }
            }
            RegexKind::Concat(factors) => {
                let mut remaining = factors;
                while let Some((factor, suffix)) = remaining.split_first() {
                    let suffix_regex = store.regex_concat(suffix.iter().copied());
                    let mut heads = SmallVec::<[Term<'arena>; 4]>::new();
                    self.partial_regex(store, *factor, truth, &mut heads);
                    for head in heads {
                        terms.push(head.append(store, suffix_regex));
                    }
                    if !factor.get().nullable() {
                        break;
                    }
                    remaining = suffix;
                }
            }
            RegexKind::Star(inner) => {
                let mut heads = SmallVec::<[Term<'arena>; 4]>::new();
                self.partial_regex(store, inner, truth, &mut heads);
                for head in heads {
                    terms.push(head.append(store, regex));
                }
            }
            RegexKind::Intersect(_) | RegexKind::Not(_) => {
                let derivative = self.brzozowski(store, regex, truth);
                let epsilon = store.epsilon;
                terms.extend(Term::blocked(store, derivative, epsilon));
            }
        }
    }

    /// `δ_ℓ(regex)`: the symbolic derivative evaluated under the letter's truth assignment.
    fn brzozowski<F>(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        regex: RegexId<'arena>,
        truth: &mut F,
    ) -> RegexId<'arena>
    where
        F: FnMut(CompiledAtomPattern<'arena>) -> bool,
    {
        let mut matcher = SymbolicMatcher::new(store, &mut self.symbolic);
        let transition = matcher.derivative(regex);
        matcher.evaluate_assignment(transition, truth)
    }
}

/// Collects the atoms of a test.
pub(super) fn test_atoms<'arena>(
    test: TestId<'arena>,
    atoms: &mut Vec<CompiledAtomPattern<'arena>>,
) {
    match *test.get() {
        TestNode::True | TestNode::False => {}
        TestNode::Atom { pattern, .. } => atoms.push(pattern),
        TestNode::And(children) | TestNode::Or(children) => {
            for child in children {
                test_atoms(*child, atoms);
            }
        }
    }
}

/// Removes repeated atoms, keeping first occurrences.
pub(super) fn distinct<'arena>(mut atoms: Vec<CompiledAtomPattern<'arena>>) -> Atoms<'arena> {
    let mut seen = HashSet::new();
    atoms.retain(|atom| seen.insert(*atom));
    Rc::from(atoms)
}
