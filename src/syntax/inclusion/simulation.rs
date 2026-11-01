//! Syntactic simulation between terms: a sound under-approximation of language inclusion that
//! strengthens dead-item detection, reduction and subsumption.

use hashbrown::HashMap;
use smallvec::SmallVec;

use super::super::node::{RegexId, RegexKind, TestId};
use super::super::symbolic::eval_test_assignment;
use super::Alphabet;
use super::constraint::{Constraint, steps};
use super::term::{Term, test_atoms};

/// Memoised simulation relation; valid for one canonical store.
#[derive(Default)]
pub(super) struct Simulation<'arena> {
    terms: HashMap<(Term<'arena>, Term<'arena>), bool>,
    regexes: HashMap<(RegexId<'arena>, RegexId<'arena>), bool>,
    tests: HashMap<(TestId<'arena>, TestId<'arena>), bool>,
}

type Factors<'arena> = SmallVec<[RegexId<'arena>; 4]>;

/// Concatenation factors of a regex; `ε` has none.
fn factors(regex: RegexId<'_>) -> Factors<'_> {
    match regex.get().kind {
        RegexKind::Concat(factors) => SmallVec::from_slice(factors),
        RegexKind::Epsilon => SmallVec::new(),
        _ => SmallVec::from_elem(regex, 1),
    }
}

fn is_all(regex: RegexId<'_>) -> bool {
    matches!(regex.get().kind, RegexKind::All)
}

impl<'arena> Simulation<'arena> {
    /// Whether `left ⪯ right`, which implies that `left`'s language is included in `right`'s under
    /// every valuation. Block markers are irrelevant to languages and ignored.
    pub(super) fn term_le(&mut self, left: Term<'arena>, right: Term<'arena>) -> bool {
        if left == right {
            return true;
        }
        if let Some(result) = self.terms.get(&(left, right)) {
            return *result;
        }
        let mut left_factors = left.block.into_iter().collect::<Factors<'arena>>();
        left_factors.extend(factors(left.rest));
        let mut right_factors = right.block.into_iter().collect::<Factors<'arena>>();
        right_factors.extend(factors(right.rest));
        let result = self.sequence_le(&left_factors, &right_factors);
        self.terms.insert((left, right), result);
        result
    }

    /// Simulation between concatenations of factors.
    fn sequence_le(&mut self, left: &[RegexId<'arena>], right: &[RegexId<'arena>]) -> bool {
        if left == right {
            return true;
        }
        if let [only] = right
            && is_all(*only)
        {
            return true;
        }
        if let [only] = left
            && matches!(only.get().kind, RegexKind::Empty)
        {
            return true;
        }
        if left.is_empty() {
            return right.iter().all(|factor| factor.get().nullable());
        }
        if right.is_empty() {
            return false;
        }
        if let ([left], [right]) = (left, right) {
            return self.le(*left, *right);
        }
        // t ⪯ Σ*·u and t ⪯ u·Σ* if t ⪯ u.
        if is_all(right[0]) && self.sequence_le(left, &right[1..]) {
            return true;
        }
        if let Some((last, init)) = right.split_last()
            && is_all(*last)
            && self.sequence_le(left, init)
        {
            return true;
        }
        // t·t' ⪯ u·u' if t ⪯ u and t' ⪯ u'.
        if self.le(left[0], right[0]) && self.sequence_le(&left[1..], &right[1..]) {
            return true;
        }
        if let [only] = right {
            match only.get().kind {
                RegexKind::Star(inner) => return self.sequence_le(left, &factors(inner)),
                RegexKind::Union(children) => {
                    return children
                        .iter()
                        .any(|child| self.sequence_le(left, &factors(*child)));
                }
                _ => {}
            }
        }
        if let [only] = left
            && let RegexKind::Union(children) = only.get().kind
        {
            return children
                .iter()
                .all(|child| self.sequence_le(&factors(*child), right));
        }
        false
    }

    /// Simulation between single regexes.
    fn le(&mut self, left: RegexId<'arena>, right: RegexId<'arena>) -> bool {
        if left == right || is_all(right) || matches!(left.get().kind, RegexKind::Empty) {
            return true;
        }
        if matches!(left.get().kind, RegexKind::Epsilon) {
            return right.get().nullable();
        }
        if let Some(result) = self.regexes.get(&(left, right)) {
            return *result;
        }
        let result = match (left.get().kind, right.get().kind) {
            (RegexKind::Union(children), _) => children.iter().all(|child| self.le(*child, right)),
            (_, RegexKind::Union(children)) => children.iter().any(|child| self.le(left, *child)),
            (RegexKind::Intersect(children), RegexKind::Intersect(others)) => {
                children.iter().any(|child| self.le(*child, right))
                    || others.iter().all(|other| self.le(left, *other))
            }
            (RegexKind::Intersect(children), _) => {
                children.iter().any(|child| self.le(*child, right))
            }
            (_, RegexKind::Intersect(others)) => others.iter().all(|other| self.le(left, *other)),
            (RegexKind::Test(left), RegexKind::Test(right)) => self.test_le(left, right),
            (RegexKind::Concat(left), RegexKind::Concat(right)) => self.sequence_le(left, right),
            (RegexKind::Concat(left), _) => self.sequence_le(left, &[right]),
            (_, RegexKind::Concat(right)) => self.sequence_le(&[left], right),
            (RegexKind::Star(inner), RegexKind::Star(_)) => self.le(inner, right),
            (_, RegexKind::Star(inner)) => self.le(left, inner),
            (RegexKind::Not(left), RegexKind::Not(right)) => self.le(right, left),
            _ => false,
        };
        self.regexes.insert((left, right), result);
        result
    }

    /// Exact test implication under every valuation, decided by the letters of both tests' atoms.
    fn test_le(&mut self, left: TestId<'arena>, right: TestId<'arena>) -> bool {
        if let Some(result) = self.tests.get(&(left, right)) {
            return *result;
        }
        let mut atoms = Vec::new();
        test_atoms(left, &mut atoms);
        test_atoms(right, &mut atoms);
        let atoms = super::term::distinct(atoms);
        let result = steps(&Constraint::unconstrained(), &atoms, Alphabet::Letters)
            .iter()
            .flat_map(|(_, letters)| letters)
            .all(|letter| {
                let mut truth = |atom| letter.holds(atom);
                !eval_test_assignment(left, &mut truth) || eval_test_assignment(right, &mut truth)
            });
        self.tests.insert((left, right), result);
        result
    }
}
