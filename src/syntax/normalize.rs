//! Smart constructors for canonical test and regex DAGs.
//!
//! The constructors implement `Norm_B` and `Norm` from `symbolic-matcher.tex`: flattened ACI
//! Boolean operators, absorption and contradiction reductions, flattened regex set operators,
//! ordered concatenation, cross-layer test reductions, and cached nullability.

use smallvec::SmallVec;

use super::component::CompiledAtomPattern;
use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};
use super::source::{Comparison, ComponentPattern};
use super::store::CanonicalStore;
/// Returns whether any unordered pair satisfies `predicate`.
///
/// # Preconditions
/// `predicate` must be symmetric; each pair is presented in only one orientation.
fn pair_satisfies<T: Copy>(values: &[T], mut predicate: impl FnMut(T, T) -> bool) -> bool {
    values.iter().enumerate().any(|(index, left)| {
        values[index + 1..]
            .iter()
            .any(|right| predicate(*left, *right))
    })
}

/// Recognizes an equality atom and its disequality complement.
///
/// # Preconditions
/// Both IDs must be canonical tests from the same [`CanonicalStore`].
fn complementary_test<'arena>(left: TestId<'arena>, right: TestId<'arena>) -> bool {
    matches!(
        (*left.get(), *right.get()),
        (
            TestNode::Atom {
                comparison: left_comparison,
                pattern: left_pattern,
            },
            TestNode::Atom {
                comparison: right_comparison,
                pattern: right_pattern,
            },
        ) if left_comparison != right_comparison && left_pattern == right_pattern
    )
}

/// Recognizes distinct constants in the same component domain.
///
/// # Preconditions
/// Both patterns must have been compiled by the same [`CanonicalStore`].
fn distinct_constant_patterns(
    left: CompiledAtomPattern<'_>,
    right: CompiledAtomPattern<'_>,
) -> bool {
    match (left, right) {
        (
            CompiledAtomPattern::Principal(ComponentPattern::Constant(left)),
            CompiledAtomPattern::Principal(ComponentPattern::Constant(right)),
        ) => left != right,
        (
            CompiledAtomPattern::Action(ComponentPattern::Constant(left)),
            CompiledAtomPattern::Action(ComponentPattern::Constant(right)),
        ) => left != right,
        (
            CompiledAtomPattern::Resource(ComponentPattern::Constant(left)),
            CompiledAtomPattern::Resource(ComponentPattern::Constant(right)),
        ) => left != right,
        _ => false,
    }
}

/// Recognizes two distinct constant atoms with the requested comparison.
///
/// # Preconditions
/// Both IDs must be canonical tests from the same [`CanonicalStore`].
fn distinct_constant_atoms(left: TestId<'_>, right: TestId<'_>, comparison: Comparison) -> bool {
    matches!(
        (*left.get(), *right.get()),
        (
            TestNode::Atom {
                comparison: left_comparison,
                pattern: left_pattern,
            },
            TestNode::Atom {
                comparison: right_comparison,
                pattern: right_pattern,
            },
        ) if left_comparison == comparison
            && right_comparison == comparison
            && distinct_constant_patterns(left_pattern, right_pattern)
    )
}

/// Returns whether a constant atom can be removed because a sibling implies it.
///
/// `candidate_comparison` identifies the atom being considered for removal. The sibling must use
/// its opposite comparison and select a distinct constant in the same component domain. Thus the
/// two call sites implement the dual implications:
///
/// - conjunction: `Eq(c) ∧ Neq(d) = Eq(c)` for `c != d`, so the `Neq(d)` candidate is removed;
/// - disjunction: `Neq(d) ∨ Eq(c) = Neq(d)` for `c != d`, so the `Eq(c)` candidate is removed.
/// # Preconditions
/// `candidate` and every ID in `siblings` must be canonical tests from the same store. The sibling
/// slice need not be sorted.
fn redundant_constant_atom(
    candidate: TestId<'_>,
    siblings: &[TestId<'_>],
    candidate_comparison: Comparison,
) -> bool {
    let TestNode::Atom {
        comparison,
        pattern: candidate_pattern,
    } = *candidate.get()
    else {
        return false;
    };
    let sibling_comparison = !candidate_comparison;
    comparison == candidate_comparison
        && siblings.iter().copied().any(|sibling| {
            let TestNode::Atom {
                comparison,
                pattern,
            } = *sibling.get()
            else {
                return false;
            };
            comparison == sibling_comparison
                && distinct_constant_patterns(candidate_pattern, pattern)
        })
}

/// Recognizes a compound operand absorbed by another operand of the outer connective.
///
/// For an outer conjunction, `candidate` must be a disjunction. A plain sibling implements direct
/// absorption, `x ∧ (x ∨ y) = x`; a disjunctive sibling whose children are a subset of the
/// candidate's children implements generalized absorption,
/// `(x ∨ y) ∧ (x ∨ y ∨ z) = x ∨ y`. Outer disjunction uses the dual laws
/// `x ∨ (x ∧ y) = x` and `(x ∧ y) ∨ (x ∧ y ∧ z) = x ∧ y`.
///
/// An operand is never compared with itself. The outer smart constructors sort and deduplicate
/// their operands before calling this helper, so idempotence (`x ∧ x = x`, `x ∨ x = x`) has
/// already retained exactly one representative.
///
/// # Preconditions
/// `siblings` must be sorted and deduplicated. Every opposite-connective child slice must also be
/// sorted and deduplicated. All IDs must belong to the same [`CanonicalStore`].
fn absorbed_by_sibling<'arena>(
    candidate: TestId<'arena>,
    siblings: &[TestId<'arena>],
    conjunction: bool,
) -> bool {
    let nested = match (conjunction, *candidate.get()) {
        (true, TestNode::Or(children)) | (false, TestNode::And(children)) => children,
        _ => return false,
    };
    siblings.iter().copied().any(|sibling| {
        // Do not remove the sole representative left by the caller's idempotence reduction.
        if sibling == candidate {
            return false;
        }
        match (conjunction, *sibling.get()) {
            // Generalized absorption: the sibling's child set is a subset of the candidate's.
            (true, TestNode::Or(children)) | (false, TestNode::And(children)) => children
                .iter()
                .all(|child| nested.binary_search(child).is_ok()),
            // Direct absorption: the sibling is one of the candidate's nested operands.
            _ => nested.binary_search(&sibling).is_ok(),
        }
    })
}

/// Recognizes a regex and its whole-language complement.
///
/// # Preconditions
/// Both IDs must be canonical regexes from the same [`CanonicalStore`].
fn complementary_regex<'arena>(left: RegexId<'arena>, right: RegexId<'arena>) -> bool {
    matches!(left.get().kind, RegexKind::Not(inner) if inner == right)
        || matches!(right.get().kind, RegexKind::Not(inner) if inner == left)
}

/// Recognizes the canonical complement of epsilon.
///
/// # Preconditions
/// `regex` must be a canonical regex from the current [`CanonicalStore`].
fn is_epsilon_complement(regex: RegexId<'_>) -> bool {
    matches!(regex.get().kind, RegexKind::Not(inner) if matches!(inner.get().kind, RegexKind::Epsilon))
}

/// Recognizes a compound regex operand absorbed by another operand of the outer set connective.
///
/// For outer union, `candidate` must be an intersection. A plain sibling implements
/// `R ∪ (R ∩ S) = R`; an intersecting sibling whose children are a subset of the candidate's
/// children implements `(R ∩ S) ∪ (R ∩ S ∩ T) = R ∩ S`. Outer intersection uses the dual laws
/// `R ∩ (R ∪ S) = R` and `(R ∪ S) ∩ (R ∪ S ∪ T) = R ∪ S`.
///
/// An operand is never compared with itself. The outer smart constructors sort and deduplicate
/// their operands first, so set-union/set-intersection idempotence has already retained exactly one
/// representative.
///
/// # Preconditions
/// `siblings` must be sorted and deduplicated. Every opposite-connective child slice must also be
/// sorted and deduplicated. All IDs must belong to the same [`CanonicalStore`].
fn regex_absorbed_by_sibling<'arena>(
    candidate: RegexId<'arena>,
    siblings: &[RegexId<'arena>],
    union: bool,
) -> bool {
    let nested = match (union, candidate.get().kind) {
        (true, RegexKind::Intersect(children)) | (false, RegexKind::Union(children)) => children,
        _ => return false,
    };
    siblings.iter().copied().any(|sibling| {
        // Do not remove the sole representative left by the caller's idempotence reduction.
        if sibling == candidate {
            return false;
        }
        match (union, sibling.get().kind) {
            // Generalized absorption: the sibling's child set is a subset of the candidate's.
            (true, RegexKind::Intersect(children)) | (false, RegexKind::Union(children)) => {
                children
                    .iter()
                    .all(|child| nested.binary_search(child).is_ok())
            }
            // Direct absorption: the sibling is one of the candidate's nested operands.
            _ => nested.binary_search(&sibling).is_ok(),
        }
    })
}

impl<'arena> CanonicalStore<'arena> {
    /// Recognizes atomic and compound complements among sibling tests.
    ///
    /// # Preconditions
    /// `tests` and every nested Boolean child slice must be sorted and deduplicated. All IDs must
    /// belong to `self`.
    fn tests_have_complements(&mut self, tests: &[TestId<'arena>], conjunction: bool) -> bool {
        if pair_satisfies(tests, complementary_test) {
            return true;
        }
        tests.iter().copied().any(|candidate| {
            let dual_children = match (conjunction, *candidate.get()) {
                (true, TestNode::Or(children)) | (false, TestNode::And(children)) => children,
                _ => return false,
            };
            dual_children.iter().all(|child| {
                let complement = self.test_not(*child);
                tests.binary_search(&complement).is_ok()
            })
        })
    }

    /// Constructs canonical conjunction over one-event tests.
    ///
    /// # Preconditions
    /// Every child must be a canonical test from `self`. Input order and duplicates are unrestricted.
    pub(super) fn test_and(
        &mut self,
        children: impl IntoIterator<Item = TestId<'arena>>,
    ) -> TestId<'arena> {
        let mut flat = SmallVec::<[TestId<'arena>; 4]>::new();
        for child in children {
            match *child.get() {
                TestNode::False => return self.test_false,
                TestNode::True => {}
                TestNode::And(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        flat.sort_unstable();
        flat.dedup();
        if self.tests_have_complements(&flat, true)
            || pair_satisfies(&flat, |left, right| {
                distinct_constant_atoms(left, right, Comparison::Eq)
            })
        {
            return self.test_false;
        }
        if flat.iter().any(|candidate| {
            matches!(
                *candidate.get(),
                TestNode::Or(_)
                    | TestNode::Atom {
                        comparison: Comparison::Neq,
                        ..
                    }
            )
        }) {
            let siblings = flat.clone();
            flat.retain(|candidate| {
                !absorbed_by_sibling(*candidate, &siblings, true)
                    && !redundant_constant_atom(*candidate, &siblings, Comparison::Neq)
            });
        }
        match flat.as_slice() {
            [] => self.test_true,
            [only] => *only,
            _ => {
                let values = self.tests.arena().alloc_slice_copy(&flat);
                self.tests.mk(TestNode::And(values))
            }
        }
    }

    /// Constructs canonical disjunction over one-event tests.
    ///
    /// # Preconditions
    /// Every child must be a canonical test from `self`. Input order and duplicates are unrestricted.
    pub(super) fn test_or(
        &mut self,
        children: impl IntoIterator<Item = TestId<'arena>>,
    ) -> TestId<'arena> {
        let mut flat = SmallVec::<[TestId<'arena>; 4]>::new();
        for child in children {
            match *child.get() {
                TestNode::True => return self.test_true,
                TestNode::False => {}
                TestNode::Or(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        flat.sort_unstable();
        flat.dedup();
        if self.tests_have_complements(&flat, false)
            || pair_satisfies(&flat, |left, right| {
                distinct_constant_atoms(left, right, Comparison::Neq)
            })
        {
            return self.test_true;
        }
        if flat.iter().any(|candidate| {
            matches!(
                *candidate.get(),
                TestNode::And(_)
                    | TestNode::Atom {
                        comparison: Comparison::Eq,
                        ..
                    }
            )
        }) {
            let siblings = flat.clone();
            flat.retain(|candidate| {
                !absorbed_by_sibling(*candidate, &siblings, false)
                    && !redundant_constant_atom(*candidate, &siblings, Comparison::Eq)
            });
        }
        match flat.as_slice() {
            [] => self.test_false,
            [only] => *only,
            _ => {
                let values = self.tests.arena().alloc_slice_copy(&flat);
                self.tests.mk(TestNode::Or(values))
            }
        }
    }

    /// Constructs the normalized Boolean complement of one event test.
    ///
    /// # Preconditions
    /// `test` must be a canonical test from `self`.
    pub(super) fn test_not(&mut self, test: TestId<'arena>) -> TestId<'arena> {
        match *test.get() {
            TestNode::True => self.test_false,
            TestNode::False => self.test_true,
            TestNode::Atom {
                comparison,
                pattern,
            } => self.tests.mk(TestNode::Atom {
                comparison: !comparison,
                pattern,
            }),
            TestNode::And(children) => {
                let complements = children
                    .iter()
                    .map(|child| self.test_not(*child))
                    .collect::<SmallVec<[TestId<'arena>; 4]>>();
                self.test_or(complements)
            }
            TestNode::Or(children) => {
                let complements = children
                    .iter()
                    .map(|child| self.test_not(*child))
                    .collect::<SmallVec<[TestId<'arena>; 4]>>();
                self.test_and(complements)
            }
        }
    }

    /// Interns one normalized regex kind with its deterministic nullability cache.
    ///
    /// # Preconditions
    /// `kind` must already satisfy the flattened-normal-form invariants, all child IDs must belong
    /// to `self`, and `nullable` must equal the semantic nullability of `kind`.
    fn intern_regex(&mut self, kind: RegexKind<'arena>, nullable: bool) -> RegexId<'arena> {
        let (id, is_new) = self.regexes.mk_is_new(RegexNode::new(kind, nullable));
        if !is_new {
            assert_eq!(
                id.get().nullable(),
                nullable,
                "equal regex syntax computed inconsistent nullability"
            );
        }
        id
    }

    /// Lifts a one-event test into a regex, folding false to the empty language.
    ///
    /// # Preconditions
    /// `test` must be a canonical test from `self`.
    pub(super) fn regex_test(&mut self, test: TestId<'arena>) -> RegexId<'arena> {
        if test == self.test_false {
            self.empty
        } else {
            self.intern_regex(RegexKind::Test(test), false)
        }
    }

    /// Constructs canonical set union.
    ///
    /// # Preconditions
    /// Every child must be a canonical regex from `self`. Input order and duplicates are unrestricted.
    pub(super) fn regex_union(
        &mut self,
        children: impl IntoIterator<Item = RegexId<'arena>>,
    ) -> RegexId<'arena> {
        let mut flat = SmallVec::<[RegexId<'arena>; 4]>::new();
        for child in children {
            match child.get().kind {
                RegexKind::All => return self.all,
                RegexKind::Empty => {}
                RegexKind::Union(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        let mut tests = SmallVec::<[TestId<'arena>; 4]>::new();
        flat.retain(|child| match child.get().kind {
            RegexKind::Test(test) => {
                tests.push(test);
                false
            }
            _ => true,
        });
        if !tests.is_empty() {
            let test = self.test_or(tests);
            let regex = self.regex_test(test);
            if regex != self.empty {
                flat.push(regex);
            }
        }

        flat.sort_unstable();
        flat.dedup();
        if pair_satisfies(&flat, complementary_regex) {
            return self.all;
        }
        if flat.contains(&self.epsilon)
            && flat
                .iter()
                .any(|child| *child != self.epsilon && self.nullable(*child))
        {
            flat.retain(|child| *child != self.epsilon);
        }
        if flat
            .iter()
            .any(|candidate| matches!(candidate.get().kind, RegexKind::Intersect(_)))
        {
            let siblings = flat.clone();
            flat.retain(|candidate| !regex_absorbed_by_sibling(*candidate, &siblings, true));
        }
        match flat.as_slice() {
            [] => self.empty,
            [only] => *only,
            _ => {
                let nullable = flat.iter().any(|child| self.nullable(*child));
                let values = self.regexes.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexKind::Union(values), nullable)
            }
        }
    }

    /// Constructs canonical set intersection.
    ///
    /// # Preconditions
    /// Every child must be a canonical regex from `self`. Input order and duplicates are unrestricted.
    pub(super) fn regex_intersect(
        &mut self,
        children: impl IntoIterator<Item = RegexId<'arena>>,
    ) -> RegexId<'arena> {
        let mut flat = SmallVec::<[RegexId<'arena>; 4]>::new();
        for child in children {
            match child.get().kind {
                RegexKind::Empty => return self.empty,
                RegexKind::All => {}
                RegexKind::Intersect(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        let mut tests = SmallVec::<[TestId<'arena>; 4]>::new();
        flat.retain(|child| match child.get().kind {
            RegexKind::Test(test) => {
                tests.push(test);
                false
            }
            _ => true,
        });
        if !tests.is_empty() {
            let test = self.test_and(tests);
            let regex = self.regex_test(test);
            if regex == self.empty {
                return self.empty;
            }
            flat.push(regex);
        }

        flat.sort_unstable();
        flat.dedup();
        if pair_satisfies(&flat, complementary_regex) {
            return self.empty;
        }
        if flat.contains(&self.epsilon) {
            return if flat.iter().all(|child| self.nullable(*child)) {
                self.epsilon
            } else {
                self.empty
            };
        }
        if flat
            .iter()
            .any(|child| !is_epsilon_complement(*child) && !self.nullable(*child))
        {
            flat.retain(|child| !is_epsilon_complement(*child));
        }
        if flat
            .iter()
            .any(|candidate| matches!(candidate.get().kind, RegexKind::Union(_)))
        {
            let siblings = flat.clone();
            flat.retain(|candidate| !regex_absorbed_by_sibling(*candidate, &siblings, false));
        }
        match flat.as_slice() {
            [] => self.all,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regexes.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexKind::Intersect(values), nullable)
            }
        }
    }

    /// Constructs canonical ordered concatenation.
    ///
    /// # Preconditions
    /// Every child must be a canonical regex from `self`. Their order is semantic; duplicates are
    /// permitted.
    pub(super) fn regex_concat(
        &mut self,
        children: impl IntoIterator<Item = RegexId<'arena>>,
    ) -> RegexId<'arena> {
        let mut flat = SmallVec::<[RegexId<'arena>; 4]>::new();
        for child in children {
            match child.get().kind {
                RegexKind::Empty => return self.empty,
                RegexKind::Epsilon => {}
                RegexKind::Concat(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        match flat.as_slice() {
            [] => self.epsilon,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regexes.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexKind::Concat(values), nullable)
            }
        }
    }

    /// Constructs canonical Kleene star.
    ///
    /// # Preconditions
    /// `inner` must be a canonical regex from `self`.
    pub(super) fn regex_star(&mut self, inner: RegexId<'arena>) -> RegexId<'arena> {
        match inner.get().kind {
            RegexKind::Empty | RegexKind::Epsilon => self.epsilon,
            RegexKind::All => self.all,
            RegexKind::Test(test) if test == self.test_true => self.all,
            RegexKind::Star(_) => inner,
            _ => self.intern_regex(RegexKind::Star(inner), true),
        }
    }

    /// Constructs canonical whole-language complement.
    ///
    /// # Preconditions
    /// `inner` must be a canonical regex from `self`.
    pub(super) fn regex_not(&mut self, inner: RegexId<'arena>) -> RegexId<'arena> {
        match inner.get().kind {
            RegexKind::Empty => self.all,
            RegexKind::All => self.empty,
            RegexKind::Not(value) => value,
            _ => self.intern_regex(RegexKind::Not(inner), !self.nullable(inner)),
        }
    }

    /// Returns cached empty-history acceptance directly from the hashconsed node.
    ///
    /// # Preconditions
    /// `regex` must be a canonical regex from `self`.
    pub(super) fn nullable(&self, regex: RegexId<'arena>) -> bool {
        regex.get().nullable()
    }
}
