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

/// Returns whether a test set contains both an atom and its disequality complement.
fn has_complementary_tests(tests: &[TestId<'_>]) -> bool {
    let mut remaining = tests;
    while let Some((left, right)) = remaining.split_first() {
        if right
            .iter()
            .any(|candidate| complementary_test(*left, *candidate))
        {
            return true;
        }
        remaining = right;
    }
    false
}

/// Recognizes `Eq(pattern)` paired with `Neq(pattern)`.
fn complementary_test<'arena>(left: TestId<'arena>, right: TestId<'arena>) -> bool {
    match (*left.get(), *right.get()) {
        (
            TestNode::Atom {
                comparison: left_comparison,
                pattern: left_pattern,
            },
            TestNode::Atom {
                comparison: right_comparison,
                pattern: right_pattern,
            },
        ) => left_comparison != right_comparison && left_pattern == right_pattern,
        _ => false,
    }
}

/// Recognizes unequal constants selected at the same component coordinate.
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

fn atom(test: TestId<'_>) -> Option<(Comparison, CompiledAtomPattern<'_>)> {
    match *test.get() {
        TestNode::Atom {
            comparison,
            pattern,
        } => Some((comparison, pattern)),
        _ => None,
    }
}

fn contradictory_equalities(left: TestId<'_>, right: TestId<'_>) -> bool {
    matches!(
        (atom(left), atom(right)),
        (
            Some((Comparison::Eq, left)),
            Some((Comparison::Eq, right))
        ) if distinct_constant_patterns(left, right)
    )
}

fn has_contradictory_equalities(tests: &[TestId<'_>]) -> bool {
    tests.iter().enumerate().any(|(index, left)| {
        tests[index + 1..]
            .iter()
            .any(|right| contradictory_equalities(*left, *right))
    })
}

/// An equality implies disequality with every distinct constant at the same coordinate.
fn redundant_conjunct(candidate: TestId<'_>, siblings: &[TestId<'_>]) -> bool {
    let Some((Comparison::Neq, candidate)) = atom(candidate) else {
        return false;
    };
    siblings.iter().any(|sibling| {
        matches!(
            atom(*sibling),
            Some((Comparison::Eq, sibling))
                if distinct_constant_patterns(candidate, sibling)
        )
    })
}

/// A disequality subsumes equality with every distinct constant at the same coordinate.
fn redundant_disjunct(candidate: TestId<'_>, siblings: &[TestId<'_>]) -> bool {
    let Some((Comparison::Eq, candidate)) = atom(candidate) else {
        return false;
    };
    siblings.iter().any(|sibling| {
        matches!(
            atom(*sibling),
            Some((Comparison::Neq, sibling))
                if distinct_constant_patterns(candidate, sibling)
        )
    })
}

fn has_distinct_disequalities(tests: &[TestId<'_>]) -> bool {
    tests.iter().enumerate().any(|(index, left)| {
        let Some((Comparison::Neq, left)) = atom(*left) else {
            return false;
        };
        tests[index + 1..].iter().any(|right| {
            matches!(
                atom(*right),
                Some((Comparison::Neq, right))
                    if distinct_constant_patterns(left, right)
            )
        })
    })
}

/// Returns true when a compound opposite operator contains a sibling's complete operand set.
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
        if sibling == candidate {
            return false;
        }
        match (conjunction, *sibling.get()) {
            (true, TestNode::Or(children)) | (false, TestNode::And(children)) => children
                .iter()
                .all(|child| nested.binary_search(child).is_ok()),
            _ => nested.binary_search(&sibling).is_ok(),
        }
    })
}

/// Returns whether a regex set contains a node and its whole-language complement.
fn has_complementary_regexes(regexes: &[RegexId<'_>]) -> bool {
    let mut remaining = regexes;
    while let Some((left, right)) = remaining.split_first() {
        if right
            .iter()
            .any(|candidate| complementary_regex(*left, *candidate))
        {
            return true;
        }
        remaining = right;
    }
    false
}

/// Recognizes `r` paired with `Not(r)` using canonical handle equality.
fn complementary_regex<'arena>(left: RegexId<'arena>, right: RegexId<'arena>) -> bool {
    matches!(left.get().kind, RegexKind::Not(inner) if inner == right)
        || matches!(right.get().kind, RegexKind::Not(inner) if inner == left)
}

fn is_epsilon_complement(regex: RegexId<'_>) -> bool {
    matches!(regex.get().kind, RegexKind::Not(inner) if matches!(inner.get().kind, RegexKind::Epsilon))
}

/// Returns true when a compound opposite set operator contains a sibling's complete operand set.
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
        if sibling == candidate {
            return false;
        }
        match (union, sibling.get().kind) {
            (true, RegexKind::Intersect(children)) | (false, RegexKind::Union(children)) => {
                children
                    .iter()
                    .all(|child| nested.binary_search(child).is_ok())
            }
            _ => nested.binary_search(&sibling).is_ok(),
        }
    })
}

impl<'arena> CanonicalStore<'arena> {
    fn tests_have_complements(&mut self, tests: &[TestId<'arena>], conjunction: bool) -> bool {
        if has_complementary_tests(tests) {
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
        if self.tests_have_complements(&flat, true) || has_contradictory_equalities(&flat) {
            return self.test_false;
        }
        let siblings = flat.clone();
        flat.retain(|candidate| {
            !absorbed_by_sibling(*candidate, &siblings, true)
                && !redundant_conjunct(*candidate, &siblings)
        });
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
        if self.tests_have_complements(&flat, false) || has_distinct_disequalities(&flat) {
            return self.test_true;
        }
        let siblings = flat.clone();
        flat.retain(|candidate| {
            !absorbed_by_sibling(*candidate, &siblings, false)
                && !redundant_disjunct(*candidate, &siblings)
        });
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
    pub(super) fn test_not(&mut self, test: TestId<'arena>) -> TestId<'arena> {
        match *test.get() {
            TestNode::True => self.test_false,
            TestNode::False => self.test_true,
            TestNode::Atom {
                comparison,
                pattern,
            } => self.tests.mk(TestNode::Atom {
                comparison: match comparison {
                    Comparison::Eq => Comparison::Neq,
                    Comparison::Neq => Comparison::Eq,
                },
                pattern,
            }),
            TestNode::And(children) => {
                let complements = children.iter().map(|child| self.test_not(*child)).collect();
                self.test_or(complements)
            }
            TestNode::Or(children) => {
                let complements = children.iter().map(|child| self.test_not(*child)).collect();
                self.test_and(complements)
            }
        }
    }

    /// Interns one normalized regex kind with its deterministic nullability cache.
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
    pub(super) fn regex_test(&mut self, test: TestId<'arena>) -> RegexId<'arena> {
        if test == self.test_false {
            self.empty
        } else {
            self.intern_regex(RegexKind::Test(test), false)
        }
    }

    /// Constructs canonical set union.
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

        let mut tests = Vec::new();
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
        if has_complementary_regexes(&flat) {
            return self.all;
        }
        if flat.contains(&self.epsilon)
            && flat
                .iter()
                .any(|child| *child != self.epsilon && self.nullable(*child))
        {
            flat.retain(|child| *child != self.epsilon);
        }
        let siblings = flat.clone();
        flat.retain(|candidate| !regex_absorbed_by_sibling(*candidate, &siblings, true));
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

        let mut tests = Vec::new();
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
        if has_complementary_regexes(&flat) {
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
        let siblings = flat.clone();
        flat.retain(|candidate| !regex_absorbed_by_sibling(*candidate, &siblings, false));
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
    pub(super) fn regex_not(&mut self, inner: RegexId<'arena>) -> RegexId<'arena> {
        match inner.get().kind {
            RegexKind::Empty => self.all,
            RegexKind::All => self.empty,
            RegexKind::Not(value) => value,
            _ => self.intern_regex(RegexKind::Not(inner), !self.nullable(inner)),
        }
    }

    /// Returns cached empty-history acceptance directly from the hashconsed node.
    pub(super) fn nullable(&self, regex: RegexId<'arena>) -> bool {
        regex.get().nullable()
    }
}
