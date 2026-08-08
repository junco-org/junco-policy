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
fn contradictory_equalities(left: TestId<'_>, right: TestId<'_>) -> bool {
    let (
        TestNode::Atom {
            comparison: Comparison::Eq,
            pattern: left,
        },
        TestNode::Atom {
            comparison: Comparison::Eq,
            pattern: right,
        },
    ) = (*left.get(), *right.get())
    else {
        return false;
    };
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

fn has_contradictory_equalities(tests: &[TestId<'_>]) -> bool {
    tests.iter().enumerate().any(|(index, left)| {
        tests[index + 1..]
            .iter()
            .any(|right| contradictory_equalities(*left, *right))
    })
}

/// Returns true for `Or`/`And` operands absorbed by a direct sibling.
fn absorbed_by_sibling<'arena>(
    candidate: TestId<'arena>,
    siblings: &[TestId<'arena>],
    conjunction: bool,
) -> bool {
    let nested = match (conjunction, *candidate.get()) {
        (true, TestNode::Or(children)) | (false, TestNode::And(children)) => children,
        _ => return false,
    };
    nested
        .iter()
        .any(|child| siblings.iter().any(|sibling| sibling == child))
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

impl<'arena> CanonicalStore<'arena> {
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
        if has_complementary_tests(&flat) || has_contradictory_equalities(&flat) {
            return self.test_false;
        }
        let siblings = flat.clone();
        flat.retain(|candidate| !absorbed_by_sibling(*candidate, &siblings, true));
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
        if has_complementary_tests(&flat) {
            return self.test_true;
        }
        let siblings = flat.clone();
        flat.retain(|candidate| !absorbed_by_sibling(*candidate, &siblings, false));
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

        flat.sort_unstable();
        flat.dedup();
        if has_complementary_regexes(&flat) {
            return self.all;
        }
        if !flat.is_empty()
            && flat
                .iter()
                .all(|child| matches!(child.get().kind, RegexKind::Test(_)))
        {
            let tests = flat
                .iter()
                .map(|child| match child.get().kind {
                    RegexKind::Test(test) => test,
                    _ => unreachable!("all operands were checked as tests"),
                })
                .collect();
            let test = self.test_or(tests);
            return self.regex_test(test);
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

        flat.sort_unstable();
        flat.dedup();
        if has_complementary_regexes(&flat) {
            return self.empty;
        }
        if flat
            .iter()
            .any(|child| matches!(child.get().kind, RegexKind::Epsilon))
            && flat
                .iter()
                .any(|child| matches!(child.get().kind, RegexKind::Test(_)))
        {
            return self.empty;
        }
        if !flat.is_empty()
            && flat
                .iter()
                .all(|child| matches!(child.get().kind, RegexKind::Test(_)))
        {
            let tests = flat
                .iter()
                .map(|child| match child.get().kind {
                    RegexKind::Test(test) => test,
                    _ => unreachable!("all operands were checked as tests"),
                })
                .collect();
            let test = self.test_and(tests);
            return self.regex_test(test);
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
