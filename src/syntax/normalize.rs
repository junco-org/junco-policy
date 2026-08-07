//! Smart constructors for canonical test and regex DAGs.
//!
//! Every constructor applies local algebraic identities before hashconsing. Commutative test
//! conjunction/disjunction and regex union/intersection are flattened, ordered by canonical handle,
//! and deduplicated. Concatenation is flattened but preserves source order. These normal forms keep
//! the set of derivative states finite for the supported similarity quotient.

use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};
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
    pub(super) fn test_and(&mut self, children: Vec<TestId<'arena>>) -> TestId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TestNode::False => return self.test_false,
                TestNode::True => {}
                TestNode::And(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        // BHConsed ordering/equality is canonical uid ordering/equality. The uid remains an
        // implementation detail of the hashconsing crate; no uid is converted into a table index.
        flat.sort_unstable();
        flat.dedup();
        if has_complementary_tests(&flat) {
            return self.test_false;
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
    pub(super) fn test_or(&mut self, children: Vec<TestId<'arena>>) -> TestId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
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
        match flat.as_slice() {
            [] => self.test_false,
            [only] => *only,
            _ => {
                let values = self.tests.arena().alloc_slice_copy(&flat);
                self.tests.mk(TestNode::Or(values))
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
    pub(super) fn regex_union(&mut self, children: Vec<RegexId<'arena>>) -> RegexId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
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
    pub(super) fn regex_intersect(&mut self, children: Vec<RegexId<'arena>>) -> RegexId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
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
    pub(super) fn regex_concat(&mut self, children: Vec<RegexId<'arena>>) -> RegexId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
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
