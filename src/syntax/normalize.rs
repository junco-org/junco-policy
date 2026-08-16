//! Smart constructors for canonical test and regex DAGs.
//!
//! The constructors implement `Norm_B` and `Norm` from `symbolic-matcher.tex`: flattened ACI
//! Boolean operators, absorption and contradiction reductions, flattened regex set operators,
//! ordered concatenation, cross-layer test reductions, and cached nullability.

use smallvec::SmallVec;

use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};
use super::rewrite::{
    RegexConnective, SiblingResult, TestConnective, rewrite_regex_siblings, rewrite_test_siblings,
};
use super::source::Comparison;
use super::store::CanonicalStore;

fn is_epsilon_complement(regex: RegexId<'_>) -> bool {
    matches!(regex.get().kind, RegexKind::Not(inner) if matches!(inner.get().kind, RegexKind::Epsilon))
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
        if rewrite_test_siblings(self, &mut flat, TestConnective::And) == SiblingResult::Collapse {
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
        if rewrite_test_siblings(self, &mut flat, TestConnective::Or) == SiblingResult::Collapse {
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
        if rewrite_regex_siblings(&mut flat, RegexConnective::Union) == SiblingResult::Collapse {
            return self.all;
        }
        if flat.contains(&self.epsilon)
            && flat
                .iter()
                .any(|child| *child != self.epsilon && self.nullable(*child))
        {
            flat.retain(|child| *child != self.epsilon);
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
        if rewrite_regex_siblings(&mut flat, RegexConnective::Intersect) == SiblingResult::Collapse
        {
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
