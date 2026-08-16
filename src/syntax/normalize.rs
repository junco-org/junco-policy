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
fn has_sibling_pair<T: Copy>(values: &[T], mut matches: impl FnMut(T, T) -> bool) -> bool {
    values.iter().enumerate().any(|(index, left)| {
        values[index + 1..]
            .iter()
            .any(|right| matches(*left, *right))
    })
}

fn remove_by_sibling_relation<T: Copy>(
    values: &mut SmallVec<[T; 4]>,
    candidate_may_match: impl Fn(T) -> bool,
    redundant: impl Fn(T, &[T]) -> bool,
) {
    if !values.iter().copied().any(&candidate_may_match) {
        return;
    }
    let siblings = values.clone();
    values.retain(|candidate| !redundant(*candidate, &siblings));
}

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

fn redundant_constant_atom(
    candidate: TestId<'_>,
    siblings: &[TestId<'_>],
    candidate_comparison: Comparison,
    sibling_comparison: Comparison,
) -> bool {
    let TestNode::Atom {
        comparison,
        pattern: candidate_pattern,
    } = *candidate.get()
    else {
        return false;
    };
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

fn complementary_regex<'arena>(left: RegexId<'arena>, right: RegexId<'arena>) -> bool {
    matches!(left.get().kind, RegexKind::Not(inner) if inner == right)
        || matches!(right.get().kind, RegexKind::Not(inner) if inner == left)
}

fn is_epsilon_complement(regex: RegexId<'_>) -> bool {
    matches!(regex.get().kind, RegexKind::Not(inner) if matches!(inner.get().kind, RegexKind::Epsilon))
}

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
        if has_sibling_pair(tests, complementary_test) {
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
        if self.tests_have_complements(&flat, true)
            || has_sibling_pair(&flat, |left, right| {
                distinct_constant_atoms(left, right, Comparison::Eq)
            })
        {
            return self.test_false;
        }
        remove_by_sibling_relation(
            &mut flat,
            |candidate| {
                matches!(
                    *candidate.get(),
                    TestNode::Or(_)
                        | TestNode::Atom {
                            comparison: Comparison::Neq,
                            ..
                        }
                )
            },
            |candidate, siblings| {
                absorbed_by_sibling(candidate, siblings, true)
                    || redundant_constant_atom(candidate, siblings, Comparison::Neq, Comparison::Eq)
            },
        );
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
        if self.tests_have_complements(&flat, false)
            || has_sibling_pair(&flat, |left, right| {
                distinct_constant_atoms(left, right, Comparison::Neq)
            })
        {
            return self.test_true;
        }
        remove_by_sibling_relation(
            &mut flat,
            |candidate| {
                matches!(
                    *candidate.get(),
                    TestNode::And(_)
                        | TestNode::Atom {
                            comparison: Comparison::Eq,
                            ..
                        }
                )
            },
            |candidate, siblings| {
                absorbed_by_sibling(candidate, siblings, false)
                    || redundant_constant_atom(candidate, siblings, Comparison::Eq, Comparison::Neq)
            },
        );
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
        if has_sibling_pair(&flat, complementary_regex) {
            return self.all;
        }
        if flat.contains(&self.epsilon)
            && flat
                .iter()
                .any(|child| *child != self.epsilon && self.nullable(*child))
        {
            flat.retain(|child| *child != self.epsilon);
        }
        remove_by_sibling_relation(
            &mut flat,
            |candidate| matches!(candidate.get().kind, RegexKind::Intersect(_)),
            |candidate, siblings| regex_absorbed_by_sibling(candidate, siblings, true),
        );
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
        if has_sibling_pair(&flat, complementary_regex) {
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
        remove_by_sibling_relation(
            &mut flat,
            |candidate| matches!(candidate.get().kind, RegexKind::Union(_)),
            |candidate, siblings| regex_absorbed_by_sibling(candidate, siblings, false),
        );
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
