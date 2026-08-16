//! Declarative sibling rewrite rules for normalized Boolean sets.

use smallvec::SmallVec;

use super::component::CompiledAtomPattern;
use super::node::{RegexId, RegexKind, TestId, TestNode};
use super::source::{Comparison, ComponentPattern};
use super::store::CanonicalStore;

#[derive(Clone, Copy)]
pub(super) enum TestConnective {
    And,
    Or,
}

impl TestConnective {
    fn distinct_constant_comparison(self) -> Comparison {
        match self {
            Self::And => Comparison::Eq,
            Self::Or => Comparison::Neq,
        }
    }

    fn implication_comparisons(self) -> (Comparison, Comparison) {
        match self {
            Self::And => (Comparison::Neq, Comparison::Eq),
            Self::Or => (Comparison::Eq, Comparison::Neq),
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum RegexConnective {
    Union,
    Intersect,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SiblingResult {
    Retain,
    Collapse,
}

#[derive(Clone, Copy)]
enum TestCollapse {
    Complements,
    DistinctConstants,
}

#[derive(Clone, Copy)]
enum TestDiscard {
    Absorption,
    ConstantImplication,
}

#[derive(Clone, Copy)]
enum RegexCollapse {
    Complements,
}

#[derive(Clone, Copy)]
enum RegexDiscard {
    Absorption,
}

struct SiblingRules<Collapse: 'static, Discard: 'static> {
    collapse: &'static [Collapse],
    discard: &'static [Discard],
}

const TEST_AND_RULES: SiblingRules<TestCollapse, TestDiscard> = SiblingRules {
    collapse: &[TestCollapse::Complements, TestCollapse::DistinctConstants],
    discard: &[TestDiscard::Absorption, TestDiscard::ConstantImplication],
};

const TEST_OR_RULES: SiblingRules<TestCollapse, TestDiscard> = SiblingRules {
    collapse: &[TestCollapse::Complements, TestCollapse::DistinctConstants],
    discard: &[TestDiscard::Absorption, TestDiscard::ConstantImplication],
};

const REGEX_UNION_RULES: SiblingRules<RegexCollapse, RegexDiscard> = SiblingRules {
    collapse: &[RegexCollapse::Complements],
    discard: &[RegexDiscard::Absorption],
};

const REGEX_INTERSECT_RULES: SiblingRules<RegexCollapse, RegexDiscard> = SiblingRules {
    collapse: &[RegexCollapse::Complements],
    discard: &[RegexDiscard::Absorption],
};

fn has_pair<T: Copy>(values: &[T], mut matches: impl FnMut(T, T) -> bool) -> bool {
    values.iter().enumerate().any(|(index, left)| {
        values[index + 1..]
            .iter()
            .any(|right| matches(*left, *right))
    })
}

fn atom<'arena>(test: TestId<'arena>) -> Option<(Comparison, CompiledAtomPattern<'arena>)> {
    match *test.get() {
        TestNode::Atom {
            comparison,
            pattern,
        } => Some((comparison, pattern)),
        _ => None,
    }
}

fn distinct_constants(left: CompiledAtomPattern<'_>, right: CompiledAtomPattern<'_>) -> bool {
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

fn complementary_atoms<'arena>(left: TestId<'arena>, right: TestId<'arena>) -> bool {
    matches!(
        (atom(left), atom(right)),
        (
            Some((left_comparison, left_pattern)),
            Some((right_comparison, right_pattern)),
        ) if left_comparison != right_comparison && left_pattern == right_pattern
    )
}

fn opposite_test_children<'arena>(
    test: TestId<'arena>,
    connective: TestConnective,
) -> Option<&'arena [TestId<'arena>]> {
    match (connective, *test.get()) {
        (TestConnective::And, TestNode::Or(children))
        | (TestConnective::Or, TestNode::And(children)) => Some(children),
        _ => None,
    }
}

fn has_test_complements<'arena>(
    store: &mut CanonicalStore<'arena>,
    tests: &[TestId<'arena>],
    connective: TestConnective,
) -> bool {
    has_pair(tests, complementary_atoms)
        || tests.iter().copied().any(|candidate| {
            opposite_test_children(candidate, connective).is_some_and(|children| {
                children.iter().all(|child| {
                    let complement = store.test_not(*child);
                    tests.binary_search(&complement).is_ok()
                })
            })
        })
}

fn distinct_constant_collapse<'arena>(
    tests: &[TestId<'arena>],
    connective: TestConnective,
) -> bool {
    let target = connective.distinct_constant_comparison();
    has_pair(tests, |left, right| {
        matches!(
            (atom(left), atom(right)),
            (
                Some((left_comparison, left_pattern)),
                Some((right_comparison, right_pattern)),
            ) if left_comparison == target
                && right_comparison == target
                && distinct_constants(left_pattern, right_pattern)
        )
    })
}

impl TestCollapse {
    fn matches<'arena>(
        self,
        store: &mut CanonicalStore<'arena>,
        tests: &[TestId<'arena>],
        connective: TestConnective,
    ) -> bool {
        match self {
            Self::Complements => has_test_complements(store, tests, connective),
            Self::DistinctConstants => distinct_constant_collapse(tests, connective),
        }
    }
}

fn set_is_subset<T: Ord>(subset: &[T], superset: &[T]) -> bool {
    subset
        .iter()
        .all(|value| superset.binary_search(value).is_ok())
}

fn test_absorbed<'arena>(
    candidate: TestId<'arena>,
    siblings: &[TestId<'arena>],
    connective: TestConnective,
) -> bool {
    let Some(candidate_children) = opposite_test_children(candidate, connective) else {
        return false;
    };
    siblings.iter().copied().any(|sibling| {
        if sibling == candidate {
            return false;
        }
        opposite_test_children(sibling, connective).map_or_else(
            || candidate_children.binary_search(&sibling).is_ok(),
            |sibling_children| set_is_subset(sibling_children, candidate_children),
        )
    })
}

fn constant_implication<'arena>(
    candidate: TestId<'arena>,
    siblings: &[TestId<'arena>],
    connective: TestConnective,
) -> bool {
    let (candidate_comparison, candidate_pattern) = match atom(candidate) {
        Some(atom) => atom,
        None => return false,
    };
    let (expected_candidate, expected_sibling) = connective.implication_comparisons();
    candidate_comparison == expected_candidate
        && siblings.iter().copied().any(|sibling| {
            matches!(
                atom(sibling),
                Some((comparison, pattern))
                    if comparison == expected_sibling
                        && distinct_constants(candidate_pattern, pattern)
            )
        })
}

impl TestDiscard {
    fn can_match(self, candidate: TestId<'_>, connective: TestConnective) -> bool {
        match self {
            Self::Absorption => opposite_test_children(candidate, connective).is_some(),
            Self::ConstantImplication => atom(candidate).is_some_and(|(comparison, _)| {
                comparison == connective.implication_comparisons().0
            }),
        }
    }

    fn matches<'arena>(
        self,
        candidate: TestId<'arena>,
        siblings: &[TestId<'arena>],
        connective: TestConnective,
    ) -> bool {
        match self {
            Self::Absorption => test_absorbed(candidate, siblings, connective),
            Self::ConstantImplication => constant_implication(candidate, siblings, connective),
        }
    }
}

pub(super) fn rewrite_test_siblings<'arena>(
    store: &mut CanonicalStore<'arena>,
    tests: &mut SmallVec<[TestId<'arena>; 4]>,
    connective: TestConnective,
) -> SiblingResult {
    let rules = match connective {
        TestConnective::And => &TEST_AND_RULES,
        TestConnective::Or => &TEST_OR_RULES,
    };
    if rules
        .collapse
        .iter()
        .any(|rule| rule.matches(store, tests, connective))
    {
        return SiblingResult::Collapse;
    }
    if !rules.discard.iter().any(|rule| {
        tests
            .iter()
            .copied()
            .any(|candidate| rule.can_match(candidate, connective))
    }) {
        return SiblingResult::Retain;
    }
    let siblings = tests.clone();
    tests.retain(|candidate| {
        !rules
            .discard
            .iter()
            .any(|rule| rule.matches(*candidate, &siblings, connective))
    });
    SiblingResult::Retain
}

fn complementary_regex<'arena>(left: RegexId<'arena>, right: RegexId<'arena>) -> bool {
    matches!(left.get().kind, RegexKind::Not(inner) if inner == right)
        || matches!(right.get().kind, RegexKind::Not(inner) if inner == left)
}

fn opposite_regex_children<'arena>(
    regex: RegexId<'arena>,
    connective: RegexConnective,
) -> Option<&'arena [RegexId<'arena>]> {
    match (connective, regex.get().kind) {
        (RegexConnective::Union, RegexKind::Intersect(children))
        | (RegexConnective::Intersect, RegexKind::Union(children)) => Some(children),
        _ => None,
    }
}

fn regex_absorbed<'arena>(
    candidate: RegexId<'arena>,
    siblings: &[RegexId<'arena>],
    connective: RegexConnective,
) -> bool {
    let Some(candidate_children) = opposite_regex_children(candidate, connective) else {
        return false;
    };
    siblings.iter().copied().any(|sibling| {
        if sibling == candidate {
            return false;
        }
        opposite_regex_children(sibling, connective).map_or_else(
            || candidate_children.binary_search(&sibling).is_ok(),
            |sibling_children| set_is_subset(sibling_children, candidate_children),
        )
    })
}

impl RegexCollapse {
    fn matches<'arena>(self, regexes: &[RegexId<'arena>]) -> bool {
        match self {
            Self::Complements => has_pair(regexes, complementary_regex),
        }
    }
}

impl RegexDiscard {
    fn can_match(self, candidate: RegexId<'_>, connective: RegexConnective) -> bool {
        match self {
            Self::Absorption => opposite_regex_children(candidate, connective).is_some(),
        }
    }

    fn matches<'arena>(
        self,
        candidate: RegexId<'arena>,
        siblings: &[RegexId<'arena>],
        connective: RegexConnective,
    ) -> bool {
        match self {
            Self::Absorption => regex_absorbed(candidate, siblings, connective),
        }
    }
}

pub(super) fn rewrite_regex_siblings<'arena>(
    regexes: &mut SmallVec<[RegexId<'arena>; 4]>,
    connective: RegexConnective,
) -> SiblingResult {
    let rules = match connective {
        RegexConnective::Union => &REGEX_UNION_RULES,
        RegexConnective::Intersect => &REGEX_INTERSECT_RULES,
    };
    if rules.collapse.iter().any(|rule| rule.matches(regexes)) {
        return SiblingResult::Collapse;
    }
    if !rules.discard.iter().any(|rule| {
        regexes
            .iter()
            .copied()
            .any(|candidate| rule.can_match(candidate, connective))
    }) {
        return SiblingResult::Retain;
    }
    let siblings = regexes.clone();
    regexes.retain(|candidate| {
        !rules
            .discard
            .iter()
            .any(|rule| rule.matches(*candidate, &siblings, connective))
    });
    SiblingResult::Retain
}
