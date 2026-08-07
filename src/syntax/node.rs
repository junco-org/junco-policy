//! Immutable hashconsed test and regular-expression nodes.
//!
//! `TestId` and `RegexId` are arena-backed [`BHConsed`] references. Structurally equal nodes share
//! one canonical allocation, so parent nodes need only child references. Nodes contain no compiler,
//! variable-environment, canonical-store, rule, or validator backreferences.

use std::hash::{Hash, Hasher};

use hashconsing::BHConsed;

use super::component::InternedAtomPattern;
use super::source::Comparison;

/// Boolean test over one history event.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TestNode<'arena> {
    /// Test that accepts every event.
    True,
    /// Test that accepts no event.
    False,
    /// Component equality or disequality test.
    Atom {
        comparison: Comparison,
        pattern: InternedAtomPattern<'arena>,
    },
    /// Conjunction of canonical child tests.
    And(&'arena [TestId<'arena>]),
    /// Disjunction of canonical child tests.
    Or(&'arena [TestId<'arena>]),
}

/// Canonical arena reference to a [`TestNode`].
pub(crate) type TestId<'arena> = BHConsed<'arena, TestNode<'arena>>;

/// Regular-expression syntax stored in one canonical node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RegexKind<'arena> {
    /// Empty language.
    Empty,
    /// Universal language over complete histories.
    All,
    /// Language containing only the empty history.
    Epsilon,
    /// One-event language selected by a boolean test.
    Test(TestId<'arena>),
    /// Set union. Children are flattened, sorted, and deduplicated.
    Union(&'arena [RegexId<'arena>]),
    /// Ordered language concatenation.
    Concat(&'arena [RegexId<'arena>]),
    /// Kleene star.
    Star(RegexId<'arena>),
    /// Set intersection. Children are flattened, sorted, and deduplicated.
    Intersect(&'arena [RegexId<'arena>]),
    /// Whole-language complement.
    Not(RegexId<'arena>),
}

/// Hashconsed regex payload with its cached nullability.
///
/// Structural identity deliberately excludes `nullable`: nullability is a deterministic function
/// of `kind`. Interning asserts that every reconstruction of an existing kind computes the same
/// cache value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RegexNode<'arena> {
    pub(super) kind: RegexKind<'arena>,
    nullable: bool,
}

impl<'arena> RegexNode<'arena> {
    /// Constructs a syntax node with its derived nullability cache.
    pub(super) const fn new(kind: RegexKind<'arena>, nullable: bool) -> Self {
        Self { kind, nullable }
    }

    /// Returns whether the node accepts the empty history.
    pub(super) const fn nullable(&self) -> bool {
        self.nullable
    }
}

impl PartialEq for RegexNode<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for RegexNode<'_> {}

impl Hash for RegexNode<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

/// Canonical arena reference to a [`RegexNode`].
pub(crate) type RegexId<'arena> = BHConsed<'arena, RegexNode<'arena>>;
