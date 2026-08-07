//! Hashconsed test and regular-expression nodes plus public rule-local handles.
//!
//! `TestId` and `RegexId` are arena-backed [`BHConsed`] references. The hashconsing library gives
//! structurally equal nodes one canonical handle, so equality and ordering of child handles are
//! constant-time. Public [`Test`] and [`Regex`] wrappers add context and rule-scope provenance; a
//! rule builder rejects wrappers created by another context or scope.

use std::hash::{Hash, Hasher};

use hashconsing::BHConsed;

use super::component::CompiledAtomPattern;
use super::identity::{ContextId, RuleScopeId};
use super::pattern::Comparison;

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
        pattern: CompiledAtomPattern<'arena>,
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
/// of `kind`, not syntax. Interning asserts that every reconstruction of an existing kind computes
/// the same cache value. Keeping the cache beside the node removes the former uid-to-`usize`
/// conversion and parallel nullable table.
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

/// Rule-local handle to a compiled boolean event test.
///
/// Handles are cheap to copy. They may be combined only through the [`RuleSyntax`](super::RuleSyntax)
/// that created them; provenance checks prevent variables from escaping their binding scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Test<'arena> {
    pub(super) context: ContextId<'arena>,
    pub(super) scope: RuleScopeId<'arena>,
    pub(super) id: TestId<'arena>,
}

/// Rule-local handle to a canonical past regular expression.
///
/// The arena lifetime ensures the underlying DAG outlives this handle. Context and scope identities
/// are reference-backed provenance tokens, not numeric table indexes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Regex<'arena> {
    pub(super) context: ContextId<'arena>,
    pub(super) scope: RuleScopeId<'arena>,
    pub(super) id: RegexId<'arena>,
}
