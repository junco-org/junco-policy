//! Immutable hashconsed test, regular-expression, and transition-regex nodes.

use std::hash::{Hash, Hasher};

use hashconsing::BHConsed;

use crate::model::Event;

use super::component::CompiledAtomPattern;
use super::source::Comparison;

/// Boolean test over one history event.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum TestNode<'arena, E: Event + 'arena> {
    /// Test that accepts every event.
    True,
    /// Test that accepts no event.
    False,
    /// Component equality or disequality test.
    Atom {
        comparison: Comparison,
        pattern: CompiledAtomPattern<E>,
    },
    /// Conjunction of canonical child tests.
    And(&'arena [TestId<'arena, E>]),
    /// Disjunction of canonical child tests.
    Or(&'arena [TestId<'arena, E>]),
}

/// Canonical arena reference to a [`TestNode`].
pub(super) type TestId<'arena, E> = BHConsed<'arena, TestNode<'arena, E>>;

/// Regular-expression syntax stored in one canonical node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum RegexKind<'arena, E: Event + 'arena> {
    /// Empty language.
    Empty,
    /// Universal language over complete histories.
    All,
    /// Language containing only the empty history.
    Epsilon,
    /// One-event language selected by a boolean test.
    Test(TestId<'arena, E>),
    /// Set union. Children are flattened, sorted, and deduplicated.
    Union(&'arena [RegexId<'arena, E>]),
    /// Ordered language concatenation.
    Concat(&'arena [RegexId<'arena, E>]),
    /// Kleene star.
    Star(RegexId<'arena, E>),
    /// Set intersection. Children are flattened, sorted, and deduplicated.
    Intersect(&'arena [RegexId<'arena, E>]),
    /// Whole-language complement.
    Not(RegexId<'arena, E>),
}

/// Hashconsed regex payload with its cached nullability.
///
/// Structural identity deliberately excludes `nullable`: nullability is a deterministic function
/// of `kind`. Interning asserts that every reconstruction of an existing kind computes the same
/// cache value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RegexNode<'arena, E: Event + 'arena> {
    pub(super) kind: RegexKind<'arena, E>,
    nullable: bool,
}

impl<'arena, E: Event + 'arena> RegexNode<'arena, E> {
    /// Constructs a syntax node with its derived nullability cache.
    pub(super) const fn new(kind: RegexKind<'arena, E>, nullable: bool) -> Self {
        Self { kind, nullable }
    }

    /// Returns whether the node accepts the empty history.
    pub(super) const fn nullable(&self) -> bool {
        self.nullable
    }
}

impl<'arena, E: Event + 'arena> PartialEq for RegexNode<'arena, E> {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl<'arena, E: Event + 'arena> Eq for RegexNode<'arena, E> {}

impl<'arena, E: Event + 'arena> Hash for RegexNode<'arena, E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

/// Canonical arena reference to a [`RegexNode`].
pub(crate) type RegexId<'arena, E> = BHConsed<'arena, RegexNode<'arena, E>>;

/// Normalized symbolic transition over one unresolved event.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum TransitionNode<'arena, E: Event + 'arena> {
    /// Constant transition to one normalized regex state.
    Const(RegexId<'arena, E>),
    /// Conditional transition selected by one normalized event test.
    If {
        test: TestId<'arena, E>,
        then_transition: TransitionId<'arena, E>,
        else_transition: TransitionId<'arena, E>,
    },
    /// Canonical n-ary transition union.
    Union(&'arena [TransitionId<'arena, E>]),
    /// Canonical n-ary transition intersection.
    Intersect(&'arena [TransitionId<'arena, E>]),
    /// Transition complement before normalization pushes it to leaves.
    Not(TransitionId<'arena, E>),
    /// One-sided concatenation with a fixed normalized regex suffix.
    Append {
        transition: TransitionId<'arena, E>,
        suffix: &'arena [RegexId<'arena, E>],
    },
}

/// Canonical arena reference to a [`TransitionNode`].
pub(super) type TransitionId<'arena, E> = BHConsed<'arena, TransitionNode<'arena, E>>;
