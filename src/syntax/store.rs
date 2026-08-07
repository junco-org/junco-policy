//! Canonical storage for compiled values, tests, and regular expressions.
//!
//! The store owns monotonic value and node interning tables and borrows only the caller-provided
//! allocation arena. It has no active-rule, variable-environment, candidate, history, or validator
//! backreferences. Compiler and evaluator functions receive the store explicitly.

use bumpalo::Bump;
use hashconsing::BHConsign;

use super::component::ComponentValues;
use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};
use super::variable::VariableName;

/// Shared canonical value and node store used by all compiled rules in one validator.
pub(crate) struct CanonicalStore<'arena> {
    /// Component strings/resources shared by constants and candidate substitutions.
    pub(super) values: ComponentValues<'arena>,
    /// Canonical table for boolean event tests.
    pub(super) tests: BHConsign<'arena, TestNode<'arena>>,
    /// Canonical table for normalized regular-expression nodes.
    pub(super) regexes: BHConsign<'arena, RegexNode<'arena>>,
    /// Canonical true test.
    pub(super) test_true: TestId<'arena>,
    /// Canonical false test.
    pub(super) test_false: TestId<'arena>,
    /// Canonical empty language.
    pub(super) empty: RegexId<'arena>,
    /// Canonical universal language.
    pub(super) all: RegexId<'arena>,
    /// Canonical language containing only the empty history.
    pub(super) epsilon: RegexId<'arena>,
}

impl<'arena> CanonicalStore<'arena> {
    /// Creates empty value/node tables and seeds algebraic constants.
    pub(crate) fn new(arena: &'arena Bump) -> Self {
        let values = ComponentValues::new(arena);

        let mut tests = BHConsign::with_capacity(arena, 128);
        let test_true = tests.mk(TestNode::True);
        let test_false = tests.mk(TestNode::False);

        let mut regexes = BHConsign::with_capacity(arena, 1024);
        let empty = regexes.mk(RegexNode::new(RegexKind::Empty, false));
        let all = regexes.mk(RegexNode::new(RegexKind::All, true));
        let epsilon = regexes.mk(RegexNode::new(RegexKind::Epsilon, true));

        Self {
            values,
            tests,
            regexes,
            test_true,
            test_false,
            empty,
            all,
            epsilon,
        }
    }

    /// Interns a variable spelling in the same string pool used by component values.
    pub(super) fn intern_variable(&mut self, name: &str) -> VariableName<'arena> {
        VariableName::new(self.values.intern_string(name))
    }

    /// Number of canonical regex nodes, used to assert that derivative cycles stabilize.
    #[cfg(test)]
    pub(crate) fn regex_node_count(&self) -> usize {
        self.regexes.len()
    }
}
