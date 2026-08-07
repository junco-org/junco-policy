//! Canonical storage for compiled tests and regular expressions.
//!
//! The store owns name and node interning tables and borrows only the caller-provided allocation
//! arena. It has no active-rule, variable-environment, candidate, history, or validator
//! backreferences. Compiler and evaluator functions receive the store explicitly.

use std::collections::HashSet;

use bumpalo::Bump;
use hashconsing::BHConsign;

use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};
use super::variable::VariableName;

/// Shared canonical node store used by all compiled rules in one validator.
pub(crate) struct CanonicalStore<'arena> {
    /// Arena-backed variable spellings shared by compiled rules.
    pub(super) variables: HashSet<VariableName<'arena>>,
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
    /// Creates empty consignment tables and seeds their algebraic constants.
    pub(crate) fn new(arena: &'arena Bump) -> Self {
        let mut tests = BHConsign::with_capacity(arena, 128);
        let test_true = tests.mk(TestNode::True);
        let test_false = tests.mk(TestNode::False);

        let mut regexes = BHConsign::with_capacity(arena, 1024);
        let empty = regexes.mk(RegexNode::new(RegexKind::Empty, false));
        let all = regexes.mk(RegexNode::new(RegexKind::All, true));
        let epsilon = regexes.mk(RegexNode::new(RegexKind::Epsilon, true));

        Self {
            variables: HashSet::with_capacity(64),
            tests,
            regexes,
            test_true,
            test_false,
            empty,
            all,
            epsilon,
        }
    }

    /// Returns the arena that owns every compiled payload and canonical node.
    pub(super) fn arena(&self) -> &'arena Bump {
        self.tests.arena()
    }

    /// Returns one stable reference for each distinct variable spelling.
    pub(super) fn intern_variable(&mut self, name: &str) -> VariableName<'arena> {
        if let Some(variable) = self.variables.get(name).copied() {
            return variable;
        }
        let variable = VariableName::new(self.arena().alloc_str(name));
        self.variables.insert(variable);
        variable
    }

    /// Number of canonical regex nodes, used to assert that derivative cycles stabilize.
    #[cfg(test)]
    pub(crate) fn regex_node_count(&self) -> usize {
        self.regexes.len()
    }
}
