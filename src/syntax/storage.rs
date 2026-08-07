//! Ownership root for interned names and hashconsed syntax.
//!
//! One `SyntaxContext` belongs to one validator. It borrows the caller's bump arena, owns the
//! mutable consignment tables, and retains canonical handles for algebraic constants. Hashconsed
//! nodes and compiled constant payloads live in the arena; the tables only discover or reuse those
//! immutable allocations.

use bumpalo::Bump;
use hashconsing::BHConsign;
use string_interner::DefaultStringInterner;

use super::identity::{ContextId, RuleScopeId};
use super::node::{RegexId, RegexKind, RegexNode, TestId, TestNode};

/// All mutable compilation and derivative state shared by a validator's rules.
pub(crate) struct SyntaxContext<'arena> {
    /// Reference-backed provenance identity carried by public syntax handles and checkpoints.
    pub(super) context_id: ContextId<'arena>,
    /// Global name interner. Equal variable names reuse symbols across rules, while `Scope` decides
    /// which symbols are valid in each individual rule.
    pub(super) variables: DefaultStringInterner,
    /// Canonical table for boolean event tests.
    pub(super) test_consign: BHConsign<'arena, TestNode<'arena>>,
    /// Canonical table for normalized regular-expression nodes.
    pub(super) regex_consign: BHConsign<'arena, RegexNode<'arena>>,
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

impl<'arena> SyntaxContext<'arena> {
    /// Creates empty consignment tables and seeds their algebraic constants.
    pub(crate) fn new(arena: &'arena Bump) -> Self {
        let context_id = ContextId::allocate(arena);

        let mut test_consign = BHConsign::with_capacity(arena, 128);
        let test_true = test_consign.mk(TestNode::True);
        let test_false = test_consign.mk(TestNode::False);

        let mut regex_consign = BHConsign::with_capacity(arena, 1024);
        let empty = regex_consign.mk(RegexNode::new(RegexKind::Empty, false));
        let all = regex_consign.mk(RegexNode::new(RegexKind::All, true));
        let epsilon = regex_consign.mk(RegexNode::new(RegexKind::Epsilon, true));

        Self {
            context_id,
            variables: DefaultStringInterner::with_capacity(64),
            test_consign,
            regex_consign,
            test_true,
            test_false,
            empty,
            all,
            epsilon,
        }
    }

    /// Returns the arena that owns every compiled payload and hashconsed node.
    pub(super) fn arena(&self) -> &'arena Bump {
        self.test_consign.arena()
    }

    /// Allocates a fresh provenance identity for one rule-local builder.
    pub(crate) fn new_rule_scope(&self) -> RuleScopeId<'arena> {
        RuleScopeId::allocate(self.arena())
    }

    /// Returns this validator's stable identity for checkpoint validation.
    pub(crate) fn identity(&self) -> ContextId<'arena> {
        self.context_id
    }

    /// Number of canonical regex nodes, used to assert that derivative cycles stabilize.
    #[cfg(test)]
    pub(crate) fn regex_node_count(&self) -> usize {
        self.regex_consign.len()
    }
}
