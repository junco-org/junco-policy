//! Reference-backed identities for syntax provenance.
//!
//! Public [`Test`](super::Test) and [`Regex`](super::Regex) handles carry two provenance
//! identities: the syntax context that owns their hashconsed node and the rule scope that bound
//! their variables. Both identities are stable references to arena allocations. Comparing the
//! references by address prevents handles from crossing contexts or rule scopes without assigning
//! integer identifiers or maintaining another lookup table.

use std::fmt;
use std::hash::{Hash, Hasher};

use bumpalo::Bump;

/// Non-zero-sized allocation whose address identifies one syntax context.
#[derive(Debug)]
struct ContextToken {
    _addressable: u8,
}

/// Non-zero-sized allocation whose address identifies one rule-local variable scope.
#[derive(Debug)]
struct RuleScopeToken {
    _addressable: u8,
}

/// Identity of one [`SyntaxContext`](super::storage::SyntaxContext).
///
/// Equality and hashing use the allocation address, not the token's value.
#[derive(Clone, Copy)]
pub(crate) struct ContextId<'arena>(&'arena ContextToken);

impl<'arena> ContextId<'arena> {
    /// Allocates a fresh context identity in `arena`.
    pub(super) fn allocate(arena: &'arena Bump) -> Self {
        Self(arena.alloc(ContextToken { _addressable: 0 }))
    }
}

impl PartialEq for ContextId<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for ContextId<'_> {}

impl Hash for ContextId<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state);
    }
}

impl fmt::Debug for ContextId<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("ContextId")
            .field(&(self.0 as *const ContextToken))
            .finish()
    }
}

/// Identity of one rule's variable-binding scope.
///
/// A scope identity is deliberately distinct from [`ContextId`], so the compiler cannot mix the
/// two provenance checks. Equality and hashing use pointer identity.
#[derive(Clone, Copy)]
pub(crate) struct RuleScopeId<'arena>(&'arena RuleScopeToken);

impl<'arena> RuleScopeId<'arena> {
    /// Allocates a fresh rule-scope identity in `arena`.
    pub(super) fn allocate(arena: &'arena Bump) -> Self {
        Self(arena.alloc(RuleScopeToken { _addressable: 0 }))
    }
}

impl PartialEq for RuleScopeId<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for RuleScopeId<'_> {}

impl Hash for RuleScopeId<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state);
    }
}

impl fmt::Debug for RuleScopeId<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("RuleScopeId")
            .field(&(self.0 as *const RuleScopeToken))
            .finish()
    }
}
