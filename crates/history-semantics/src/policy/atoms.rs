//! One-event [`TestExpr`] building blocks every policy's predicates are assembled from.
//!
//! Head variables are the string names [`PRINCIPAL_VAR`] and [`RESOURCE_VAR`]; a rule head binds
//! them and a tail atom refers back to them.

use alloc::string::String;
use history_syntax::{AtomPattern, Comparison, ComponentPattern, Event, TestExpr};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use history_syntax::verify::dsl::{AtomView, PatternView, TestView};

verus! {
/// Head variable bound to the acting principal.
pub(super) const PRINCIPAL_VAR: &'static str = "p";
/// Head variable bound to the candidate's resource.
pub(super) const RESOURCE_VAR: &'static str = "r";
}

/// An event whose principal compares against the head-bound principal `p`.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView::Principal(PatternView::Variable(seq!['p'])),
}))]
pub fn principal_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    proof! {
        reveal_strlit("p");
        assert(PRINCIPAL_VAR@ == seq!['p']);
    }
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::Variable(String::from_str(PRINCIPAL_VAR))),
    )
}

/// An event whose resource compares against the head-bound resource `r`.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView::Resource(PatternView::Variable(seq!['r'])),
}))]
pub fn resource_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    proof! {
        reveal_strlit("r");
        assert(RESOURCE_VAR@ == seq!['r']);
    }
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::Variable(String::from_str(RESOURCE_VAR))),
    )
}

/// An event whose action compares against the constant `action`.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView::Action(PatternView::Constant(action)),
}))]
pub fn action_is<E: Event>(action: E::Action, comparison: Comparison) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::Constant(action)),
    )
}
