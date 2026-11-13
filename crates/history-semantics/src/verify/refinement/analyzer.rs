//! Fresh-capacity non-vacuity for the canonical real-event counterexample model.
//!
//! R3 owns symbolic values, shared tagged choices, real-event instances and case-local
//! minimality. R6 owns executable query verdicts; this layer proves the reusable
//! existence statement without retaining a second analyzer view or interpreter.

use history_syntax::Event;
use history_syntax::spec::events::surjectivity;
use junco_core::spec::hypotheses::eq_equivalence;
use junco_core::spec::questions::{self as q, Counterexample, Domains};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// Every well-formed symbolic pair with its own fresh capacity has a real-event instance.
pub open spec fn stmt_choice_exists<E: Event>() -> bool {
    forall|domains: Domains<E::Component>, cex: Counterexample<E::Component>|
        #[trigger] q::counterexample_wf::<E>(domains, cex)
            && q::counterexample_capacity::<E>(domains, cex)
            && surjectivity::<E>()
            && eq_equivalence::<E::Component>(
                |left: E::Component, right: E::Component| left.eq_spec(&right),
                |_value: E::Component| true)
        ==> q::has_instance::<E>(domains, cex)
}

/// Capacity counts distinct used fresh names, not their maximum numeric identifier.
pub proof fn theorem_choice_exists<E: Event>()
    ensures stmt_choice_exists::<E>(),
{
    assert forall|domains: Domains<E::Component>, cex: Counterexample<E::Component>|
        #[trigger] q::counterexample_wf::<E>(domains, cex)
            && q::counterexample_capacity::<E>(domains, cex)
            && surjectivity::<E>()
            && eq_equivalence::<E::Component>(
                |left: E::Component, right: E::Component| left.eq_spec(&right),
                |_value: E::Component| true)
        implies q::has_instance::<E>(domains, cex) by {
        q::lemma_counterexample_has_instance::<E>(domains, cex);
    }
}

} // verus!
