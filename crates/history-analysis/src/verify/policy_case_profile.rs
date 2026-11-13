//! Transfer of candidate constraint satisfaction across equal constant profiles.

use super::frontend::*;
use super::{self as views, reconstruction as slots, typed_numeric as typed, verdict};
use crate::analyzer::PolicyAnalyzer;
use crate::constraint::Constraint;
use history_semantics::verify::refinement::{analyzer, implementation, inclusion};
use history_syntax::event::specs::{EventSpec, arity};
use history_syntax::{Component, Event};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas,
    vstd::std_specs::vec::group_vec_axioms};

/// A covered typed value maps to a book code exactly when it equals that code's representative.
proof fn lemma_value_is_code<E: Event>(a: PolicyAnalyzer<E>, coding: typed::NatCoding<E>,
    event: Seq<E::Component>, field: Component, code: nat)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        typed::fixes_book::<E>(a.constants, coding), typed::covered_event::<E>(coding, event),
        field.0 < arity::<E>(), slots::code_field(a.constants, field, code),
    ensures (typed::numeric_event::<E>(coding, event)[field.0 as int] == code)
        == event[field.0 as int].eq_spec(&a.constants.values@[code as int - 1]),
{
    let k = field.0 as int;
    let value = a.constants.values@[code as int - 1];
    typed::lemma_native_equivalence::<E>();
    slots::lemma_code_payload(a.constants, field, code);
    lemma_stored_encoded(a.constants, value, code as u32);
    typed::lemma_fixed_code::<E>(a.constants, coding, field, value, code as u64);
    let eq = typed::native_eq::<E>();
    let i = choose|i: int| 0 <= i < coding[k].len() && eq(coding[k][i].0, event[k]);
    let j = choose|j: int| 0 <= j < coding[k].len() && eq(coding[k][j].0, value);
    typed::lemma_coding_reflects_eq(coding[k], eq, event[k], value, i, j);
    typed::lemma_numeric_field::<E>(coding, event, field);
}

/// Equal constant profiles put a second typed candidate in the same numeric constraint case.
pub(crate) proof fn lemma_same_profile_case<E: Event>(a: PolicyAnalyzer<E>, g: Constraint,
    first: Seq<E::Component>, second: Seq<E::Component>,
    first_coding: typed::NatCoding<E>, second_coding: typed::NatCoding<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        verdict::constraint_codes_wf(a.constants, g@),
        typed::fixes_book::<E>(a.constants, first_coding), typed::covered_event::<E>(first_coding, first),
        typed::fixes_book::<E>(a.constants, second_coding), typed::covered_event::<E>(second_coding, second),
        analyzer::same_profile(a@, first, second),
        inclusion::sat_by(typed::numeric_event::<E>(first_coding, first), implementation::constraint_of(g@)),
    ensures inclusion::sat_by(typed::numeric_event::<E>(second_coding, second), implementation::constraint_of(g@)),
{
    views::lemma_constraint_view(g@);
    assert forall|l: inclusion::Literal| implementation::constraint_of(g@).contains(l)
        implies inclusion::literal_holds(typed::numeric_event::<E>(second_coding, second), l) by {
        let k = l.component.0 as int;
        assert(views::register_codes(implementation::register_of(g@, l.component)).contains(l.value));
        let value = a.constants.values@[l.value as int - 1];
        slots::lemma_code_payload(a.constants, l.component, l.value);
        assert(a.constants.values@.to_set().contains(value));
        vstd::set::lemma_set_filter(a.constants.values@.to_set(),
            |v: E::Component| E::coordinate_spec(v) == k, value);
        assert(a@.known[k].contains(value));
        lemma_value_is_code(a, first_coding, first, l.component, l.value);
        lemma_value_is_code(a, second_coding, second, l.component, l.value);
        assert(first[k].eq_spec(&value) == second[k].eq_spec(&value));
    }
}
} // verus!
