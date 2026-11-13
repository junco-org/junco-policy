//! Transfer of numeric cases across real candidates' bounded constant profiles.

use super::frontend::*;
use super::{self as views, reconstruction as slots, typed_numeric as typed, verdict};
use crate::analyzer::PolicyAnalyzer;
use crate::constraint::Constraint;
use history_semantics::verify::refinement::{implementation, inclusion};
use history_syntax::spec::events::{arity, event_view};
use history_syntax::{Component, Event};
use junco_core::spec::questions as q;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas,
    vstd::std_specs::vec::group_vec_axioms, crate::verify::frontend::domain_view::lemma_analyzer_view};

proof fn lemma_value_is_code<E: Event>(a: PolicyAnalyzer<E>, coding: typed::NatCoding<E>,
    event: E, field: Component, code: nat, known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        typed::fixes_known::<E>(a.constants, coding, known), typed::covered_event::<E>(coding, event_view(event)),
        field.0 < arity::<E>(), slots::code_field(a.constants, field, code),
        typed::known_value::<E>(known, field.0 as int, a.constants.values@[code as int - 1]),
    ensures (typed::numeric_event::<E>(coding, event_view(event))[field.0 as int] == code)
        == event_view(event)[field.0 as int].eq_spec(&a.constants.values@[code as int - 1]),
{
    let k = field.0 as int;
    let projected = event_view(event);
    let value = a.constants.values@[code as int - 1];
    typed::lemma_native_equivalence::<E>();
    slots::lemma_code_payload(a.constants, field, code);
    q::lemma_native_eq_reflexive(value);
    lemma_stored_encoded(a.constants, value, code as u32);
    typed::lemma_known_code::<E>(a.constants, coding, field, value, code as u64, known);
    let eq = typed::native_eq::<E>();
    let i = choose|i: int| 0 <= i < coding[k].len() && eq(coding[k][i].0, projected[k]);
    let j = choose|j: int| 0 <= j < coding[k].len() && eq(coding[k][j].0, value);
    typed::lemma_coding_reflects_eq(coding[k], eq, projected[k], value, i, j);
    typed::lemma_numeric_field::<E>(coding, projected, field);
}

/// Equal profiles are taken against the returned context, not the entire native codebook.
pub(crate) proof fn lemma_same_profile_case<E: Event>(a: PolicyAnalyzer<E>, g: Constraint,
    first: E, second: E, first_coding: typed::NatCoding<E>, second_coding: typed::NatCoding<E>,
    known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        verdict::constraint_codes_wf(a.constants, g@), verdict::constraint_codes_known(a.constants, g@, known),
        typed::fixes_known::<E>(a.constants, first_coding, known), typed::covered_event::<E>(first_coding, event_view(first)),
        typed::fixes_book::<E>(a.constants, second_coding), typed::covered_event::<E>(second_coding, event_view(second)),
        q::same_profile(known, first, second),
        inclusion::sat_by(typed::numeric_event::<E>(first_coding, event_view(first)), implementation::constraint_of(g@)),
    ensures inclusion::sat_by(typed::numeric_event::<E>(second_coding, event_view(second)), implementation::constraint_of(g@)),
{
    typed::lemma_book_fixes_known(a.constants, second_coding, known);
    typed::lemma_native_equivalence::<E>();
    views::lemma_constraint_view(g@);
    assert forall|l: inclusion::Literal| implementation::constraint_of(g@).contains(l)
        implies inclusion::literal_holds(typed::numeric_event::<E>(second_coding, event_view(second)), l) by {
        let k = l.component.0 as int;
        assert(views::register_codes(implementation::register_of(g@, l.component)).contains(l.value));
        assert(implementation::register_of(g@, l.component) == g@[k]);
        assert(typed::known_value::<E>(known, k, a.constants.values@[l.value as int - 1]));
        let value = a.constants.values@[l.value as int - 1];
        slots::lemma_code_payload(a.constants, l.component, l.value);
        let constant = choose|constant: E::Component| known[k].contains(constant) && value.eq_spec(&constant);
        assert(event_view(first)[k].eq_spec(&constant) == event_view(second)[k].eq_spec(&constant));
        q::lemma_native_eq_symmetric(value, constant);
        if event_view(first)[k].eq_spec(&value) {
            q::lemma_native_eq_transitive(event_view(first)[k], value, constant);
        }
        if event_view(first)[k].eq_spec(&constant) {
            q::lemma_native_eq_transitive(event_view(first)[k], constant, value);
        }
        if event_view(second)[k].eq_spec(&value) {
            q::lemma_native_eq_transitive(event_view(second)[k], value, constant);
        }
        if event_view(second)[k].eq_spec(&constant) {
            q::lemma_native_eq_transitive(event_view(second)[k], constant, value);
        }
        assert(event_view(first)[k].eq_spec(&value) == event_view(second)[k].eq_spec(&value));
        lemma_value_is_code(a, first_coding, first, l.component, l.value, known);
        lemma_value_is_code(a, second_coding, second, l.component, l.value, known);
    }
}
}
