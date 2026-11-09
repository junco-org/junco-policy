//! Numeric input provenance used by the executable tail-inclusion verdict.

use super::frontend::*;
use super::reconstruction::code_field;
use super::search_exec::{self as exec, root_vocabulary};
use super::*;
use super::{reconstruction as slots, typed_numeric as typed};
use crate::analyzer::{Constants, PolicyAnalyzer};
use crate::analyzer::{Counterexample, Inclusion};
use history_semantics::{
    SymbolicLanguage, compile_verify as numeric, symbolic_language_verify as facade,
    symbolic_verify as symbolic,
};
use history_syntax::Rule;
use junco_core::flat::FlatRule;
use junco_core::flat::{FlatHead, FlatPair, FlatTerm, FlatTest};
use junco_core::verify::dsl as tdsl;
use junco_core::verify::{encoding as enc, flatten as fl};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

pub(crate) open spec fn source_codes_wf<E: Event>(c: Constants<E>, source: FlatPair<u64>) -> bool {
    forall|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
        ==> match source.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            _ => true,
        }
}

pub(crate) open spec fn head_codes_wf<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>) -> bool {
    head.len() == 3 && forall|i: int| #![trigger head[i]] 0 <= i < 3 ==> match head[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat),
        _ => true,
    }
}

pub(crate) open spec fn constraint_codes_wf<E: Event>(c: Constants<E>, g: implementation::ConstraintView) -> bool {
    forall|field: Component, v: nat| #[trigger] register_codes(implementation::register_of(g, field)).contains(v)
        ==> code_field(c, field, v)
}

pub(crate) proof fn lemma_encoded_payload<E: Event>(c: Constants<E>, field: Component,
    value: ComponentValue<E>, id: u64)
    requires constants_wf(c), enc::encoded(constant_book(c), fl::component_equality::<E>(), field, value, id),
    ensures code_field(c, field, id as nat),
{
    lemma_field_book(c, field);
    let f = junco_core::flat::verify::field_index(field);
    let i = choose|i: int| 0 <= i < constant_book(c)[f].len()
        && constant_book(c)[f][i].1 == id
        && fl::component_equality::<E>()(field, value, constant_book(c)[f][i].0);
    lemma_field_entry_source(c.values@, field, i);
    let j = choose|j: int| 0 <= j < c.values@.len()
        && field_entries(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
    assert(id as nat == j + 1);
    assert(value_field(c.values@[j]) == field);
}

pub(crate) proof fn lemma_lowered_payload<E: Event>(c: Constants<E>, source: FlatPair<ComponentValue<E>>,
    target: FlatPair<u64>)
    requires constants_wf(c), enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
    ensures source_codes_wf(c, target), head_codes_wf(c, target.head@),
{
    assert forall|i: int| #![trigger target.tests@[i]] 0 <= i < target.tests@.len()
        implies match target.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            _ => true,
        } by {
        if let FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } = target.tests@[i] {
            let value = match source.tests@[i] {
                FlatTest::Atom { term: FlatTerm::Constant(value), .. } => value,
                _ => arbitrary(),
            };
            lemma_encoded_payload(c, field, value, v);
        }
    }
    assert forall|i: int| #![trigger target.head@[i]] 0 <= i < 3 implies match target.head@[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat), _ => true,
    } by {
        if let FlatHead::Constant(v) = target.head@[i] {
            let value = match source.head@[i] { FlatHead::Constant(value) => value, _ => arbitrary() };
            lemma_encoded_payload(c, enc::field_at(i), value, v);
        }
    }
}

pub(crate) proof fn lemma_append_payload<E: Event>(c: Constants<E>, before: FlatPair<u64>,
    source: FlatPair<u64>, after: FlatPair<u64>)
    requires source_codes_wf(c, before), source_codes_wf(c, source), table::frame(before, after),
        table::tests_copied(source, after, before.tests@.len(), source.tests@.len()),
        after.tests@.len() == before.tests@.len() + source.tests@.len(),
    ensures source_codes_wf(c, after),
{
    assert forall|i: int| #![trigger after.tests@[i]] 0 <= i < after.tests@.len() implies
        match after.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            _ => true,
        } by {
        if i < before.tests@.len() { assert(after.tests@[i] == before.tests@[i]); }
        else {
            let j = i - before.tests@.len();
            assert(table::test_shift(source.tests@[j], after.tests@[i], before.tests@.len()));
            match (source.tests@[j], after.tests@[i]) {
                (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {}, _ => {},
            }
        }
    }
}

pub(crate) proof fn lemma_root_payload<E: Event>(a: PolicyAnalyzer<E>, l: SymbolicLanguage,
    source: FlatPair<u64>, g: implementation::ConstraintView)
    requires source_codes_wf(a.constants, source), universes_wf(a.constants, a.universes),
        constraint_codes_wf(a.constants, g),
        symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))
            .subset_of(numeric::source_primitives(source)),
    ensures forall|field: Component, v: nat|
        root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
            ==> code_field(a.constants, field, v),
{
    let ps = symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)));
    facade::lemma_primitive_codes_mono(ps, numeric::source_primitives(source));
    assert forall|field: Component, v: nat|
        root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
        implies code_field(a.constants, field, v) by {
        let k = component_index(field) as int;
        match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        if facade::primitive_codes(ps, field).contains(v) {
            numeric::lemma_source_code_member(source, field, v);
            let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
                && match source.tests@[i] {
                    FlatTest::Atom { field: f, term: FlatTerm::Constant(code), .. } => f == field && code as nat == v,
                    _ => false,
                };
            match source.tests@[i] {
                FlatTest::Atom { field: f, term: FlatTerm::Constant(code), .. } => {
                    assert(code_field(a.constants, f, code as nat));
                    assert(code_field(a.constants, field, v));
                },
                _ => {},
            }
        } else if exec::domain_values(a.universes[k]).contains(v) {
            if let Some(ids) = a.universes[k] {
                let id = choose|id: u32| (*ids)@.to_set().contains(id) && id as nat == v;
                let j = choose|j: int| 0 <= j < (*ids)@.len() && (*ids)@[j] == id;
                assert(value_field(a.constants.values@[id as int - 1]) == field);
                assert(0 < id <= a.constants.values@.len());
                assert(code_field(a.constants, field, v));
            }
        } else {
            assert(register_codes(implementation::register_of(g, field)).contains(v));
            assert(code_field(a.constants, field, v));
        }
    }
}

pub(crate) proof fn lemma_root_fits<E: Event>(a: PolicyAnalyzer<E>, l: SymbolicLanguage,
    g: implementation::ConstraintView, bound: nat)
    requires a.constants.values@.len() <= bound,
        forall|field: Component, v: nat|
            root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
                ==> code_field(a.constants, field, v),
        forall|v: [Set<nat>; 3]| v[0].len() <= bound && v[1].len() <= bound && v[2].len() <= bound
            ==> #[trigger] exec::resource_capacity(v),
    ensures exec::search_fits(l, a.universes, g),
{
    let vocabulary = root_vocabulary(l, a.universes, g);
    let range = Set::<nat>::range(1, a.constants.values@.len() + 1);
    vstd::set_lib::range_set_properties::<nat>(1, a.constants.values@.len() + 1);
    assert forall|k: int| 0 <= k < 3 implies vocabulary[k].len() <= bound by {
        let field = component_of(k as usize);
        assert(component_index(field) == k);
        assert(vocabulary[k].subset_of(range)) by {
            assert forall|v: nat| vocabulary[k].contains(v) implies range.contains(v) by {
                assert(code_field(a.constants, field, v));
            }
        }
        vstd::set_lib::lemma_len_subset(vocabulary[k], range);
    }
    assert(exec::resource_capacity(vocabulary));
}
}

verus! {
pub(crate) struct TailInput<E: Event> {
    pub left: Rule<E>,
    pub right: Rule<E>,
    pub left_flat: FlatRule<ComponentValue<E>>,
    pub right_flat: FlatRule<ComponentValue<E>>,
    pub left_numeric: FlatPair<u64>,
    pub right_numeric: FlatPair<u64>,
}

pub(crate) open spec fn tail_input_wf<E: Event>(c: Constants<E>, i: TailInput<E>) -> bool {
    &&& i.left.head@ == i.right.head@
    &&& fl::flattened(i.left, i.left_flat) && fl::flattened(i.right, i.right_flat)
    &&& enc::constants_in_domain(i.left_flat.source, fl::component_domain::<E>())
    &&& enc::constants_in_domain(i.right_flat.source, fl::component_domain::<E>())
    &&& enc::lowering(i.left_flat.source, i.left_numeric, constant_book(c), fl::component_equality::<E>())
    &&& enc::lowering(i.right_flat.source, i.right_numeric, constant_book(c), fl::component_equality::<E>())
}

pub(crate) open spec fn difference_source<E: Event>(i: TailInput<E>, p: FlatPair<u64>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| numeric::source_regex(p, p.root as nat, theta, w)
        == (numeric::source_regex(i.left_numeric, i.left_numeric.root as nat, theta, w)
            && !numeric::source_regex(i.right_numeric, i.right_numeric.root as nat, theta, w))
}

pub(crate) open spec fn difference_language<E: Event>(i: TailInput<E>, q: language::Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta) ==> encoding::n_lang(theta, q, w)
        == (numeric::source_regex(i.left_numeric, i.left_numeric.root as nat, theta, w)
            && !numeric::source_regex(i.right_numeric, i.right_numeric.root as nat, theta, w))
}

pub(crate) open spec fn tail_ready<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>) -> bool {
    analyzer_state_wf(a) && analyzer_obligations::<E>() && tail_input_wf(a.constants, i) && difference_language(i, q)
}

pub(crate) open spec fn tail_verdict<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, r: Inclusion<E>) -> bool {
    analyzer::tail_included_ok(a@, i.left.head@, i.left.tail@, i.right.tail@, r@)
}

pub(crate) proof fn lemma_numeric_head_sat(h: encoding::NHead, theta: Subst)
    ensures inclusion::sat_by(theta, inclusion::head_constraint(h)) == encoding::n_head_matches(h, theta),
{
    inclusion::lemma_head_constraint(h);
    if encoding::n_head_matches(h, theta) {
        assert forall|l: inclusion::Literal| inclusion::head_constraint(h).contains(l)
            implies inclusion::literal_holds(theta, l) by {}
    } else if inclusion::sat_by(theta, inclusion::head_constraint(h)) {
        assert forall|c: Component| encoding::n_head_field(h, c) is Some
            implies language::field_value(theta, c) == encoding::n_head_field(h, c)->Some_0 by {
            if let Some(v) = encoding::n_head_field(h, c) {
                assert(inclusion::head_constraint(h).contains(inclusion::eq_literal(c, v)));
            }
        }
    }
}

pub(crate) proof fn lemma_empty_language(theta: Subst, w: Seq<EventView>)
    ensures !encoding::n_lang(theta, language::Regex::<model::Test>::Empty, w),
{ reveal_with_fuel(language::lang, 1); }

pub(crate) proof fn lemma_result_outcome(d: encoding::NDomains, start: search::Item, outcome: search::Outcome)
    requires exec::search_result(d, start, outcome),
    ensures search::outcome_ok(d, start.constraint, start.state, language::Regex::Empty, outcome),
{
    reveal(exec::search_result);
    assert(search::initial_ok(start.state, start.state, language::Regex::Empty)) by {
        assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta)
            implies encoding::n_lang(theta, start.state, w)
                == (encoding::n_lang(theta, start.state, w) && !encoding::n_lang(theta, language::Regex::Empty, w)) by {
            lemma_empty_language(theta, w);
        }
    }
}

proof fn lemma_embed_failure<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    -> (coding: typed::NatCoding<E>)
    requires tail_ready(a, i, q), semantics::event_in(a@.domains, c), semantics::history_in(a@.domains, h),
        analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h),
    ensures inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
        q, language::Regex::Empty, typed::numeric_event(coding, c), typed::numeric_history(coding, h)),
        typed::numeric_history(coding, h).len() == h.len(),
{
    let coding = typed::lemma_pair_embedding(a.constants, c, h);
    typed::lemma_analyzer_domain_embedding(a, coding, c, h);
    typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
        i.left_numeric, i.right_numeric, a.constants, coding, c, h);
    lemma_numeric_head_sat(typed::template_head(i.left_numeric), typed::numeric_event(coding, c));
    lemma_empty_language(typed::numeric_event(coding, c), typed::numeric_history(coding, h));
    coding
}

pub(crate) proof fn lemma_holds<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>)
    requires tail_ready(a, i, q), inclusion::included_under(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty),
    ensures analyzer::tail_included_ok(a@, i.left.head@, i.left.tail@, i.right.tail@, analyzer::InclusionView::Holds),
{
    assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
        semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
            implies !analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = lemma_embed_failure(a, i, q, c, h);
        }
    }
}

pub(crate) proof fn lemma_shortest<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>, n: nat)
    requires tail_ready(a, i, q), inclusion::no_cex_shorter(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty, n),
    ensures analyzer::shortest(a@, n, analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)),
{
    assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
        semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h) && h.len() < n
            implies !analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = lemma_embed_failure(a, i, q, c, h);
        }
    }
}

pub(crate) proof fn lemma_no_candidates<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(), tail_input_wf(a.constants, i),
        !inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))),
    ensures analyzer::tail_included_ok(a@, i.left.head@, i.left.tail@, i.right.tail@, analyzer::InclusionView::Holds),
{
    assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
        semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
            implies !analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = typed::lemma_pair_embedding(a.constants, c, h);
            typed::lemma_analyzer_domain_embedding(a, coding, c, h);
            typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
                i.left_numeric, i.right_numeric, a.constants, coding, c, h);
            let theta = typed::numeric_event(coding, c);
            lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
            assert(inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))));
        }
    }
}

pub(crate) proof fn lemma_counterexample<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires tail_ready(a, i, q), slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        search::outcome_ok(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)), q,
            language::Regex::Empty, search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets))),
    ensures analyzer::tail_included_ok(a@, i.left.head@, i.left.tail@, i.right.tail@, analyzer::InclusionView::Counterexample(result@)),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    assert forall|f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>|
        analyzer::admissible(a@, result@, f) implies {
            &&& semantics::event_in(a@.domains, analyzer::event_of(result@.candidate, f))
            &&& semantics::history_in(a@.domains, analyzer::history_of(result@, f))
            &&& analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(
                analyzer::event_of(result@.candidate, f), analyzer::history_of(result@, f))
        } by {
        let coding = typed::lemma_slot_embedding(a, candidate, history, f);
        let c = analyzer::event_of(result@.candidate, f);
        let h = analyzer::history_of(result@, f);
        let theta = typed::numeric_event(coding, c);
        let w = typed::numeric_history(coding, h);
        assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
        assert(encoding::n_event_in(ndomains(a.universes), theta));
        assert(search::follows(ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
        assert(encoding::n_history_in(ndomains(a.universes), w));
        assert(w.len() == h.len());
        typed::lemma_domain_event(a, coding, c);
        assert forall|j: int| 0 <= j < h.len() implies semantics::event_in(a@.domains, h[j]) by {
            assert(w[j] == typed::numeric_event(coding, h[j]));
            assert(encoding::n_event_in(ndomains(a.universes), w[j]));
            typed::lemma_domain_event(a, coding, h[j]);
        }
        assert(inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
            q, language::Regex::Empty, theta, w));
        lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
        typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
            i.left_numeric, i.right_numeric, a.constants, coding, c, h);
    }
    lemma_shortest(a, i, q, exec::chain_assignments(letters, alphabets).len());
    assert(result@.history.len() == exec::chain_assignments(letters, alphabets).len());
}
}

verus! {
pub(crate) open spec fn decision_ready<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, g: Constraint,
    difference: FlatPair<u64>) -> bool {
    &&& analyzer_state_wf(a) && analyzer_obligations::<E>() && tail_input_wf(a.constants, i)
    &&& source_codes_wf(a.constants, difference) && difference_source(i, difference)
    &&& constraint_wf(g) && constraint_codes_wf(a.constants, g@)
    &&& implementation::constraint_of(g@) == inclusion::head_constraint(typed::template_head(i.left_numeric))
    &&& inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(g@))
    &&& forall|v: [Set<nat>; 3]| v[0].len() <= a.constants.values@.len()
        && v[1].len() <= a.constants.values@.len() && v[2].len() <= a.constants.values@.len()
            ==> #[trigger] exec::resource_capacity(v)
}

pub(crate) proof fn lemma_universes_extended<E: Event>(before: Constants<E>, after: Constants<E>, u: Universes)
    requires analyzer_obligations::<E>(), constants_wf(before), constants_wf(after), universes_wf(before, u),
        enc::extends(constant_book(before), constant_book(after), fl::component_equality::<E>()),
    ensures universes_wf(after, u),
{
    assert forall|k: int| #![trigger u[k]] 0 <= k < 3 implies match u[k] {
        None => true,
        Some(ids) => (*ids)@.no_duplicates() && forall|j: int| 0 <= j < (*ids)@.len()
            ==> code_field(after, enc::field_at(k), (*ids)@[j] as nat),
    } by {
        if let Some(ids) = u[k] {
            assert forall|j: int| 0 <= j < (*ids)@.len()
                implies code_field(after, enc::field_at(k), (*ids)@[j] as nat) by {
                let id = (*ids)@[j];
                let value = before.values@[id as int - 1];
                assert(stored_code(before, value, id));
                lemma_stored_encoded(before, value, id);
                lemma_encoded_payload(after, enc::field_at(k), value, id as u64);
            }
        }
    }
}

pub(crate) proof fn lemma_head_payload<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>,
    constants: [Option<u32>; 3], g: Constraint)
    requires head_codes_wf(c, head), head_view(constants) == pins(head),
        forall|i: int| 0 <= i < 3 ==> g.0[i]@ == match constants[i] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        },
    ensures constraint_codes_wf(c, g@),
{
    assert forall|field: Component, v: nat| register_codes(implementation::register_of(g@, field)).contains(v)
        implies code_field(c, field, v) by {
        let k = component_index(field) as int;
        match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        assert(option_code(constants[k]) == encoding_head_code(head[k]));
        match constants[k] {
            Some(code) => { assert(head[k] == FlatHead::Constant(code as u64)); },
            None => { assert(!register_codes(implementation::register_of(g@, field)).contains(v)); },
        }
    }
}

pub(crate) proof fn lemma_refutation_input<E: Event>(a: PolicyAnalyzer<E>, start: search::Item,
    outcome: crate::search::SearchOutcome, vocabulary: [Set<nat>; 3])
    requires analyzer_state_wf(a), exec::search_result(ndomains(a.universes), start, exec::outcome_view(outcome)),
        exec::refutation_ready(outcome, a.universes, vocabulary),
        forall|field: Component, v: nat| vocabulary[component_index(field) as int].contains(v)
            ==> code_field(a.constants, field, v),
    ensures match outcome {
        crate::search::SearchOutcome::Holds => true,
        crate::search::SearchOutcome::Refuted(r) => slots::reconstruction_input(a.constants, a.universes,
            r.constraint, r.letters@, r.alphabets@),
    },
{
    reveal(exec::refutation_ready);
    lemma_result_outcome(ndomains(a.universes), start, exec::outcome_view(outcome));
    if let crate::search::SearchOutcome::Refuted(r) = outcome {
        assert forall|field: Component| slots::register_codes_ok(a.constants, field,
            implementation::register_of(r.constraint@, field)) by {
            assert forall|v: nat| register_codes(implementation::register_of(r.constraint@, field)).contains(v)
                implies code_field(a.constants, field, v) by {}
            match implementation::register_of(r.constraint@, field) {
                implementation::RegisterView::Equals(_) => {}, implementation::RegisterView::Differs(_) => {},
            }
        }
        assert forall|j: int| 0 <= j < r.letters@.len() implies
            slots::letter_codes_ok(a.constants, ndomains(a.universes), r.letters@[j]@, r.alphabets@[j]) by {
            exec::lemma_letter_payload(a.constants, vocabulary, a.universes, r.letters@[j]@, r.alphabets@[j]);
        }
        assert(inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(r.constraint@)));
    }
}
}
