//! Numeric input provenance of analyzer queries, and the typed reading of decided verdicts.

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

/// A template over known codes with component-local variables has primitives the search turns
/// into atoms without an internal error: constants are constant ids, variables are local.
pub(crate) proof fn lemma_source_primitives_safe<E: Event>(c: Constants<E>, source: FlatPair<u64>)
    requires constants_wf(c), source_codes_wf(c, source), table::local_vars(source),
    ensures exec::primitives_safe(numeric::source_primitives(source)),
{
    assert forall|p: model::Primitive| #[trigger] numeric::source_primitives(source).contains(p) implies match p {
        model::Primitive::Eq(k, model::GTerm::Constant(v)) => v <= u32::MAX,
        model::Primitive::Eq(k, model::GTerm::Variable(k2)) => k2 == k,
    } by {
        numeric::lemma_source_primitive_prefix(source, source.tests@.len(), p);
        let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len() && match source.tests@[i] {
            FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, numeric::term_view(term)),
            _ => false,
        };
        match source.tests@[i] {
            FlatTest::Atom { field, term, .. } => match term {
                FlatTerm::Constant(v) => { assert(code_field(c, field, v as nat)); },
                FlatTerm::Variable(k) => {},
            },
            _ => {},
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

/// A stored or query template's tail as a regular expression over kernel tests.
pub(crate) open spec fn tail_regex(t: FlatPair<u64>) -> language::Regex<model::Test> {
    policy::template_regex(t, t.root as nat)
}

/// Under a coding that covers the pair, a typed failure of `tail_included` is exactly a numeric
/// failure of its query `tail(left) ⊑_{Γ_head} tail(right)`.
proof fn lemma_tail_failure<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, coding: typed::NatCoding<E>,
    c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(), tail_input_wf(a.constants, i),
        table::dag(i.left_numeric), table::dag(i.right_numeric),
        typed::fixes_book(a.constants, coding), typed::covered_event(coding, c),
        forall|j: int| 0 <= j < h.len() ==> #[trigger] typed::covered_event(coding, h[j]),
    ensures analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h) == (
        inclusion::sat_by(typed::numeric_event(coding, c), inclusion::head_constraint(typed::template_head(i.left_numeric)))
        && encoding::n_lang(typed::numeric_event(coding, c), tail_regex(i.left_numeric), typed::numeric_history(coding, h))
        && !encoding::n_lang(typed::numeric_event(coding, c), tail_regex(i.right_numeric), typed::numeric_history(coding, h))),
{
    let theta = typed::numeric_event(coding, c);
    let w = typed::numeric_history(coding, h);
    typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
        i.left_numeric, i.right_numeric, a.constants, coding, c, h);
    lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
    super::firing::lemma_template_regex(i.left_numeric, i.left_numeric.root as nat, theta, w);
    super::firing::lemma_template_regex(i.right_numeric, i.right_numeric.root as nat, theta, w);
}

/// A typed failure of `tail_included` within the domains is a numeric counterexample of the same
/// length to its query.
proof fn lemma_tail_embedding<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>,
    c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    -> (r: (Subst, Seq<EventView>))
    requires analyzer_state_wf(a), analyzer_obligations::<E>(), tail_input_wf(a.constants, i),
        table::dag(i.left_numeric), table::dag(i.right_numeric),
        semantics::event_in(a@.domains, c), semantics::history_in(a@.domains, h),
        analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@)(c, h),
    ensures r.1.len() == h.len(), inclusion::inclusion_cex(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), tail_regex(i.left_numeric),
        tail_regex(i.right_numeric), r.0, r.1),
{
    let coding = typed::lemma_pair_embedding(a.constants, c, h);
    typed::lemma_analyzer_domain_embedding(a, coding, c, h);
    lemma_tail_failure(a, i, coding, c, h);
    (typed::numeric_event(coding, c), typed::numeric_history(coding, h))
}

/// `tail_included`'s contract from the verdict of its query.
pub(crate) proof fn lemma_tail_verdict<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>,
    g: implementation::ConstraintView, v: Inclusion<E>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(), tail_input_wf(a.constants, i),
        table::dag(i.left_numeric), table::dag(i.right_numeric),
        implementation::constraint_of(g) == inclusion::head_constraint(typed::template_head(i.left_numeric)),
        policy::decided(a, g, tail_regex(i.left_numeric), tail_regex(i.right_numeric), v),
    ensures analyzer::tail_included_ok(a@, i.left.head@, i.left.tail@, i.right.tail@, v@),
{
    let left = tail_regex(i.left_numeric);
    let right = tail_regex(i.right_numeric);
    let fails = analyzer::tail_fails(i.left.head@, i.left.tail@, i.right.tail@);
    match v {
        Inclusion::Holds => {
            assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
                semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
                implies !fails(c, h) by {
                if fails(c, h) {
                    let (theta, w) = lemma_tail_embedding(a, i, c, h);
                    assert(encoding::n_lang(theta, left, w));
                }
            }
        }
        Inclusion::Counterexample(cex) => {
            assert forall|f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>|
                #[trigger] analyzer::admissible(a@, cex@, f) implies
                    semantics::event_in(a@.domains, analyzer::event_of(cex@.candidate, f))
                    && semantics::history_in(a@.domains, analyzer::history_of(cex@, f))
                    && fails(analyzer::event_of(cex@.candidate, f), analyzer::history_of(cex@, f)) by {
                let coding = lemma_decided_instance(a, g, left, right, cex, f);
                lemma_tail_failure(a, i, coding, analyzer::event_of(cex@.candidate, f), analyzer::history_of(cex@, f));
            }
            lemma_decided_shortest(a, g, left, right, cex);
            assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
                semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h) && h.len() < cex@.history.len()
                implies !fails(c, h) by {
                if fails(c, h) {
                    let (theta, w) = lemma_tail_embedding(a, i, c, h);
                }
            }
        }
        Inclusion::Exhausted => {}
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
}

verus! {
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

verus! {
/// Search correctness for one query: a start state with the language of `left & ¬right` gives
/// `outcome_ok` for that query (`search::initial_ok`).
pub(crate) proof fn lemma_query_outcome(d: encoding::NDomains, start: search::Item,
    left: language::Regex<model::Test>, right: language::Regex<model::Test>, outcome: search::Outcome)
    requires exec::search_result(d, start, outcome), search::initial_ok(start.state, left, right),
    ensures search::outcome_ok(d, start.constraint, left, right, outcome),
{
    reveal(exec::search_result);
}

/// The refutation and slots behind a decided counterexample.
pub(crate) proof fn lemma_decided_slots<E: Event>(a: PolicyAnalyzer<E>, g: implementation::ConstraintView,
    left: language::Regex<model::Test>, right: language::Regex<model::Test>, cex: Counterexample<E>)
    -> (r: (Constraint, Seq<Letter>, Seq<Set<model::Primitive>>, Seq<implementation::SlotView>, Seq<Seq<implementation::SlotView>>))
    requires policy::decided(a, g, left, right, Inclusion::Counterexample(cex)),
    ensures slots::constructed(a.constants, a.universes, r.0, r.1, r.3, r.4),
        cex@ == slots::cex_of_slots(a.constants, r.3, r.4),
        implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(r.0@),
            exec::chain_assignments(r.1, r.2), r.3, r.4, slots::known_codes(a.constants)),
        search::outcome_ok(ndomains(a.universes), implementation::constraint_of(g), left, right,
            search::Outcome::Refuted(implementation::constraint_of(r.0@), exec::chain_assignments(r.1, r.2))),
        cex@.history.len() == r.4.len(), r.4.len() == r.1.len(),
        r.1.len() == exec::chain_assignments(r.1, r.2).len(),
{
    let (g1, letters, alphabets) = choose|g1: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>|
        #[trigger] slots::reconstructed(a.constants, a.universes, g1, letters, alphabets, cex)
        && search::outcome_ok(ndomains(a.universes), implementation::constraint_of(g), left, right,
            search::Outcome::Refuted(implementation::constraint_of(g1@), exec::chain_assignments(letters, alphabets)));
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g1, letters, candidate, history)
            && cex@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(g1@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    (g1, letters, alphabets, candidate, history)
}

/// Every admissible instance of a decided counterexample is, under a coding that fixes the
/// constant book, a numeric counterexample to the query `left ⊑_g right` within the domains.
pub(crate) proof fn lemma_decided_instance<E: Event>(a: PolicyAnalyzer<E>, g: implementation::ConstraintView,
    left: language::Regex<model::Test>, right: language::Regex<model::Test>, cex: Counterexample<E>,
    f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>) -> (coding: typed::NatCoding<E>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(),
        policy::decided(a, g, left, right, Inclusion::Counterexample(cex)),
        analyzer::admissible(a@, cex@, f),
    ensures ({
        let c = analyzer::event_of(cex@.candidate, f);
        let h = analyzer::history_of(cex@, f);
        let theta = typed::numeric_event(coding, c);
        let w = typed::numeric_history(coding, h);
        &&& typed::fixes_book(a.constants, coding)
        &&& typed::covered_event(coding, c)
        &&& forall|i: int| 0 <= i < h.len() ==> #[trigger] typed::covered_event(coding, h[i])
        &&& semantics::event_in(a@.domains, c)
        &&& semantics::history_in(a@.domains, h)
        &&& w.len() == h.len()
        &&& inclusion::inclusion_cex(ndomains(a.universes), implementation::constraint_of(g), left, right, theta, w)
    }),
{
    let (g1, letters, alphabets, candidate, history) = lemma_decided_slots(a, g, left, right, cex);
    let coding = typed::lemma_slot_embedding(a, candidate, history, f);
    let c = analyzer::event_of(cex@.candidate, f);
    let h = analyzer::history_of(cex@, f);
    let theta = typed::numeric_event(coding, c);
    let w = typed::numeric_history(coding, h);
    assert(inclusion::sat_by(theta, implementation::constraint_of(g1@)));
    assert(encoding::n_event_in(ndomains(a.universes), theta));
    assert(search::follows(ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
    assert(encoding::n_history_in(ndomains(a.universes), w));
    assert(w.len() == h.len());
    typed::lemma_domain_event(a, coding, c);
    assert forall|j: int| 0 <= j < h.len() implies #[trigger] semantics::event_in(a@.domains, h[j]) by {
        assert(w[j] == typed::numeric_event(coding, h[j]));
        assert(encoding::n_event_in(ndomains(a.universes), w[j]));
        typed::lemma_domain_event(a, coding, h[j]);
    }
    assert(inclusion::inclusion_cex(ndomains(a.universes), implementation::constraint_of(g), left, right, theta, w));
    coding
}

/// No counterexample to the query is shorter than a decided counterexample.
pub(crate) proof fn lemma_decided_shortest<E: Event>(a: PolicyAnalyzer<E>, g: implementation::ConstraintView,
    left: language::Regex<model::Test>, right: language::Regex<model::Test>, cex: Counterexample<E>)
    requires policy::decided(a, g, left, right, Inclusion::Counterexample(cex)),
    ensures inclusion::no_cex_shorter(ndomains(a.universes), implementation::constraint_of(g), left, right,
        cex@.history.len()),
{
    let (g1, letters, alphabets, candidate, history) = lemma_decided_slots(a, g, left, right, cex);
}

/// A decided counterexample uses fresh numbers only at components without a declared universe.
pub(crate) proof fn lemma_decided_fresh<E: Event>(a: PolicyAnalyzer<E>, g: implementation::ConstraintView,
    left: language::Regex<model::Test>, right: language::Regex<model::Test>, cex: Counterexample<E>)
    requires policy::decided(a, g, left, right, Inclusion::Counterexample(cex)),
    ensures analyzer::fresh_unrestricted(a@.domains, cex@),
{
    let (g1, letters, alphabets, candidate, history) = lemma_decided_slots(a, g, left, right, cex);
    let v = cex@;
    assert forall|k: int, n: nat| 0 <= k < 3 && a.universes[k] is Some implies
        candidate[k] != implementation::SlotView::Fresh(n)
        && forall|i: int| 0 <= i < history.len() ==> #[trigger] history[i][k] != implementation::SlotView::Fresh(n) by {
        assert(slots::candidate_field_ok(a.constants, a.universes, g1, k, candidate[k]));
        assert forall|i: int| 0 <= i < history.len() implies #[trigger] history[i][k] != implementation::SlotView::Fresh(n) by {
            assert(slots::slot_domain(history[i][k], domain_view(a.universes[k])));
        }
    }
    if a.universes[0] is Some {
        assert(analyzer::fresh_used(v, |c: analyzer::ComponentsView<E::Principal, E::Action, E::Resource>| c.principal)
            =~= ISet::<nat>::empty()) by {
            assert forall|n: nat| !(v.candidate.principal == analyzer::ValueView::<E::Principal>::Fresh(n)
                || exists|i: int| 0 <= i < v.history.len() && #[trigger] v.history[i].principal == analyzer::ValueView::<E::Principal>::Fresh(n)) by {
                assert(candidate[0] != implementation::SlotView::Fresh(n));
                assert forall|i: int| 0 <= i < v.history.len() implies #[trigger] v.history[i].principal != analyzer::ValueView::<E::Principal>::Fresh(n) by {
                    assert(history[i][0] != implementation::SlotView::Fresh(n));
                    assert(slots::slot_wf(a.constants, history[i]));
                    assert(v.history[i] == slots::components_of_slots(a.constants, history[i]));
                }
            }
        }
    }
    if a.universes[1] is Some {
        assert(analyzer::fresh_used(v, |c: analyzer::ComponentsView<E::Principal, E::Action, E::Resource>| c.action)
            =~= ISet::<nat>::empty()) by {
            assert forall|n: nat| !(v.candidate.action == analyzer::ValueView::<E::Action>::Fresh(n)
                || exists|i: int| 0 <= i < v.history.len() && #[trigger] v.history[i].action == analyzer::ValueView::<E::Action>::Fresh(n)) by {
                assert(candidate[1] != implementation::SlotView::Fresh(n));
                assert forall|i: int| 0 <= i < v.history.len() implies #[trigger] v.history[i].action != analyzer::ValueView::<E::Action>::Fresh(n) by {
                    assert(history[i][1] != implementation::SlotView::Fresh(n));
                    assert(slots::slot_wf(a.constants, history[i]));
                    assert(v.history[i] == slots::components_of_slots(a.constants, history[i]));
                }
            }
        }
    }
    if a.universes[2] is Some {
        assert(analyzer::fresh_used(v, |c: analyzer::ComponentsView<E::Principal, E::Action, E::Resource>| c.resource)
            =~= ISet::<nat>::empty()) by {
            assert forall|n: nat| !(v.candidate.resource == analyzer::ValueView::<E::Resource>::Fresh(n)
                || exists|i: int| 0 <= i < v.history.len() && #[trigger] v.history[i].resource == analyzer::ValueView::<E::Resource>::Fresh(n)) by {
                assert(candidate[2] != implementation::SlotView::Fresh(n));
                assert forall|i: int| 0 <= i < v.history.len() implies #[trigger] v.history[i].resource != analyzer::ValueView::<E::Resource>::Fresh(n) by {
                    assert(history[i][2] != implementation::SlotView::Fresh(n));
                    assert(slots::slot_wf(a.constants, history[i]));
                    assert(v.history[i] == slots::components_of_slots(a.constants, history[i]));
                }
            }
        }
    }
}
}

verus! {
/// The language of `firing_denials`: the denials of the rules whose head the case entails.
pub(crate) proof fn lemma_firing_language(d: encoding::NDomains, p: Seq<encoding::NRule>, g: inclusion::Constraint,
    theta: Subst, w: Seq<EventView>)
    ensures encoding::n_lang(theta, inclusion::firing_denials(d, p, g), w)
        == exists|k: int| 0 <= k < p.len() && #[trigger] inclusion::entails(d, g, inclusion::head_constraint(p[k].head))
            && encoding::n_lang(theta, inclusion::denial(p[k]), w),
{
    let pred = |r: encoding::NRule| inclusion::entails(d, g, inclusion::head_constraint(r.head));
    let firing = p.filter(pred);
    let cs = firing.map(|i: int, r: encoding::NRule| inclusion::denial(r));
    reveal_with_fuel(language::lang, 1);
    assert(inclusion::firing_denials(d, p, g) == language::Regex::Union(cs));
    if encoding::n_lang(theta, inclusion::firing_denials(d, p, g), w) {
        let i = choose|i: int| 0 <= i < cs.len() && language::lang(model::gsem(theta), cs[i], w);
        p.lemma_filter_contains_rev(pred, firing[i]);
        let k = choose|k: int| 0 <= k < p.len() && p[k] == firing[i];
        assert(inclusion::entails(d, g, inclusion::head_constraint(p[k].head)));
    }
    if exists|k: int| 0 <= k < p.len() && #[trigger] inclusion::entails(d, g, inclusion::head_constraint(p[k].head))
        && encoding::n_lang(theta, inclusion::denial(p[k]), w) {
        let k = choose|k: int| 0 <= k < p.len() && #[trigger] inclusion::entails(d, g, inclusion::head_constraint(p[k].head))
            && encoding::n_lang(theta, inclusion::denial(p[k]), w);
        p.lemma_filter_contains(pred, k);
        let i = choose|i: int| 0 <= i < firing.len() && firing[i] == p[k];
        assert(cs[i] == inclusion::denial(p[k]));
        assert(language::lang(model::gsem(theta), cs[i], w));
    }
}

/// A rule's denial: its tail, or the complement of its tail for `require`.
pub(crate) proof fn lemma_denial_language(rule: encoding::NRule, theta: Subst, w: Seq<EventView>)
    ensures encoding::n_lang(theta, inclusion::denial(rule), w) == match rule.mode {
        history_syntax::RuleMode::Forbid => encoding::n_lang(theta, rule.tail, w),
        history_syntax::RuleMode::Require => !encoding::n_lang(theta, rule.tail, w),
    },
{
    reveal_with_fuel(language::lang, 1);
}

/// `policy_capacity` bounds the per-state products of every search over the book.
pub(crate) proof fn lemma_policy_resources<E: Event>(a: PolicyAnalyzer<E>)
    requires policy::policy_capacity(a),
    ensures forall|v: [Set<nat>; 3]| v[0].len() <= a.constants.values@.len()
        && v[1].len() <= a.constants.values@.len() && v[2].len() <= a.constants.values@.len()
            ==> #[trigger] exec::resource_capacity(v),
{
    let count = a.constants.values@.len();
    let m = count + 2;
    assert forall|v: [Set<nat>; 3]| v[0].len() <= count && v[1].len() <= count && v[2].len() <= count
        implies #[trigger] exec::resource_capacity(v) by {
        let x = v[0].len() + 2; let y = v[1].len() + 2; let z = v[2].len() + 2;
        assert(m <= m * m * m && x * y <= m * m * m && x * y * z <= m * m * m) by(nonlinear_arith)
            requires x <= m, y <= m, z <= m, 2 <= x, 2 <= y, 2 <= z;
    }
}
}
