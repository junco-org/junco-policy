//! Numeric decision certificates, reconstruction provenance, and the tail-inclusion client.

use super::frontend::*;
use super::reconstruction::code_field;
use super::search_exec::{self as exec, root_vocabulary};
use super::*;
use super::{policy_bridge as bridge, reconstruction as slots, typed_numeric as typed};
use crate::analyzer::{Constants, PolicyAnalyzer};
use crate::analyzer::{Counterexample, Inclusion, NumericDecision};
use crate::spec::analyzer::{tail_fails, tail_included_spec};
use history_semantics::{
    SymbolicLanguage, compile_verify as numeric, symbolic_language_verify as facade,
    symbolic_verify as symbolic,
};
use history_syntax::Rule;
use history_syntax::spec::events::{arity, event_view};
use junco_core::flat::FlatRule;
use junco_core::flat::{FlatHead, FlatPair, FlatTerm, FlatTest};
use junco_core::spec::questions::{
    FreshChoice, InclusionView, admissible, capacity_for, cex_arity, cex_has_instance, in_domains,
    instantiates, shortest, tails_included,
};
use junco_core::spec::semantics::history_view;
use junco_core::verify::{encoding as enc, flatten as fl};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

pub(crate) open spec fn test_fields_bounded<C>(test: FlatTest<C>, arity: nat) -> bool {
    match test {
        FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } =>
            field.0 < arity && variable.0 < arity,
        FlatTest::Atom { field, .. } => field.0 < arity,
        _ => true,
    }
}

/// Numeric table heads may be all `Any`; only field bounds, not binder declarations, are needed.
pub(crate) open spec fn source_fields_bounded<C>(source: FlatPair<C>) -> bool {
    1 <= source.head@.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < source.tests@.len() ==>
            test_fields_bounded(#[trigger] source.tests@[i], source.head@.len())
}

pub(crate) proof fn lemma_source_fields_bounded(source: FlatPair<u64>)
    requires source_fields_bounded(source),
    ensures search::atoms_bounded(numeric::source_primitives(source), source.head@.len()),
{
    assert forall|p: model::Primitive| numeric::source_primitives(source).contains(p) implies match p {
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < source.head@.len(),
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < source.head@.len() && v.0 < source.head@.len(),
    } by {
        numeric::lemma_source_primitive_prefix(source, source.tests@.len(), p);
        let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len() && match source.tests@[i] {
            FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, numeric::term_view(term)),
            _ => false,
        };
        assert(test_fields_bounded(source.tests@[i], source.head@.len()));
        match source.tests@[i] {
            FlatTest::Atom { term: FlatTerm::Constant(_), .. } => {},
            FlatTest::Atom { term: FlatTerm::Variable(_), .. } => {},
            _ => {},
        }
    }
}

pub(crate) open spec fn source_codes_wf<E: Event>(c: Constants<E>, source: FlatPair<u64>) -> bool {
    &&& source.head@.len() == arity::<E>()
    &&& source_fields_bounded(source)
    &&& forall|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
        ==> match source.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
            _ => true,
        }
}

pub(crate) open spec fn head_codes_wf<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>) -> bool {
    head.len() == arity::<E>() && forall|i: int| #![trigger head[i]] 0 <= i < head.len() ==> match head[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat),
        _ => true,
    }
}

pub(crate) open spec fn constraint_codes_wf<E: Event>(c: Constants<E>, g: implementation::ConstraintView) -> bool {
    g.len() == arity::<E>() && forall|field: Component, v: nat| field.0 < g.len()
        && #[trigger] register_codes(implementation::register_of(g, field)).contains(v)
            ==> code_field(c, field, v)
}

pub(crate) proof fn lemma_encoded_payload<E: Event>(c: Constants<E>, field: Component,
    value: E::Component, id: u64)
    requires constants_wf(c), enc::encoded(constant_book(c), fl::component_equality::<E>(), field, value, id),
    ensures code_field(c, field, id as nat),
{
    lemma_field_book(c, field);
    let f = junco_core::flat::verify::field_index(field);
    let i = choose|i: int| 0 <= i < constant_book(c)[f].len()
        && constant_book(c)[f][i].1 == id
        && fl::component_equality::<E>()(field, value, constant_book(c)[f][i].0);
    lemma_field_entry_source::<E>(c.values@, field, i);
    let j = choose|j: int| 0 <= j < c.values@.len()
        && field_entries::<E>(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
    assert(id as nat == j + 1);
    assert(value_field::<E>(c.values@[j]) == field);
}

pub(crate) proof fn lemma_lowered_payload<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>)
    requires constants_wf(c), enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        source.head@.len() == arity::<E>(), junco_core::flat::verify::structural_wf(source),
    ensures source_codes_wf(c, target), head_codes_wf(c, target.head@), source_fields_bounded(target),
{
    assert forall|i: int| #![trigger target.tests@[i]] 0 <= i < target.tests@.len()
        implies match target.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
            _ => true,
        } by {
        if let FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } = target.tests@[i] {
            let value = match source.tests@[i] {
                FlatTest::Atom { term: FlatTerm::Constant(value), .. } => value,
                _ => arbitrary(),
            };
            lemma_encoded_payload(c, field, value, v);
        } else {
            assert(junco_core::flat::verify::test_wf(source.head@, source.tests@[i], i as nat));
            match (source.tests@[i], target.tests@[i]) {
                (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {},
                _ => {},
            }
    }
    }
    assert forall|i: int| #![trigger target.head@[i]] 0 <= i < target.head@.len() implies match target.head@[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat), _ => true,
    } by {
        if let FlatHead::Constant(v) = target.head@[i] {
            let value = match source.head@[i] { FlatHead::Constant(value) => value, _ => arbitrary() };
            lemma_encoded_payload(c, enc::field_at(i), value, v);
        }
    }
    assert forall|i: int| 0 <= i < target.tests@.len() implies
        test_fields_bounded(target.tests@[i], target.head@.len()) by {
        assert(junco_core::flat::verify::test_wf(source.head@, source.tests@[i], i as nat));
        match (source.tests@[i], target.tests@[i]) {
            (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {},
            _ => {},
        }
    }
}

pub(crate) proof fn lemma_append_payload<E: Event>(c: Constants<E>, before: FlatPair<u64>,
    source: FlatPair<u64>, after: FlatPair<u64>)
    requires source_codes_wf(c, before), source_codes_wf(c, source), table::frame(before, after),
        table::tests_copied(source, after, before.tests@.len(), source.tests@.len()),
        after.tests@.len() == before.tests@.len() + source.tests@.len(),
        source_fields_bounded(before), source_fields_bounded(source),
        after.head@.len() == before.head@.len(), after.head@.len() == source.head@.len(),
    ensures source_codes_wf(c, after), source_fields_bounded(after),
{
    assert forall|i: int| #![trigger after.tests@[i]] 0 <= i < after.tests@.len() implies
        test_fields_bounded(after.tests@[i], after.head@.len())
            && match after.tests@[i] {
                FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
                FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
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
        constants_wf(a.constants),
        constraint_codes_wf(a.constants, g),
        source_fields_bounded(source), source.head@.len() == a.universes@.len(),
        symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))
            .subset_of(numeric::source_primitives(source)),
    ensures g.len() == a.universes@.len(),
        root_vocabulary(l, a.universes, g).len() == arity::<E>(),
        search::atoms_bounded(symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l))), a.universes@.len()),
        facade::primitives_search_safe(symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))),
        forall|field: Component, v: nat|
            field.0 < a.universes@.len() && root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
                ==> code_field(a.constants, field, v),
{
    let ps = symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)));
    facade::lemma_primitive_codes_mono(ps, numeric::source_primitives(source));
    lemma_source_fields_bounded(source);
    assert forall|p: model::Primitive| ps.contains(p) implies match p {
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < a.universes@.len(),
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < a.universes@.len() && v.0 < a.universes@.len(),
    } by { assert(numeric::source_primitives(source).contains(p)); }
    assert forall|p: model::Primitive| ps.contains(p) implies match p {
        model::Primitive::Eq(_, model::GTerm::Constant(v)) => v <= u32::MAX,
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c == v,
    } by {
        numeric::lemma_source_primitive_prefix(source, source.tests@.len(), p);
        let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
            && match source.tests@[i] {
                FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, numeric::term_view(term)),
                _ => false,
            };
        match source.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => {
                assert(code_field(a.constants, field, v as nat));
            },
            FlatTest::Atom { field, term: FlatTerm::Variable(v), .. } => { assert(field == v); },
            _ => {},
        }
    }
    assert forall|field: Component, v: nat|
        field.0 < a.universes@.len() && root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
        implies code_field(a.constants, field, v) by {
        let k = component_index(field) as int;
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
                assert(value_field::<E>(a.constants.values@[id as int - 1]) == field);
                assert(0 < id <= a.constants.values@.len());
                assert(code_field(a.constants, field, v));
            }
        } else {
            assert(register_codes(implementation::register_of(g, field)).contains(v));
            assert(code_field(a.constants, field, v));
        }
    }
}

}

verus! {
pub(crate) struct TailInput<E: Event> {
    pub left: Rule<E>,
    pub right: Rule<E>,
    pub left_flat: FlatRule<E::Component>,
    pub right_flat: FlatRule<E::Component>,
    pub left_numeric: FlatPair<u64>,
    pub right_numeric: FlatPair<u64>,
}

pub(crate) open spec fn tail_input_wf<E: Event>(c: Constants<E>, i: TailInput<E>) -> bool {
    &&& i.left.head@ == i.right.head@
    &&& i.left.head@.len() == arity::<E>()
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
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==> encoding::n_lang(theta, q, w)
        == (numeric::source_regex(i.left_numeric, i.left_numeric.root as nat, theta, w)
            && !numeric::source_regex(i.right_numeric, i.right_numeric.root as nat, theta, w))
}

pub(crate) open spec fn tail_ready<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>) -> bool {
    analyzer_state_wf(a) && analyzer_obligations::<E>() && tail_input_wf(a.constants, i) && difference_language(i, q)
}

/// The wave-1 verdict of `tail_included`: Holds is inclusion; a counterexample has the arity, a
/// real instance under capacity, and minimum length (`tail_included_spec` minus the instance
/// clauses, which `lemma_tail_decision_full` adds under `stored_known`).
pub(crate) open spec fn tail_verdict<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, r: Inclusion<E>) -> bool {
    match r@ {
        InclusionView::Holds => tails_included::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@),
        InclusionView::Counterexample(cex) => cex_arity(cex, arity::<E>())
            && (capacity_for::<E>(a@.domains, a@.known, cex) ==> cex_has_instance::<E>(a@.domains, a@.known, cex))
            && shortest::<E>(a@.domains, cex.history.len(), tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)),
        InclusionView::Exhausted => true,
    }
}

pub(crate) proof fn lemma_numeric_head_sat(h: encoding::NHead, theta: Subst)
    requires h.len() == theta.len(), h.len() <= history_syntax::MAX_ARITY,
    ensures inclusion::sat_by(theta, inclusion::head_constraint(h)) == encoding::n_head_matches(h, theta),
{
    inclusion::lemma_head_sat(h, theta);
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
        assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len())
            implies encoding::n_lang(theta, start.state, w)
                == (encoding::n_lang(theta, start.state, w) && !encoding::n_lang(theta, language::Regex::Empty, w)) by {
            lemma_empty_language(theta, w);
        }
    }
}

/// A failing real pair embeds into a numeric inclusion counterexample of the same length.
proof fn lemma_embed_failure<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    c: E, h: Seq<E>)
    -> (coding: typed::NatCoding<E>)
    requires tail_ready(a, i, q), in_domains::<E>(a@.domains, c, h),
        tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h),
    ensures inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
        q, language::Regex::Empty, typed::numeric_event::<E>(coding, event_view(c)), typed::numeric_history::<E>(coding, history_view(h))),
        typed::numeric_history::<E>(coding, history_view(h)).len() == h.len(),
{
    let coding = bridge::lemma_pair_in_domains(a, c, h);
    typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
        i.left_numeric, i.right_numeric, a.constants, coding, event_view(c), history_view(h));
    lemma_numeric_head_sat(typed::template_head(i.left_numeric), typed::numeric_event::<E>(coding, event_view(c)));
    lemma_empty_language(typed::numeric_event::<E>(coding, event_view(c)), typed::numeric_history::<E>(coding, history_view(h)));
    coding
}

pub(crate) proof fn lemma_holds<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>)
    requires tail_ready(a, i, q), inclusion::included_under(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty),
    ensures tails_included::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@),
{
    assert forall|c: E, h: Seq<E>| in_domains::<E>(a@.domains, c, h)
        implies !tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = lemma_embed_failure(a, i, q, c, h);
        }
    }
}

pub(crate) proof fn lemma_shortest<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>, n: nat)
    requires tail_ready(a, i, q), inclusion::no_cex_shorter(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty, n),
    ensures shortest::<E>(a@.domains, n, tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)),
{
    assert forall|c: E, h: Seq<E>| in_domains::<E>(a@.domains, c, h) && h.len() < n
        implies !tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = lemma_embed_failure(a, i, q, c, h);
        }
    }
}

pub(crate) proof fn lemma_no_candidates<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(), tail_input_wf(a.constants, i),
        !inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))),
    ensures tails_included::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@),
{
    assert forall|c: E, h: Seq<E>| in_domains::<E>(a@.domains, c, h)
        implies !tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) by {
        if tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)(c, h) {
            let coding = bridge::lemma_pair_in_domains(a, c, h);
            typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
                i.left_numeric, i.right_numeric, a.constants, coding, event_view(c), history_view(h));
            let theta = typed::numeric_event::<E>(coding, event_view(c));
            lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
            assert(inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))));
        }
    }
}

/// The wave-1 counterexample clause: arity, a real instance under capacity, minimum length.
pub(crate) proof fn lemma_counterexample_shape<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires tail_ready(a, i, q), slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        search::outcome_ok(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)), q,
            language::Regex::Empty, search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets))),
    ensures cex_arity(result@, arity::<E>()),
        capacity_for::<E>(a@.domains, a@.known, result@) ==> cex_has_instance::<E>(a@.domains, a@.known, result@),
        shortest::<E>(a@.domains, result@.history.len(), tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@)),
{
    bridge::lemma_reconstructed_has_instance(a, g, letters, alphabets, result);
    lemma_shortest(a, i, q, exec::chain_assignments(letters, alphabets).len());
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    assert(result@.history.len() == exec::chain_assignments(letters, alphabets).len());
}

/// A4's counterexample clause: real instances fail, an instance exists under capacity and refutes
/// the inclusion, and no failing pair in the domains is shorter (needs every interned constant
/// known, `stored_known`).
pub(crate) proof fn lemma_counterexample<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires tail_ready(a, i, q), stored_known(a), slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        search::outcome_ok(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)), q,
            language::Regex::Empty, search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets))),
    ensures tail_included_spec::<E>(a@, i.left.head@, i.left.tail@, i.right.tail@, InclusionView::Counterexample(result@)),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    let fails = tail_fails::<E>(i.left.head@, i.left.tail@, i.right.tail@);
    assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(a@.domains, a@.known, result@, f) && #[trigger] instantiates::<E>(result@, f, c, h)
        implies in_domains::<E>(a@.domains, c, h) && fails(c, h) by {
        let coding = bridge::lemma_instance_embedding(a, g, letters, alphabets, result, candidate, history, f, c, h);
        let theta = typed::numeric_event::<E>(coding, event_view(c));
        let w = typed::numeric_history::<E>(coding, history_view(h));
        assert(inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
            q, language::Regex::Empty, theta, w));
        lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
        typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
            i.left_numeric, i.right_numeric, a.constants, coding, event_view(c), history_view(h));
    }
    bridge::lemma_reconstructed_has_instance(a, g, letters, alphabets, result);
    if cex_has_instance::<E>(a@.domains, a@.known, result@) {
        let (f, c, h) = choose|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
            admissible::<E>(a@.domains, a@.known, result@, f) && #[trigger] instantiates::<E>(result@, f, c, h);
        assert(in_domains::<E>(a@.domains, c, h) && fails(c, h));
        assert(!tails_included::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@));
    }
    lemma_shortest(a, i, q, exec::chain_assignments(letters, alphabets).len());
    assert(result@.history.len() == exec::chain_assignments(letters, alphabets).len());
}
}

verus! {
/// The numeric languages compared by a search. They need not share a head or a mode.
pub(crate) struct NumericInput {
    pub left: language::Regex<model::Test>,
    pub right: language::Regex<model::Test>,
}


pub(crate) open spec fn numeric_difference(i: NumericInput, p: FlatPair<u64>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
        numeric::source_regex(p, p.root as nat, theta, w)
            == (encoding::n_lang(theta, i.left, w) && !encoding::n_lang(theta, i.right, w))
}

pub(crate) open spec fn numeric_decision_ok<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput,
    g: implementation::ConstraintView, result: NumericDecision<E>) -> bool {
    &&& search::outcome_ok(ndomains(a.universes), implementation::constraint_of(g),
        i.left, i.right, result.outcome@)
    &&& match result.inclusion {
        Inclusion::Holds => result.outcome@ == search::Outcome::Holds,
        Inclusion::Exhausted => result.outcome@ == search::Outcome::Exhausted,
        Inclusion::Counterexample(c) => exists|refutation: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            result.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                exec::chain_assignments(letters, alphabets))
            && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c),
    }
}

pub(crate) proof fn lemma_numeric_refutation<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput,
    start: implementation::ConstraintView, g: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, decision: NumericDecision<E>)
    requires search::outcome_ok(ndomains(a.universes), implementation::constraint_of(start),
            i.left, i.right, decision.outcome@),
        decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets)),
        decision.inclusion matches Inclusion::Counterexample(c)
            && slots::reconstructed(a.constants, a.universes, g, letters, alphabets, c),
    ensures numeric_decision_ok(a, i, start, decision),
{
    if let Inclusion::Counterexample(c) = decision.inclusion {
        assert(exists|g1: Constraint, ls: Seq<Letter>, atoms: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g1@), exec::chain_assignments(ls, atoms))
            && slots::reconstructed(a.constants, a.universes, g1, ls, atoms, c)) by {
            assert(slots::reconstructed(a.constants, a.universes, g, letters, alphabets, c));
        }
    }
}

pub(crate) proof fn lemma_outcome_difference(d: encoding::NDomains, start: search::Item,
    i: NumericInput, outcome: search::Outcome)
    requires search::initial_ok(start.state, i.left, i.right),
        exec::search_result(d, start, outcome),
    ensures search::outcome_ok(d, start.constraint, i.left, i.right, outcome),
{
    reveal(exec::search_result);
}

/// The wave-1 verdict: Holds is inclusion; a counterexample has the arity, a real instance under
/// capacity, and minimum length. `lemma_tail_decision_full` adds the instance clauses.
pub(crate) proof fn lemma_tail_decision<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>,
    n: NumericInput, g: implementation::ConstraintView, decision: NumericDecision<E>)
    requires tail_ready(a, i, n.left), n.right == language::Regex::Empty,
        implementation::constraint_of(g) == inclusion::head_constraint(typed::template_head(i.left_numeric)),
        numeric_decision_ok(a, n, g, decision),
    ensures tail_verdict(a, i, decision.inclusion),
{
    match decision.inclusion {
        Inclusion::Holds => lemma_holds(a, i, n.left),
        Inclusion::Exhausted => {},
        Inclusion::Counterexample(c) => {
            let (refutation, letters, alphabets) = choose|refutation: Constraint, letters: Seq<Letter>,
                alphabets: Seq<Set<model::Primitive>>|
                decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                    exec::chain_assignments(letters, alphabets))
                && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c);
            lemma_counterexample_shape(a, i, n.left, refutation, letters, alphabets, c);
        },
    }
}

/// R6 `tail_included_spec` (A4), under `stored_known`.
pub(crate) proof fn lemma_tail_decision_full<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>,
    n: NumericInput, g: implementation::ConstraintView, decision: NumericDecision<E>)
    requires tail_ready(a, i, n.left), stored_known(a), n.right == language::Regex::Empty,
        implementation::constraint_of(g) == inclusion::head_constraint(typed::template_head(i.left_numeric)),
        numeric_decision_ok(a, n, g, decision),
    ensures tail_included_spec::<E>(a@, i.left.head@, i.left.tail@, i.right.tail@, decision.inclusion@),
{
    match decision.inclusion {
        Inclusion::Holds => lemma_holds(a, i, n.left),
        Inclusion::Exhausted => {},
        Inclusion::Counterexample(c) => {
            let (refutation, letters, alphabets) = choose|refutation: Constraint, letters: Seq<Letter>,
                alphabets: Seq<Set<model::Primitive>>|
                decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                    exec::chain_assignments(letters, alphabets))
                && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c);
            lemma_counterexample(a, i, n.left, refutation, letters, alphabets, c);
        },
    }
}
}

verus! {
pub(crate) open spec fn decision_ready<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput, g: Constraint,
    difference: FlatPair<u64>) -> bool {
    &&& analyzer_state_wf(a) && analyzer_obligations::<E>()
    &&& source_codes_wf(a.constants, difference) && numeric_difference(i, difference)
    &&& constraint_wf(g) && constraint_codes_wf(a.constants, g@)
    &&& source_fields_bounded(difference)
    &&& difference.head@.len() == arity::<E>()
    &&& g@.len() == a.universes@.len() && difference.head@.len() == a.universes@.len()
    &&& table::dag(difference) && difference.root < difference.regexes@.len()
    &&& inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(g@))
}

pub(crate) proof fn lemma_universes_extended<E: Event>(before: Constants<E>, after: Constants<E>, u: Universes)
    requires analyzer_obligations::<E>(), constants_wf(before), constants_wf(after), universes_wf(before, u),
        enc::extends(constant_book(before), constant_book(after), fl::component_equality::<E>()),
    ensures universes_wf(after, u),
{
    assert forall|k: int| #![trigger u[k]] 0 <= k < u@.len() implies match u[k] {
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
    constants: Seq<Option<u32>>, g: Constraint)
    requires head_codes_wf(c, head), head_view(constants) == pins(head),
        g.0@.len() == constants.len(), constants.len() == head.len(),
        forall|i: int| 0 <= i < constants.len() ==> g.0[i]@ == match constants[i] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        },
    ensures constraint_codes_wf(c, g@),
{
    assert forall|field: Component, v: nat| field.0 < g.0@.len() && register_codes(implementation::register_of(g@, field)).contains(v)
        implies code_field(c, field, v) by {
        let k = component_index(field) as int;
        assert(0 <= k < constants.len());
        assert(head_view(constants)[k] == option_code(constants[k]));
        assert(pins(head)[k] == encoding_head_code(head[k]));
        assert(head_view(constants)[k] == pins(head)[k]);
        assert(option_code(constants[k]) == encoding_head_code(head[k]));
        match constants[k] {
            Some(code) => { assert(head[k] == FlatHead::Constant(code as u64)); },
            None => { assert(!register_codes(implementation::register_of(g@, field)).contains(v)); },
        }
    }
}

pub(crate) proof fn lemma_refutation_input<E: Event>(a: PolicyAnalyzer<E>, start: search::Item,
    outcome: crate::search::SearchOutcome, vocabulary: Seq<Set<nat>>)
    requires analyzer_state_wf(a), exec::search_result(ndomains(a.universes), start, exec::outcome_view(outcome)),
        exec::refutation_ready(outcome, a.universes, vocabulary),
        forall|field: Component, v: nat| field.0 < vocabulary.len() && vocabulary[component_index(field) as int].contains(v)
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
        assert(vocabulary.len() == a.universes@.len());
        assert(vocabulary.len() == arity::<E>());
        assert(r.constraint@.len() == vocabulary.len());
        assert forall|field: Component| field.0 < r.constraint.0@.len() implies slots::register_codes_ok(a.constants, field,
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
pub(crate) open spec fn excluded_id(id: crate::analyzer::RuleId, exclude: Option<crate::analyzer::RuleId>) -> bool {
    match exclude { Some(other) => id.0 == other.0, None => false }
}

pub(crate) open spec fn head_atoms_ok<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, atoms: Seq<crate::constraint::Atom>) -> bool {
    &&& atoms_wf(atoms, arity::<E>())
    &&& forall|j: int, k: int| 0 <= j < ids.len() && !excluded_id(ids[j], exclude) && 0 <= k < arity::<E>()
        ==> match #[trigger] a.rules@[ids[j].0 as int].constants@[k] {
            Some(v) => atoms.contains(crate::constraint::Atom { component: k as usize,
                operand: crate::constraint::Operand::Constant(v) })
                && atoms.contains(crate::constraint::Atom { component: k as usize,
                    operand: crate::constraint::Operand::Register }), None => true,
        }
    &&& forall|j: int| 0 <= j < atoms.len() ==> match #[trigger] atoms[j].operand {
        crate::constraint::Operand::Constant(v) => code_field(a.constants, Component(atoms[j].component as u8), v as nat),
        _ => true,
    }
}

pub(crate) open spec fn firing_prefix<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, n: int, g: Constraint, theta: Subst, word: Seq<EventView>) -> bool {
    exists|j: int| 0 <= j < n && !excluded_id(ids[j], exclude)
        && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
            inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int]).head))
        && #[trigger] encoding::n_lang(theta,
            inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int])), word)
}

/// Meaning of the union roots already accumulated by the borrowed-policy loop.
pub(crate) open spec fn covering_prefix<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, n: int, g: Constraint, p: FlatPair<u64>, roots: Seq<u32>) -> bool {
    forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
        ((exists|j: int| 0 <= j < roots.len() && #[trigger] numeric::source_regex(p, roots[j] as nat, theta, word))
        == #[trigger] firing_prefix(a, ids, exclude, n, g, theta, word))
}

pub(crate) proof fn lemma_covering_step<E: Event>(a: PolicyAnalyzer<E>,
    ids: Seq<crate::analyzer::RuleId>, exclude: Option<crate::analyzer::RuleId>, index: int, g: Constraint,
    before: FlatPair<u64>, roots: Seq<u32>, after: FlatPair<u64>, next: Seq<u32>, added: Option<u32>)
    requires 0 <= index < ids.len(), covering_prefix(a, ids, exclude, index, g, before, roots),
        forall|j: int, theta: Subst, w: Seq<EventView>| 0 <= j < roots.len()
            ==> numeric::source_regex(before, roots[j] as nat, theta, w)
                == numeric::source_regex(after, roots[j] as nat, theta, w),
        match added {
            Some(root) => !excluded_id(ids[index], exclude)
                && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                    inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]).head))
                && next == roots.push(root)
                && forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
                    numeric::source_regex(after, root as nat, theta, w)
                        == encoding::n_lang(theta, inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int])), w),
            None => next == roots && (excluded_id(ids[index], exclude)
                || !inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                    inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]).head))),
        },
    ensures covering_prefix(a, ids, exclude, index + 1, g, after, next),
{
    assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) implies
        ((exists|j: int| 0 <= j < next.len() && #[trigger] numeric::source_regex(after, next[j] as nat, theta, w))
            == #[trigger] firing_prefix(a, ids, exclude, index + 1, g, theta, w)) by {
        let r = super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]);
        let fires = !excluded_id(ids[index], exclude)
            && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@), inclusion::head_constraint(r.head));
        assert(firing_prefix(a, ids, exclude, index + 1, g, theta, w)
            == (firing_prefix(a, ids, exclude, index, g, theta, w)
                || (fires && encoding::n_lang(theta, inclusion::denial(r), w)))) by {
            if firing_prefix(a, ids, exclude, index + 1, g, theta, w) {
                let j = choose|j: int| 0 <= j < index + 1 && !excluded_id(ids[j], exclude)
                    && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                        inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int]).head))
                    && encoding::n_lang(theta, inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int])), w);
                if j < index { assert(firing_prefix(a, ids, exclude, index, g, theta, w)); }
            }
        }
        if exists|j: int| 0 <= j < next.len() && #[trigger] numeric::source_regex(after, next[j] as nat, theta, w) {
            let j = choose|j: int| 0 <= j < next.len() && numeric::source_regex(after, next[j] as nat, theta, w);
            if j < roots.len() {
                assert(numeric::source_regex(before, roots[j] as nat, theta, w));
                assert(firing_prefix(a, ids, exclude, index, g, theta, w));
            } else {
                assert(added is Some && j == roots.len());
            }
        }
        if firing_prefix(a, ids, exclude, index, g, theta, w) {
            let j = choose|j: int| 0 <= j < roots.len() && numeric::source_regex(before, roots[j] as nat, theta, w);
            assert(numeric::source_regex(after, next[j] as nat, theta, w));
        }
        if fires && encoding::n_lang(theta, inclusion::denial(r), w) {
            assert(added is Some);
            assert(numeric::source_regex(after, next[roots.len() as int] as nat, theta, w));
        }
    }
}
}
