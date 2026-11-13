//! Per-case minimality of policy counterexamples (R6): a typed pair with the same constant
//! profile as a returned candidate satisfies the same case constraint, so the search's numeric
//! minimality within the case transfers to `analyzer::shortest_in_case`.

use super::frontend::*;
use super::reconstruction::code_field;
use super::typed_numeric as typed;
use super::verdict::{self as verdict, constraint_codes_wf};
use super::policy;
use history_semantics::verify::refinement::policy as refinement_policy;
use super::*;
use crate::analyzer::{Counterexample, Inclusion, PolicyAnalyzer};
use history_semantics::verify::refinement::analyzer;
use junco_core::ComponentValue;
use junco_core::verify::dsl as tdsl;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

/// Under a book-fixing coding, a covered value has the code `k` of a known constant iff it is
/// `eq_spec`-equal to that constant.
proof fn lemma_code_is_constant<E: Event>(c: crate::analyzer::Constants<E>, coding: typed::NatCoding<E>, field: Component,
    v: ComponentValue<E>, k: nat)
    requires analyzer_obligations::<E>(), constants_wf(c), typed::fixes_book(c, coding),
        typed::has_code(coding[junco_core::flat::verify::field_index(field)], typed::native_eq::<E>(), v),
        code_field(c, field, k),
    ensures (typed::code_value(coding, field, v) == k) == v.eq_spec(&c.values@[k as int - 1]),
{
    let f = junco_core::flat::verify::field_index(field);
    let eq = typed::native_eq::<E>();
    let w = c.values@[k as int - 1];
    typed::lemma_native_equivalence::<E>();
    super::reconstruction::lemma_code_payload(c, field, k);
    let book = constant_book(c)[f];
    let i = choose|i: int| 0 <= i < book.len() && book[i] == (w, k as u64);
    assert(coding[f] == coding[f]);
    assert(typed::known_seed(c, f)[i] == (w, k));
    assert(coding[f][i] == (w, k));
    let j = choose|j: int| #![trigger coding[f][j]] 0 <= j < coding[f].len() && eq(coding[f][j].0, v);
    assert(eq(w, w));
    typed::lemma_lookup_code(coding[f], eq, w, i);
    typed::lemma_coding_reflects_eq(coding[f], eq, v, w, j, i);
}

/// Registers whose codes do not separate two values are satisfied by both or neither.
proof fn lemma_register_transfer(r: implementation::RegisterView, x1: nat, x2: nat)
    requires forall|k: nat| #[trigger] register_codes(r).contains(k) ==> ((x1 == k) == (x2 == k)),
        register_sat(r, x1),
    ensures register_sat(r, x2),
{
    match r {
        implementation::RegisterView::Equals(v) => { assert(register_codes(r).contains(v)); },
        implementation::RegisterView::Differs(vs) => {
            if vs.contains(x2) { assert(register_codes(r).contains(x2)); }
        },
    }
}

/// Same constant profile, same case: under book-fixing codings, a candidate with the profile of
/// one satisfying the case constraint `g` satisfies it too.
pub(crate) proof fn lemma_profile_case<E: Event>(a: PolicyAnalyzer<E>,
    coding1: typed::NatCoding<E>, c1: tdsl::EventView<E::Principal, E::Action, E::Resource>,
    coding2: typed::NatCoding<E>, c2: tdsl::EventView<E::Principal, E::Action, E::Resource>,
    g: Constraint)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(),
        typed::fixes_book(a.constants, coding1), typed::covered_event(coding1, c1),
        typed::fixes_book(a.constants, coding2), typed::covered_event(coding2, c2),
        constraint_codes_wf(a.constants, g@),
        analyzer::same_profile(a@, c1, c2),
        inclusion::sat_by(typed::numeric_event(coding1, c1), implementation::constraint_of(g@)),
    ensures inclusion::sat_by(typed::numeric_event(coding2, c2), implementation::constraint_of(g@)),
{
    let cs = a.constants;
    let values = cs.values@;
    let t1 = typed::numeric_event(coding1, c1);
    let t2 = typed::numeric_event(coding2, c2);
    lemma_constraint_sat(g@, t1);
    lemma_constraint_sat(g@, t2);
    assert(coding1[0] == coding1[0] && coding1[1] == coding1[1] && coding1[2] == coding1[2]);
    assert(coding2[0] == coding2[0] && coding2[1] == coding2[1] && coding2[2] == coding2[2]);
    // principal
    assert forall|k: nat| #[trigger] register_codes(g@.principal).contains(k)
        implies (t1.principal == k) == (t2.principal == k) by {
        assert(register_codes(implementation::register_of(g@, Component::Principal)).contains(k));
        let v1 = ComponentValue::<E>::Principal(c1.principal);
        let v2 = ComponentValue::<E>::Principal(c2.principal);
        lemma_code_is_constant(cs, coding1, Component::Principal, v1, k);
        lemma_code_is_constant(cs, coding2, Component::Principal, v2, k);
        let w = values[k as int - 1];
        if let ComponentValue::Principal(x) = w {
            assert(values.to_set().contains(w));
            assert(values.to_set().filter(|v: ComponentValue<E>| v is Principal).contains(w));
            assert(a@.known_principals.contains(principal_of::<E>(w)));
        }
    }
    // action
    assert forall|k: nat| #[trigger] register_codes(g@.action).contains(k)
        implies (t1.action == k) == (t2.action == k) by {
        assert(register_codes(implementation::register_of(g@, Component::Action)).contains(k));
        let v1 = ComponentValue::<E>::Action(c1.action);
        let v2 = ComponentValue::<E>::Action(c2.action);
        lemma_code_is_constant(cs, coding1, Component::Action, v1, k);
        lemma_code_is_constant(cs, coding2, Component::Action, v2, k);
        let w = values[k as int - 1];
        if let ComponentValue::Action(x) = w {
            assert(values.to_set().contains(w));
            assert(values.to_set().filter(|v: ComponentValue<E>| v is Action).contains(w));
            assert(a@.known_actions.contains(action_of::<E>(w)));
        }
    }
    // resource
    assert forall|k: nat| #[trigger] register_codes(g@.resource).contains(k)
        implies (t1.resource == k) == (t2.resource == k) by {
        assert(register_codes(implementation::register_of(g@, Component::Resource)).contains(k));
        let v1 = ComponentValue::<E>::Resource(c1.resource);
        let v2 = ComponentValue::<E>::Resource(c2.resource);
        lemma_code_is_constant(cs, coding1, Component::Resource, v1, k);
        lemma_code_is_constant(cs, coding2, Component::Resource, v2, k);
        let w = values[k as int - 1];
        if let ComponentValue::Resource(x) = w {
            assert(values.to_set().contains(w));
            assert(values.to_set().filter(|v: ComponentValue<E>| v is Resource).contains(w));
            assert(a@.known_resources.contains(resource_of::<E>(w)));
        }
    }
    lemma_register_transfer(g@.principal, t1.principal, t2.principal);
    lemma_register_transfer(g@.action, t1.action, t2.action);
    lemma_register_transfer(g@.resource, t1.resource, t2.resource);
}

/// `redundant(rule, policy)` minimality is `covered(rule, others(policy, rule))` minimality.
pub(crate) proof fn lemma_redundant_minimal<P: PartialEq, A: PartialEq, R: PartialEq>(
    a: analyzer::AnalyzerView<P, A, R>, rule: nat, policy: Seq<nat>, v: analyzer::InclusionView<P, A, R>)
    requires analyzer::covered_minimal(a, rule, analyzer::others(policy, rule), v),
    ensures analyzer::redundant_minimal(a, rule, policy, v),
{}

/// `at_least_as_strict(p, q)` minimality from per-case minimality of `covered(q[j], p)` for a
/// rule `q[j]` that every instance shows uncovered.
pub(crate) proof fn lemma_strict_minimal<P: PartialEq, A: PartialEq, R: PartialEq>(
    a: analyzer::AnalyzerView<P, A, R>, p: Seq<nat>, q: Seq<nat>, j: int, cex: analyzer::CexView<P, A, R>)
    requires 0 <= j < q.len(),
        analyzer::covered_minimal(a, q[j], p, analyzer::InclusionView::Counterexample(cex)),
        analyzer::every_instance(a, cex,
            analyzer::uncovered(analyzer::rules_of(a, p), analyzer::rules_of(a, q)[j])),
    ensures analyzer::at_least_as_strict_minimal(a, p, q, analyzer::InclusionView::Counterexample(cex)),
{
    let qq = analyzer::rules_of(a, q);
    assert(qq[j] == a.rules[q[j] as int]);
    assert(qq.len() == q.len());
}

/// Pointwise agreement of typed and numeric denials for the stored rule `rule` and the policy
/// `ids`, under every coding that fixes the constant book and covers the pair.
pub(crate) open spec fn denials_agree<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>) -> bool {
    forall|coding: typed::NatCoding<E>, c: tdsl::EventView<E::Principal, E::Action, E::Resource>,
        h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
        #![trigger typed::numeric_event(coding, c), typed::numeric_history(coding, h)]
        typed::fixes_book(a.constants, coding) && typed::covered_event(coding, c)
        && (forall|i: int| 0 <= i < h.len() ==> #[trigger] typed::covered_event(coding, h[i]))
        ==> {
            &&& semantics::rule_denies(a@.rules[rule as int], c, h)
                == encoding::n_rule_denies(policy::stored_numeric(a.rules@[rule as int]),
                    typed::numeric_event(coding, c), typed::numeric_history(coding, h))
            &&& semantics::policy_denies(analyzer::rules_of(a@, ids), c, h)
                == encoding::n_policy_denies(policy::numeric_policy(a, ids),
                    typed::numeric_event(coding, c), typed::numeric_history(coding, h))
        }
}

/// `covered(rule, ids)` minimality for a counterexample decided in one case of the policy split:
/// a shorter uncovered pair with the candidate's profile lies in the same case (`lemma_profile_case`)
/// and would be a shorter inclusion counterexample there (`case_cex_uncovered`, `no_cex_shorter`).
pub(crate) proof fn lemma_covered_minimal<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>,
    base: Constraint, cases: Set<inclusion::Constraint>, case: Constraint, cex: Counterexample<E>)
    requires analyzer_state_wf(a), analyzer_obligations::<E>(),
        rule < a.rules@.len(), policy::ids_valid(a, ids), denials_agree(a, rule, ids),
        inclusion::split_ok(ndomains(a.universes), implementation::constraint_of(base@),
            inclusion::head_pairs(policy::numeric_policy(a, ids)), cases),
        cases.contains(implementation::constraint_of(case@)),
        implementation::constraint_of(base@)
            == inclusion::head_constraint(policy::stored_numeric(a.rules@[rule as int]).head),
        constraint_codes_wf(a.constants, case@),
        policy::decided(a, case@, inclusion::denial(policy::stored_numeric(a.rules@[rule as int])),
            inclusion::firing_denials(ndomains(a.universes), policy::numeric_policy(a, ids),
                implementation::constraint_of(case@)),
            Inclusion::Counterexample(cex)),
    ensures analyzer::covered_minimal(a@, rule, ids, analyzer::InclusionView::Counterexample(cex@)),
{
    let d = ndomains(a.universes);
    let nr = policy::stored_numeric(a.rules@[rule as int]);
    let np = policy::numeric_policy(a, ids);
    let g1 = implementation::constraint_of(case@);
    let left = inclusion::denial(nr);
    let right = inclusion::firing_denials(d, np, g1);
    let n = cex@.history.len();
    let p = analyzer::rules_of(a@, ids);
    let r = a@.rules[rule as int];
    refinement_policy::lemma_policy_outcomes(d, np, nr, cases);
    assert(refinement_policy::case_cex_uncovered(d, np, nr, g1));
    verdict::lemma_decided_shortest(a, case@, left, right, cex);
    assert forall|f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>| #[trigger] analyzer::admissible(a@, cex@, f)
        implies analyzer::shortest_in_case(a@, analyzer::event_of(cex@.candidate, f), n, analyzer::uncovered(p, r)) by {
        let c1 = analyzer::event_of(cex@.candidate, f);
        let coding1 = verdict::lemma_decided_instance(a, case@, left, right, cex, f);
        let h1 = analyzer::history_of(cex@, f);
        assert(inclusion::inclusion_cex(d, g1, left, right, typed::numeric_event(coding1, c1),
            typed::numeric_history(coding1, h1)));
        assert forall|c2: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
            semantics::event_in(a@.domains, c2) && semantics::history_in(a@.domains, h) && h.len() < n
            && analyzer::same_profile(a@, c1, c2) implies !#[trigger] analyzer::uncovered(p, r)(c2, h) by {
            if analyzer::uncovered(p, r)(c2, h) {
                let coding2 = typed::lemma_pair_embedding(a.constants, c2, h);
                let t2 = typed::numeric_event(coding2, c2);
                let w2 = typed::numeric_history(coding2, h);
                lemma_profile_case(a, coding1, c1, coding2, c2, case);
                typed::lemma_analyzer_domain_embedding(a, coding2, c2, h);
                assert(encoding::n_rule_denies(nr, t2, w2) && !encoding::n_policy_denies(np, t2, w2));
                assert(inclusion::inclusion_cex(d, g1, left, right, t2, w2));
                assert(w2.len() < n);
            }
        }
    }
}

} // verus!
