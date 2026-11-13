//! Typed and numeric policies (R4): a stored rule denies a typed pair exactly when its numeric
//! rule denies the pair's numeric image, pointwise over policies, and the typed answers of
//! `covered`, `redundant` and `at_least_as_strict` follow from the numeric ones.

use super::frontend::*;
use super::policy::{self, ids_valid, numeric_policy, stored_numeric};
use super::typed_numeric as typed;
use super::{analyzer_obligations, constraint_views, firing, lemma_constraint_view_at, ndomains, table, verdict};
use crate::analyzer::{Counterexample, Inclusion, PolicyAnalyzer};
use crate::constraint::Constraint;
use history_semantics::verify::refinement::policy as outcomes;
use history_semantics::verify::refinement::{analyzer, encoding, implementation, inclusion, semantics};
use history_syntax::Event;
use junco_core::ComponentValue;
use junco_core::verify::dsl as tdsl;
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

// ----- typed denial is numeric denial -----

/// A stored rule denies a typed pair iff its numeric rule denies the pair's image under a coding
/// that fixes the constant book (B1).
pub(crate) proof fn lemma_stored_denies<E: Event>(a: PolicyAnalyzer<E>, i: nat, coding: typed::NatCoding<E>,
    c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), i < a.rules@.len(),
        typed::fixes_book(a.constants, coding), typed::covered_event(coding, c),
        forall|j: int| 0 <= j < h.len() ==> #[trigger] typed::covered_event(coding, h[j]),
    ensures
        semantics::rule_denies(a@.rules[i as int], c, h) == encoding::n_rule_denies(stored_numeric(a.rules@[i as int]),
            typed::numeric_event(coding, c), typed::numeric_history(coding, h)),
{
    let r = a.rules@[i as int];
    assert(stored_rule_wf(a.constants, r));
    assert(a@.rules[i as int] == r.source@.0@);
    typed::lemma_source_language(r.source@.0, r.source@.1, r.tail, a.constants, coding, c, h);
    table::lemma_structural_dag(r.tail);
    firing::lemma_template_regex(r.tail, r.tail.root as nat, typed::numeric_event(coding, c), typed::numeric_history(coding, h));
}

/// The policy of stored rules `ids` denies a typed pair iff its numeric policy denies the pair's
/// image (B2).
pub(crate) proof fn lemma_policy_denies<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>, coding: typed::NatCoding<E>,
    c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), ids_valid(a, ids),
        typed::fixes_book(a.constants, coding), typed::covered_event(coding, c),
        forall|j: int| 0 <= j < h.len() ==> #[trigger] typed::covered_event(coding, h[j]),
    ensures
        semantics::policy_denies(analyzer::rules_of(a@, ids), c, h) == encoding::n_policy_denies(numeric_policy(a, ids),
            typed::numeric_event(coding, c), typed::numeric_history(coding, h)),
{
    let p = analyzer::rules_of(a@, ids);
    let q = numeric_policy(a, ids);
    let theta = typed::numeric_event(coding, c);
    let w = typed::numeric_history(coding, h);
    assert forall|k: int| 0 <= k < ids.len() implies
        semantics::rule_denies(#[trigger] p[k], c, h) == encoding::n_rule_denies(q[k], theta, w) by {
        assert(ids[k] < a.rules@.len());
        lemma_stored_denies(a, ids[k], coding, c, h);
    }
    if semantics::policy_denies(p, c, h) {
        let k = choose|k: int| 0 <= k < p.len() && #[trigger] semantics::rule_denies(p[k], c, h);
        assert(encoding::n_rule_denies(q[k], theta, w));
    }
    if encoding::n_policy_denies(q, theta, w) {
        let k = choose|k: int| 0 <= k < q.len() && #[trigger] encoding::n_rule_denies(q[k], theta, w);
        assert(semantics::rule_denies(p[k], c, h));
    }
}

/// Numeric coverage within the domains gives typed coverage (B3).
pub(crate) proof fn lemma_covers_from_numeric<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), rule < a.rules@.len(), ids_valid(a, ids),
        inclusion::n_covers(ndomains(a.universes), numeric_policy(a, ids), stored_numeric(a.rules@[rule as int])),
    ensures semantics::covers(a@.domains, analyzer::rules_of(a@, ids), a@.rules[rule as int]),
{
    assert forall|c: tdsl::EventView<E::Principal, E::Action, E::Resource>, h: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>|
        semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
            && #[trigger] semantics::rule_denies(a@.rules[rule as int], c, h)
        implies semantics::policy_denies(analyzer::rules_of(a@, ids), c, h) by {
        let coding = typed::lemma_pair_embedding(a.constants, c, h);
        typed::lemma_analyzer_domain_embedding(a, coding, c, h);
        lemma_stored_denies(a, rule, coding, c, h);
        lemma_policy_denies(a, ids, coding, c, h);
    }
}

// ----- covered -----

/// A rule whose head constraint no valuation in the domains satisfies denies nothing, so every
/// policy covers it (B4).
pub(crate) proof fn lemma_covered_unsat<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), rule < a.rules@.len(), ids_valid(a, ids),
        !inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(stored_numeric(a.rules@[rule as int]).head)),
    ensures analyzer::covered_correct(a@, rule, ids, analyzer::InclusionView::Holds),
{
    let d = ndomains(a.universes);
    let r = stored_numeric(a.rules@[rule as int]);
    assert forall|theta: Subst, w: Seq<EventView>| encoding::n_theta_ok(d, theta) && encoding::n_history_in(d, w)
        && #[trigger] encoding::n_rule_denies(r, theta, w) implies encoding::n_policy_denies(numeric_policy(a, ids), theta, w) by {
        inclusion::lemma_head_sat(r.head, theta);
        assert(inclusion::sat_by(theta, inclusion::head_constraint(r.head)));
    }
    lemma_covers_from_numeric(a, rule, ids);
}

// ----- covered, from the per-case verdicts -----

/// Every case of `case_set(cases)` is the constraint of some listed case.
proof fn lemma_case_member(cases: Seq<Constraint>, g1: inclusion::Constraint)
    requires firing::case_set(cases).contains(g1),
    ensures exists|i: int| 0 <= i < cases.len() && #[trigger] implementation::constraint_of(cases[i]@) == g1,
{
    let v = choose|v: implementation::ConstraintView| constraint_views(cases).contains(v)
        && implementation::constraint_of(v) == g1;
    let g = choose|g: Constraint| cases.to_set().contains(g) && g@ == v;
    assert(cases.contains(g));
    let i = choose|i: int| 0 <= i < cases.len() && cases[i] == g;
    assert(implementation::constraint_of(cases[i]@) == g1);
}

proof fn lemma_case_at(cases: Seq<Constraint>, i: int)
    requires 0 <= i < cases.len(),
    ensures firing::case_set(cases).contains(implementation::constraint_of(cases[i]@)),
{
    lemma_constraint_view_at(cases, i);
}

/// `covered(rule, ids)` answers `Holds` when the inclusion holds in every case of the policy
/// split (B6').
pub(crate) proof fn lemma_covered_holds<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>,
    base: Constraint, cases: Seq<Constraint>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), rule < a.rules@.len(), ids_valid(a, ids),
        implementation::constraint_of(base@) == inclusion::head_constraint(stored_numeric(a.rules@[rule as int]).head),
        inclusion::split_ok(ndomains(a.universes), implementation::constraint_of(base@),
            inclusion::head_pairs(numeric_policy(a, ids)), firing::case_set(cases)),
        forall|i: int| 0 <= i < cases.len() ==> inclusion::included_under(ndomains(a.universes),
            implementation::constraint_of(#[trigger] cases[i]@), inclusion::denial(stored_numeric(a.rules@[rule as int])),
            inclusion::firing_denials(ndomains(a.universes), numeric_policy(a, ids), implementation::constraint_of(cases[i]@))),
    ensures analyzer::covered_correct(a@, rule, ids, analyzer::InclusionView::Holds),
{
    let d = ndomains(a.universes);
    let r = stored_numeric(a.rules@[rule as int]);
    let p = numeric_policy(a, ids);
    inclusion::lemma_policy_reduction(d, p, r, firing::case_set(cases));
    assert forall|g1: inclusion::Constraint| #[trigger] firing::case_set(cases).contains(g1)
        implies inclusion::included_under(d, g1, inclusion::denial(r), inclusion::firing_denials(d, p, g1)) by {
        lemma_case_member(cases, g1);
        let i = choose|i: int| 0 <= i < cases.len() && #[trigger] implementation::constraint_of(cases[i]@) == g1;
        assert(inclusion::included_under(d, implementation::constraint_of(cases[i]@), inclusion::denial(r),
            inclusion::firing_denials(d, p, implementation::constraint_of(cases[i]@))));
    }
    lemma_covers_from_numeric(a, rule, ids);
}

/// A counterexample decided for one case of the policy split answers `covered(rule, ids)`: every
/// admissible instance is denied by the rule and by no rule of the policy, and with infinite
/// unrestricted components some instance exists, so the policy does not cover the rule (B6/B7).
pub(crate) proof fn lemma_covered_cex<E: Event>(a: PolicyAnalyzer<E>, rule: nat, ids: Seq<nat>,
    base: Constraint, cases: Seq<Constraint>, i: int, cex: Counterexample<E>)
    requires
        analyzer_state_wf(a), analyzer_obligations::<E>(), rule < a.rules@.len(), ids_valid(a, ids),
        implementation::constraint_of(base@) == inclusion::head_constraint(stored_numeric(a.rules@[rule as int]).head),
        inclusion::split_ok(ndomains(a.universes), implementation::constraint_of(base@),
            inclusion::head_pairs(numeric_policy(a, ids)), firing::case_set(cases)),
        0 <= i < cases.len(),
        policy::decided(a, cases[i]@, inclusion::denial(stored_numeric(a.rules@[rule as int])),
            inclusion::firing_denials(ndomains(a.universes), numeric_policy(a, ids), implementation::constraint_of(cases[i]@)),
            Inclusion::Counterexample(cex)),
    ensures analyzer::covered_correct(a@, rule, ids, analyzer::InclusionView::Counterexample(cex@)),
{
    let d = ndomains(a.universes);
    let r = stored_numeric(a.rules@[rule as int]);
    let p = numeric_policy(a, ids);
    let g1 = implementation::constraint_of(cases[i]@);
    let left = inclusion::denial(r);
    let right = inclusion::firing_denials(d, p, g1);
    let pp = analyzer::rules_of(a@, ids);
    let rr = a@.rules[rule as int];
    lemma_case_at(cases, i);
    outcomes::lemma_policy_outcomes(d, p, r, firing::case_set(cases));
    assert(outcomes::case_cex_uncovered(d, p, r, g1));
    assert forall|f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>| #[trigger] analyzer::admissible(a@, cex@, f)
        implies semantics::event_in(a@.domains, analyzer::event_of(cex@.candidate, f))
            && semantics::history_in(a@.domains, analyzer::history_of(cex@, f))
            && analyzer::uncovered(pp, rr)(analyzer::event_of(cex@.candidate, f), analyzer::history_of(cex@, f)) by {
        let coding = verdict::lemma_decided_instance(a, cases[i]@, left, right, cex, f);
        let c = analyzer::event_of(cex@.candidate, f);
        let h = analyzer::history_of(cex@, f);
        assert(inclusion::inclusion_cex(d, g1, left, right, typed::numeric_event(coding, c), typed::numeric_history(coding, h)));
        lemma_stored_denies(a, rule, coding, c, h);
        lemma_policy_denies(a, ids, coding, c, h);
    }
    assert(analyzer::cex_values_ok(a@, cex@));
    assert(analyzer::every_instance(a@, cex@, analyzer::uncovered(pp, rr)));
    if analyzer::unrestricted_infinite(a@.domains) {
        verdict::lemma_decided_fresh(a, cases[i]@, left, right, cex);
        lemma_component_equivalence(|x: E::Principal| ComponentValue::<E>::Principal(x));
        lemma_component_equivalence(|x: E::Action| ComponentValue::<E>::Action(x));
        lemma_component_equivalence(|x: E::Resource| ComponentValue::<E>::Resource(x));
        let f = analyzer::lemma_choice_exists_declared(a@, cex@);
        let c = analyzer::event_of(cex@.candidate, f);
        let h = analyzer::history_of(cex@, f);
        assert(analyzer::uncovered(pp, rr)(c, h));
        assert(semantics::rule_denies(rr, c, h));
        assert(!semantics::covers(a@.domains, pp, rr));
    }
}

// ----- component equality -----

/// `eq_spec` on a component type is an equivalence (`eq_equivalence`) when it is on the tagged
/// component values.
proof fn lemma_component_equivalence<E: Event, T: PartialEq>(tag: spec_fn(T) -> ComponentValue<E>)
    requires
        analyzer_obligations::<E>(),
        forall|x: T, y: T| #[trigger] tag(x).eq_spec(&tag(y)) == x.eq_spec(&y),
    ensures
        forall|x: T| #[trigger] x.eq_spec(&x),
        forall|x: T, y: T| #[trigger] x.eq_spec(&y) == y.eq_spec(&x),
        forall|x: T, y: T, z: T| #[trigger] x.eq_spec(&y) && #[trigger] y.eq_spec(&z) ==> x.eq_spec(&z),
{
    assert forall|x: T| #[trigger] x.eq_spec(&x) by { assert(tag(x).eq_spec(&tag(x))); }
    assert forall|x: T, y: T| #[trigger] x.eq_spec(&y) == y.eq_spec(&x) by {
        assert(tag(x).eq_spec(&tag(y)) == tag(y).eq_spec(&tag(x)));
    }
    assert forall|x: T, y: T, z: T| #[trigger] x.eq_spec(&y) && #[trigger] y.eq_spec(&z) implies x.eq_spec(&z) by {
        assert(tag(x).eq_spec(&tag(y)) && tag(y).eq_spec(&tag(z)));
        assert(tag(x).eq_spec(&tag(z)));
    }
}

// ----- at_least_as_strict and redundant, over views -----

/// `P` covering every rule of `Q` is `P ⊑ Q` (B8).
pub(crate) proof fn lemma_strict_holds<P: PartialEq, A: PartialEq, R: PartialEq>(
    a: analyzer::AnalyzerView<P, A, R>, p: Seq<nat>, q: Seq<nat>)
    requires forall|j: int| #![trigger q[j]] 0 <= j < q.len()
        ==> semantics::covers(a.domains, analyzer::rules_of(a, p), a.rules[q[j] as int]),
    ensures analyzer::at_least_as_strict_correct(a, p, q, analyzer::InclusionView::Holds),
{
    let pp = analyzer::rules_of(a, p);
    let qq = analyzer::rules_of(a, q);
    semantics::theorem_refines_iff_covers::<P, A, R>();
    assert forall|j: int| 0 <= j < qq.len() implies semantics::covers(a.domains, pp, #[trigger] qq[j]) by {
        assert(qq[j] == a.rules[q[j] as int]);
    }
    assert(semantics::refines(a.domains, pp, qq));
}

/// A counterexample to `covered(q[j], p)` is a counterexample to `p ⊑ q` (B8).
pub(crate) proof fn lemma_strict_cex<P: PartialEq, A: PartialEq, R: PartialEq>(
    a: analyzer::AnalyzerView<P, A, R>, p: Seq<nat>, q: Seq<nat>, j: int, cex: analyzer::CexView<P, A, R>)
    requires 0 <= j < q.len(), analyzer::covered_correct(a, q[j], p, analyzer::InclusionView::Counterexample(cex)),
    ensures analyzer::at_least_as_strict_correct(a, p, q, analyzer::InclusionView::Counterexample(cex)),
{
    let pp = analyzer::rules_of(a, p);
    let qq = analyzer::rules_of(a, q);
    assert(qq[j] == a.rules[q[j] as int]);
    assert(analyzer::every_instance(a, cex, analyzer::uncovered(pp, qq[j])));
    if analyzer::unrestricted_infinite(a.domains) {
        semantics::theorem_refines_iff_covers::<P, A, R>();
        assert(!semantics::covers(a.domains, pp, qq[j]));
        assert(!semantics::refines(a.domains, pp, qq));
    }
}

/// `others(policy, rule)` keeps exactly the ids of `policy` other than `rule`.
proof fn lemma_others(policy: Seq<nat>, rule: nat)
    ensures
        forall|k: int| 0 <= k < policy.len() && policy[k] != rule
            ==> #[trigger] analyzer::others(policy, rule).contains(policy[k]),
        forall|m: int| 0 <= m < analyzer::others(policy, rule).len()
            ==> policy.contains(#[trigger] analyzer::others(policy, rule)[m]),
    decreases policy.len(),
{
    reveal_with_fuel(Seq::filter, 1);
    if policy.len() > 0 {
        let prior = policy.drop_last();
        lemma_others(prior, rule);
        let o = analyzer::others(policy, rule);
        let po = analyzer::others(prior, rule);
        assert(o == if policy.last() != rule { po.push(policy.last()) } else { po });
        assert forall|k: int| 0 <= k < policy.len() && policy[k] != rule implies #[trigger] o.contains(policy[k]) by {
            if k < prior.len() {
                assert(prior[k] == policy[k]);
                assert(po.contains(prior[k]));
                let m = choose|m: int| 0 <= m < po.len() && po[m] == prior[k];
                assert(o[m] == po[m]);
            } else {
                assert(o[po.len() as int] == policy[k]);
            }
        }
        assert forall|m: int| 0 <= m < o.len() implies policy.contains(#[trigger] o[m]) by {
            if m < po.len() {
                assert(o[m] == po[m]);
                assert(prior.contains(po[m]));
                let j = choose|j: int| 0 <= j < prior.len() && prior[j] == po[m];
                assert(policy[j] == prior[j]);
            } else {
                assert(o[m] == policy[policy.len() - 1]);
            }
        }
    }
}

/// Removing every occurrence of `rule` from `policy` changes no decision in the domains iff the
/// remaining rules cover it, read off the verdict of `covered(rule, others)` (B8).
pub(crate) proof fn lemma_redundant_correct<P: PartialEq, A: PartialEq, R: PartialEq>(
    a: analyzer::AnalyzerView<P, A, R>, rule: nat, policy: Seq<nat>, v: analyzer::InclusionView<P, A, R>)
    requires analyzer::covered_correct(a, rule, analyzer::others(policy, rule), v),
    ensures analyzer::redundant_correct(a, rule, policy, v),
{
    let others = analyzer::others(policy, rule);
    let all = analyzer::rules_of(a, policy);
    let rest = analyzer::rules_of(a, others);
    let r = a.rules[rule as int];
    lemma_others(policy, rule);
    match v {
        analyzer::InclusionView::Holds => {
            assert forall|c: tdsl::EventView<P, A, R>, h: Seq<tdsl::EventView<P, A, R>>|
                semantics::event_in(a.domains, c) && semantics::history_in(a.domains, h)
                implies #[trigger] semantics::policy_denies(all, c, h) == semantics::policy_denies(rest, c, h) by {
                if semantics::policy_denies(all, c, h) {
                    let k = choose|k: int| 0 <= k < all.len() && #[trigger] semantics::rule_denies(all[k], c, h);
                    if policy[k] == rule {
                        assert(semantics::rule_denies(r, c, h));
                    } else {
                        assert(others.contains(policy[k]));
                        let m = choose|m: int| 0 <= m < others.len() && others[m] == policy[k];
                        assert(semantics::rule_denies(rest[m], c, h));
                    }
                }
                if semantics::policy_denies(rest, c, h) {
                    let m = choose|m: int| 0 <= m < rest.len() && #[trigger] semantics::rule_denies(rest[m], c, h);
                    assert(policy.contains(others[m]));
                    let k = choose|k: int| 0 <= k < policy.len() && policy[k] == others[m];
                    assert(semantics::rule_denies(all[k], c, h));
                }
            }
        },
        analyzer::InclusionView::Counterexample(_) => {
            if policy.contains(rule) && analyzer::unrestricted_infinite(a.domains) {
                assert(!semantics::covers(a.domains, rest, r));
                let (c, h) = choose|c: tdsl::EventView<P, A, R>, h: Seq<tdsl::EventView<P, A, R>>|
                    semantics::event_in(a.domains, c) && semantics::history_in(a.domains, h)
                    && #[trigger] semantics::rule_denies(r, c, h) && !semantics::policy_denies(rest, c, h);
                let k = choose|k: int| 0 <= k < policy.len() && policy[k] == rule;
                assert(semantics::rule_denies(all[k], c, h));
                assert(semantics::policy_denies(all, c, h) != semantics::policy_denies(rest, c, h));
            }
        },
        analyzer::InclusionView::Exhausted => {},
    }
}

} // verus!
