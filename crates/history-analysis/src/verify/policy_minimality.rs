//! Case-local minimality clients for stored policy queries.
//!
//! The search starts at `g0`, whereas reconstruction uses the stronger `g_ref`.
//! Its actual `outcome_ok` contract supplies the semantic entailment between them;
//! profile transport is applied to `g0`, never to an assumed identical constraint.
//! These ghost helpers add no executable work. Entry points must call them and
//! expose `*_ok` before policy-query minimality is an end-to-end guarantee.

use super::frontend::*;
use super::{
    self as views, policy_bridge as bridge, policy_case_profile as profile,
    policy_queries as queries, reconstruction as slots, search_exec as exec,
    typed_numeric as typed, verdict,
};
use crate::analyzer::{Counterexample, Inclusion, NumericDecision, PolicyAnalyzer, RuleId};
use crate::constraint::{Constraint, Letter};
use history_semantics::verify::refinement::{
    analyzer, encoding, implementation, inclusion, search, semantics,
};
use history_syntax::{Component, Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

/// Entailment follows from realizability and counterexample soundness, not from
/// an equality between the search's initial and reconstructed constraints.
pub(crate) proof fn lemma_refutation_entails_start(d: encoding::NDomains,
    g0: inclusion::Constraint, g_ref: inclusion::Constraint,
    input: verdict::NumericInput, letters: Seq<search::Assignment>)
    requires search::outcome_ok(d, g0, input.left, input.right,
        search::Outcome::Refuted(g_ref, letters)),
    ensures inclusion::entails(d, g_ref, g0),
{
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, g_ref)
        implies inclusion::sat_by(theta, g0) by {
        let w = choose|w: Seq<EventView>| #[trigger] search::follows(d, letters, theta, w);
        assert(inclusion::inclusion_cex(d, g0, input.left, input.right, theta, w));
    }
}

/// Transfer the initial case's numeric length bound to every admissible typed
/// instance, keeping all same-profile candidates and declared finite domains.
pub(crate) proof fn lemma_policy_shortest_in_case<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g0: Constraint, g_ref: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        bridge::rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        bridge::policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        verdict::constraint_codes_wf(a.constants, g0@),
        slots::reconstructed(a.constants, a.universes, g_ref, letters, alphabets, result),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g_ref@),
            implementation::constraint_of(g0@)),
        inclusion::n_no_uncovered_shorter(views::ndomains(a.universes), by_n, left_n,
            implementation::constraint_of(g0@), letters.len()),
    ensures forall|f: analyzer::FreshChoice<E::Component>| #[trigger] analyzer::admissible(a@, result@, f)
        ==> analyzer::shortest_in_case(a@, analyzer::event_of(result@.candidate, f), result@.history.len(),
            analyzer::uncovered(bridge::rule_views(by), encoding::rule_view(left))),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g_ref, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g_ref@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    assert forall|f: analyzer::FreshChoice<E::Component>| analyzer::admissible(a@, result@, f)
        implies analyzer::shortest_in_case(a@, analyzer::event_of(result@.candidate, f), result@.history.len(),
            analyzer::uncovered(bridge::rule_views(by), encoding::rule_view(left))) by {
        let first = analyzer::event_of(result@.candidate, f);
        let first_coding = typed::lemma_slot_embedding(a, candidate, history, f);
        assert(slots::candidate_field_ok(a.constants, a.universes, g_ref, 0, candidate[0]));
        slots::lemma_candidate_slots(a.constants, a.universes, g_ref, candidate, typed::numeric_fresh::<E>(a.constants));
        assert(encoding::n_theta_ok(views::ndomains(a.universes), typed::numeric_event::<E>(first_coding, first)));
        assert(inclusion::sat_by(typed::numeric_event::<E>(first_coding, first), implementation::constraint_of(g0@)));
        assert forall|c: Seq<E::Component>, h: Seq<Seq<E::Component>>|
            semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
                && h.len() < result@.history.len() && analyzer::same_profile(a@, first, c)
            implies !analyzer::uncovered(bridge::rule_views(by), encoding::rule_view(left))(c, h) by {
            assert forall|i: int| 0 <= i < h.len() implies h[i].len() == c.len() by {
                assert(semantics::event_in(a@.domains, h[i]));
            }
            let coding = typed::lemma_pair_embedding(a.constants, c, h);
            typed::lemma_analyzer_domain_embedding(a, coding, c, h);
            profile::lemma_same_profile_case(a, g0, first, c, first_coding, coding);
            bridge::lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
            bridge::lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
            assert(typed::numeric_history::<E>(coding, h).len() == h.len());
            assert(result@.history.len() == letters.len());
        }
    }
}

/// Drop-in strengthening of `policy_queries::lemma_covered_decision`: the loop
/// supplies its actual split constraint, whose codes are known by `decision_ready`.
/// A Holds case is not coverage of the entire split; minimality is vacuous there.
pub(crate) proof fn lemma_covered_decision_minimal<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>, input: verdict::NumericInput,
    g0: Constraint, decision: NumericDecision<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule.0 < a.rules@.len(), valid_ids(a, ids),
        verdict::constraint_codes_wf(a.constants, g0@),
        input.left == inclusion::denial(queries::stored_numeric(a.rules@[rule.0 as int])),
        input.right == inclusion::firing_denials(views::ndomains(a.universes), queries::numeric_policy(a, ids, exclude),
            implementation::constraint_of(g0@)),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g0@),
            inclusion::head_constraint(queries::stored_numeric(a.rules@[rule.0 as int]).head)),
        forall|pair: (Component, nat)| inclusion::head_pairs(queries::numeric_policy(a, ids, exclude)).contains(pair)
            ==> #[trigger] inclusion::decides(views::ndomains(a.universes), implementation::constraint_of(g0@), pair.0, pair.1),
        verdict::numeric_decision_ok(a, input, g0@, decision),
    ensures analyzer::covered_minimal(a@, rule@, queries::selected_rule_ids(ids, exclude), decision.inclusion@),
        decision.inclusion is Holds ==> inclusion::included_under(views::ndomains(a.universes),
            implementation::constraint_of(g0@), input.left, input.right),
        !(decision.inclusion is Holds) ==> analyzer::covered_ok(a@, rule@,
            queries::selected_rule_ids(ids, exclude), decision.inclusion@),
        decision.inclusion matches Inclusion::Counterexample(c) ==> (
            analyzer::unrestricted_components_infinite(a@.domains) ==> (
                analyzer::cex_has_instance(a@, c@)
                && !semantics::covers(a@.domains, analyzer::rules_of(a@, queries::selected_rule_ids(ids, exclude)), a@.rules[rule@ as int]))),
{
    queries::lemma_covered_decision(a, rule, ids, exclude, input, g0@, decision);
    queries::lemma_stored_rule(a, rule);
    queries::lemma_stored_policy(a, ids, exclude);
    let left = a.rules@[rule.0 as int];
    let by = queries::numeric_policy(a, ids, exclude);
    let d = views::ndomains(a.universes);
    inclusion::lemma_policy_case_outcome(d, by, queries::stored_numeric(left), implementation::constraint_of(g0@), decision.outcome@);
    if let Inclusion::Counterexample(c) = decision.inclusion {
        let (g_ref, letters, alphabets) = choose|g_ref: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g_ref@),
                exec::chain_assignments(letters, alphabets))
            && slots::reconstructed(a.constants, a.universes, g_ref, letters, alphabets, c);
        lemma_refutation_entails_start(d, implementation::constraint_of(g0@), implementation::constraint_of(g_ref@),
            input, exec::chain_assignments(letters, alphabets));
        lemma_policy_shortest_in_case(a, left.original@, left.flat@, left.numeric, queries::stored_numeric(left),
            queries::originals(a, ids, exclude), queries::flats(a, ids, exclude), queries::templates(a, ids, exclude), by,
            g0, g_ref, letters, alphabets, c);
    }
}

/// Redundancy uses precisely the same selected policy as its correctness proof.
pub(crate) proof fn lemma_redundancy_minimal_result<C: PartialEq>(a: analyzer::AnalyzerView<C>,
    rule: nat, policy: Seq<nat>, v: analyzer::InclusionView<C>)
    requires analyzer::covered_minimal(a, rule, analyzer::without_rule(policy, rule), v),
    ensures analyzer::redundant_minimal(a, rule, policy, v),
        analyzer::covered_correct(a, rule, analyzer::without_rule(policy, rule), v)
            ==> analyzer::redundant_ok(a, rule, policy, v),
{}

/// Both correctness and shortestness use `q[j]`; independently existential
/// witnesses from refinement correctness and minimality cannot be combined.
pub(crate) proof fn lemma_refinement_minimal_result<C: PartialEq>(a: analyzer::AnalyzerView<C>,
    p: Seq<nat>, q: Seq<nat>, j: int, v: analyzer::InclusionView<C>)
    requires 0 <= j < q.len(), !(v is Holds), analyzer::covered_ok(a, q[j], p, v),
    ensures analyzer::at_least_as_strict_minimal(a, p, q, v),
        analyzer::at_least_as_strict_ok(a, p, q, v),
{
    bridge::lemma_refinement_result(a, p, q, j, v);
    if let analyzer::InclusionView::Counterexample(cex) = v {
        assert(analyzer::rules_of(a, q)[j] == a.rules[q[j] as int]);
        assert(exists|k: int| 0 <= k < analyzer::rules_of(a, q).len()
            && analyzer::every_instance(a, cex, #[trigger] analyzer::uncovered(analyzer::rules_of(a, p), analyzer::rules_of(a, q)[k]))
            && forall|f: analyzer::FreshChoice<C>| #[trigger] analyzer::admissible(a, cex, f)
                ==> analyzer::shortest_in_case(a, analyzer::event_of(cex.candidate, f), cex.history.len(),
                    analyzer::uncovered(analyzer::rules_of(a, p), analyzer::rules_of(a, q)[k]))) by {
            assert(analyzer::every_instance(a, cex, analyzer::uncovered(analyzer::rules_of(a, p), analyzer::rules_of(a, q)[j])));
        }
    }
}
} // verus!
