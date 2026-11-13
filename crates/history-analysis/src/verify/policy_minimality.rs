//! PR #10 case-local minimality over real events and the returned R3 context.
//!
//! The initial case is `g0`; reconstruction may strengthen it to `g_ref`.
//! Numeric entailment, not equality of these constraints, carries the length bound.

use super::frontend::*;
use super::{
    self as views, policy_bridge as bridge, policy_case_profile as profile,
    policy_queries as queries, reconstruction as slots, search_exec as exec,
    typed_numeric as typed, verdict,
};
use crate::analyzer::{Counterexample, Inclusion, NumericDecision, PolicyAnalyzer, RuleId};
use crate::constraint::{Constraint, Letter};
use crate::spec::analyzer;
use history_semantics::verify::refinement::{
    encoding, implementation, inclusion, policy_removal, search,
};
use history_syntax::spec::events::event_view;
use history_syntax::{Component, Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::spec::{questions as q, semantics as s};
use junco_core::verify::numeric_regex::{EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas,
    crate::verify::frontend::domain_view::lemma_analyzer_view,
    crate::verify::frontend::domain_view::lemma_rule_id_view};

/// Realizability and soundness establish entailment of the original split case.
pub(crate) proof fn lemma_refutation_entails_start(d: encoding::NDomains,
    g0: inclusion::Constraint, g_ref: inclusion::Constraint,
    input: verdict::NumericInput, letters: Seq<search::Assignment>)
    requires search::outcome_ok(d, g0, input.left, input.right, search::Outcome::Refuted(g_ref, letters)),
    ensures inclusion::entails(d, g_ref, g0),
{
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta) && inclusion::sat_by(theta, g_ref)
        implies inclusion::sat_by(theta, g0) by {
        let w = choose|w: Seq<EventView>| #[trigger] search::follows(d, letters, theta, w);
        assert(inclusion::inclusion_cex(d, g0, input.left, input.right, theta, w));
    }
}

/// Every actual instance retains the exact returned-case/profile minimum.
pub(crate) proof fn lemma_policy_shortest_in_case<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g0: Constraint, g_ref: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        bridge::rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        bridge::policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        verdict::constraint_codes_wf(a.constants, g0@),
        verdict::constraint_codes_known(a.constants, g0@, result@.known),
        slots::reconstructed(a.constants, a.universes, g_ref, letters, alphabets, result),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g_ref@), implementation::constraint_of(g0@)),
        inclusion::n_no_uncovered_shorter(views::ndomains(a.universes), by_n, left_n, implementation::constraint_of(g0@), letters.len()),
    ensures forall|first: E, first_history: Seq<E>| #[trigger] q::instance(a@.domains, result@, first, first_history)
        ==> q::shortest_in_case(a@.domains, result@.known, first, result@.history.len(),
            |c: E, h: Seq<E>| s::rule_violated(left, c, h) && !s::policy_denies(by, c, h)),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g_ref, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history, result@.known)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g_ref@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    assert forall|first: E, first_history: Seq<E>| q::instance(a@.domains, result@, first, first_history)
        implies q::shortest_in_case(a@.domains, result@.known, first, result@.history.len(),
            |c: E, h: Seq<E>| s::rule_violated(left, c, h) && !s::policy_denies(by, c, h)) by {
        let first_coding = typed::lemma_slot_embedding(a, candidate, history, first, first_history, result@.known);
        assert(slots::candidate_field_ok(a.constants, a.universes, g_ref, 0, candidate[0]));
        slots::lemma_candidate_slots(a.constants, a.universes, g_ref, candidate, typed::numeric_fresh::<E>(a.constants));
        assert(encoding::n_theta_ok(views::ndomains(a.universes), typed::numeric_event::<E>(first_coding, event_view(first))));
        assert(inclusion::sat_by(typed::numeric_event::<E>(first_coding, event_view(first)), implementation::constraint_of(g0@)));
        assert forall|c: E, h: Seq<E>| q::in_domains(a@.domains, c, h)
            && h.len() < result@.history.len() && q::same_profile(result@.known, first, c)
            implies !(s::rule_violated(left, c, h) && !s::policy_denies(by, c, h)) by {
            let coding = typed::lemma_pair_embedding(a.constants, event_view(c), typed::projected_history(h));
            assert forall|j: int| 0 <= j < h.len()
                implies typed::covered_event::<E>(coding, event_view(h[j])) by {
                assert(typed::projected_history(h)[j] == event_view(h[j]));
                assert(typed::covered_event::<E>(coding, typed::projected_history(h)[j]));
            }
            typed::lemma_analyzer_domain_embedding(a, coding, c, h);
            profile::lemma_same_profile_case(a, g0, first, c, first_coding, coding, result@.known);
            bridge::lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
            bridge::lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
            assert(typed::numeric_history::<E>(coding, typed::projected_history(h)).len() == h.len());
            assert(result@.history.len() == letters.len());
        }
    }
}

/// One case's Holds answer is accumulated separately; every other result satisfies R6.
pub(crate) proof fn lemma_covered_decision_minimal<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>, input: verdict::NumericInput,
    g0: Constraint, decision: NumericDecision<E>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        rule.0 < a.rules@.len(), valid_ids(a, ids), verdict::constraint_codes_wf(a.constants, g0@),
        input.left == inclusion::denial(queries::stored_numeric(a.rules@[rule.0 as int])),
        input.right == inclusion::firing_denials(views::ndomains(a.universes), queries::numeric_policy(a, ids, exclude), implementation::constraint_of(g0@)),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g0@),
            inclusion::head_constraint(queries::stored_numeric(a.rules@[rule.0 as int]).head)),
        forall|pair: (Component, nat)| inclusion::head_pairs(queries::numeric_policy(a, ids, exclude)).contains(pair)
            ==> #[trigger] inclusion::decides(views::ndomains(a.universes), implementation::constraint_of(g0@), pair.0, pair.1),
        verdict::numeric_decision_ok(a, input, g0@, decision, q::knowable_constants::<E>(a@.domains, a@.rules)),
    ensures decision.inclusion is Holds ==> inclusion::included_under(views::ndomains(a.universes), implementation::constraint_of(g0@), input.left, input.right),
        !(decision.inclusion is Holds) ==> analyzer::covered_spec(a@, rule@, queries::selected_rule_ids(ids, exclude), decision.inclusion@),
{
    slots::lemma_inclusion_view(decision.inclusion);
    queries::lemma_covered_decision(a, rule, ids, exclude, input, g0@, decision);
    queries::lemma_stored_rule(a, rule);
    queries::lemma_stored_policy(a, ids, exclude);
    let left = a.rules@[rule.0 as int];
    let by = queries::numeric_policy(a, ids, exclude);
    let d = views::ndomains(a.universes);
    inclusion::lemma_policy_case_outcome(d, by, queries::stored_numeric(left), implementation::constraint_of(g0@), decision.outcome@);
    if let Inclusion::Counterexample(c) = decision.inclusion {
        let (g_ref, letters, alphabets) = choose|g_ref: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g_ref@), exec::chain_assignments(letters, alphabets))
                && slots::reconstructed(a.constants, a.universes, g_ref, letters, alphabets, c);
        lemma_refutation_entails_start(d, implementation::constraint_of(g0@), implementation::constraint_of(g_ref@),
            input, exec::chain_assignments(letters, alphabets));
        lemma_policy_shortest_in_case(a, left.original@, left.flat@, left.numeric, queries::stored_numeric(left),
            queries::originals(a, ids, exclude), queries::flats(a, ids, exclude), queries::templates(a, ids, exclude), by,
            g0, g_ref, letters, alphabets, c);
    }
}

/// Removal retains order and duplicates, and absent targets keep their coverage meaning.
pub(crate) proof fn lemma_redundancy_minimal_result<E: Event>(a: analyzer::AnalyzerView<E>,
    rule: nat, policy: Seq<nat>, v: analyzer::QueryResult<E::Component>)
    requires rule < a.rules.len(), analyzer::valid_ids(a, policy),
        analyzer::covered_spec(a, rule, q::without_rule(policy, rule), v),
    ensures analyzer::redundant_spec(a, rule, policy, v),
{
    match v {
        analyzer::QueryResult::Holds => policy_removal::lemma_redundant_decisions(a.domains, a.rules, rule, policy),
        analyzer::QueryResult::Counterexample(cex) => {
            if policy.contains(rule) {
                policy_removal::lemma_redundant_counterexample_refutes(a.domains, a.rules, rule, policy, cex);
            }
        },
        _ => {},
    }
}

/// The same denying right-hand rule supplies both correctness and shortestness.
pub(crate) proof fn lemma_refinement_minimal_result<E: Event>(a: analyzer::AnalyzerView<E>,
    p: Seq<nat>, other: Seq<nat>, j: int, v: analyzer::QueryResult<E::Component>)
    requires 0 <= j < other.len(), other[j] < a.rules.len(), !(v is Holds),
        analyzer::covered_spec(a, other[j], p, v),
    ensures analyzer::at_least_as_strict_spec(a, p, other, v),
{
    bridge::lemma_refinement_result(a, p, other, j, v);
}
}
