//! Case-local minimality clients for stored policy queries (A6, R3 `minimal_in_case`).
//!
//! The search starts at `g0`, whereas reconstruction uses the stronger `g_ref`.
//! Its actual `outcome_ok` contract supplies the semantic entailment between them;
//! profile transport is applied to `g0`, never to an assumed identical constraint.
//! These ghost helpers add no executable work; they need every interned constant known
//! (`stored_known`), which Track F establishes from `known`'s contracts.

use super::frontend::*;
use super::{
    self as views, policy_bridge as bridge, policy_case_profile as profile,
    policy_queries as queries, reconstruction as slots, search_exec as exec,
    typed_numeric as typed, verdict,
};
use crate::analyzer::{Counterexample, Inclusion, NumericDecision, PolicyAnalyzer, RuleId};
use crate::constraint::{Constraint, Letter};
use crate::spec::analyzer::{covered_spec, rules_of, uncovered};
use history_semantics::verify::refinement::{encoding, implementation, inclusion, search};
use history_syntax::spec::events::event_view;
use history_syntax::{Component, Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::spec::questions::{
    FreshChoice, admissible, in_domains, instantiates, minimal_in_case, same_profile,
    shortest_in_case,
};
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

/// Transfer the initial case's numeric length bound to every real instance, keeping all
/// same-profile candidates and declared finite domains (R3 `minimal_in_case`).
pub(crate) proof fn lemma_policy_shortest_in_case<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g0: Constraint, g_ref: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), stored_known(a),
        bridge::rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        bridge::policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        verdict::constraint_codes_wf(a.constants, g0@),
        slots::reconstructed(a.constants, a.universes, g_ref, letters, alphabets, result),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g_ref@),
            implementation::constraint_of(g0@)),
        inclusion::n_no_uncovered_shorter(views::ndomains(a.universes), by_n, left_n,
            implementation::constraint_of(g0@), letters.len()),
    ensures minimal_in_case::<E>(a@.domains, a@.known, result@,
        uncovered::<E>(bridge::rule_views(by), encoding::rule_view(left))),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g_ref, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g_ref@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    let fails = uncovered::<E>(bridge::rule_views(by), encoding::rule_view(left));
    assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(a@.domains, a@.known, result@, f) && #[trigger] instantiates::<E>(result@, f, c, h)
        implies shortest_in_case::<E>(a@.domains, a@.known, c, result@.history.len(), fails) by {
        let first = event_view(c);
        let first_coding = bridge::lemma_instance_embedding(a, g_ref, letters, alphabets, result, candidate, history, f, c, h);
        assert(slots::candidate_field_ok(a.constants, a.universes, g_ref, 0, candidate[0]));
        slots::lemma_candidate_slots(a.constants, a.universes, g_ref, candidate, typed::numeric_fresh::<E>(a.constants));
        assert(inclusion::sat_by(typed::numeric_event::<E>(first_coding, first), implementation::constraint_of(g0@)));
        assert forall|c2: E, h2: Seq<E>|
            in_domains::<E>(a@.domains, c2, h2) && h2.len() < result@.history.len()
                && same_profile(a@.known, first, event_view(c2))
            implies !#[trigger] fails(c2, h2) by {
            let coding = bridge::lemma_pair_in_domains(a, c2, h2);
            profile::lemma_same_profile_case(a, g0, first, event_view(c2), first_coding, coding);
            bridge::lemma_rule_violated(a.constants, left, left_flat, left_template, left_n, coding, c2, h2);
            bridge::lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c2, h2);
            assert(result@.history.len() == letters.len());
        }
    }
}

/// Drop-in strengthening of `policy_queries::lemma_covered_decision_full`: the loop supplies its
/// actual split constraint, whose codes are known by `decision_ready`. A Holds case is not
/// coverage of the entire split; a refuted case is R6 `covered_spec` (A1, A2, A6).
pub(crate) proof fn lemma_covered_decision_minimal<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>, input: verdict::NumericInput,
    g0: Constraint, decision: NumericDecision<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), stored_known(a),
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
    ensures
        decision.inclusion is Holds ==> inclusion::included_under(views::ndomains(a.universes),
            implementation::constraint_of(g0@), input.left, input.right),
        !(decision.inclusion is Holds) ==> covered_spec::<E>(a@, rule@,
            queries::selected_rule_ids(ids, exclude), decision.inclusion@),
{
    queries::lemma_covered_decision(a, rule, ids, exclude, input, g0@, decision);
    queries::lemma_covered_decision_full(a, rule, ids, exclude, input, g0@, decision);
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
        assert(rules_of(a@, queries::selected_rule_ids(ids, exclude)) == bridge::rule_views(queries::originals(a, ids, exclude)));
    }
}
} // verus!
