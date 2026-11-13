//! Stored-rule projections and policy-query clients of numeric search composition.

use super::{
    self as views, frontend::*, policy_bridge as bridge, policy_source as source,
    reconstruction as slots, search_exec as exec, table, verdict,
};
use crate::analyzer::{Inclusion, NumericDecision, PolicyAnalyzer, RuleId, StoredRule};
use crate::constraint::{Constraint, Letter};
use crate::spec::analyzer::{counterexample_spec, rules_of, uncovered};
use history_semantics::verify::refinement::{encoding, implementation, inclusion, search};
use history_syntax::spec::events::arity;
use history_syntax::{Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::spec::questions::{capacity_for, cex_arity, cex_has_instance, covers};
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

pub(crate) open spec fn selected_ids(ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<RuleId> {
    match exclude {
        Some(excluded) => ids.filter(|id: RuleId| id.0 != excluded.0),
        None => ids,
    }
}

pub(crate) open spec fn selected_rule_ids(ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<nat> {
    rule_ids(selected_ids(ids, exclude))
}

pub(crate) open spec fn records<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<StoredRule<E>> {
    selected_ids(ids, exclude).map_values(|id: RuleId| a.rules@[id.0 as int])
}

pub(crate) open spec fn stored_numeric<E: Event>(r: StoredRule<E>) -> encoding::NRule {
    source::numeric_rule(r.numeric, r.mode)
}

pub(crate) open spec fn originals<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<Rule<E>> {
    records(a, ids, exclude).map_values(|r: StoredRule<E>| r.original@)
}

pub(crate) open spec fn flats<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<FlatRule<E::Component>> {
    records(a, ids, exclude).map_values(|r: StoredRule<E>| r.flat@)
}

pub(crate) open spec fn templates<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<FlatPair<u64>> {
    records(a, ids, exclude).map_values(|r: StoredRule<E>| r.numeric)
}

pub(crate) open spec fn numeric_policy<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>) -> Seq<encoding::NRule> {
    records(a, ids, exclude).map_values(|r: StoredRule<E>| stored_numeric(r))
}

/// The executable loop's original-id existential is the firing union of the selected policy.
pub(crate) proof fn lemma_firing_prefix<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>,
    exclude: Option<RuleId>, g: Constraint, theta: Subst, w: Seq<EventView>)
    requires valid_ids(a, ids),
    ensures verdict::firing_prefix(a, ids, exclude, ids.len() as int, g, theta, w)
        == encoding::n_lang(theta, inclusion::firing_denials(views::ndomains(a.universes),
            numeric_policy(a, ids, exclude), implementation::constraint_of(g@)), w),
{
    let d = views::ndomains(a.universes);
    let by = numeric_policy(a, ids, exclude);
    let selected = selected_ids(ids, exclude);
    let case = implementation::constraint_of(g@);
    inclusion::lemma_firing_lang(d, by, case, theta, w);
    if verdict::firing_prefix(a, ids, exclude, ids.len() as int, g, theta, w) {
        let j = choose|j: int| 0 <= j < ids.len() && !verdict::excluded_id(ids[j], exclude)
            && inclusion::entails(d, case, inclusion::head_constraint(stored_numeric(a.rules@[ids[j].0 as int]).head))
            && #[trigger] encoding::n_lang(theta, inclusion::denial(stored_numeric(a.rules@[ids[j].0 as int])), w);
        let id = ids[j];
        if let Some(excluded) = exclude {
            ids.lemma_filter_contains(|id: RuleId| id.0 != excluded.0, j);
        }
        assert(selected.contains(id));
        let k = choose|k: int| 0 <= k < selected.len() && selected[k] == id;
        assert(by[k] == stored_numeric(a.rules@[id.0 as int]));
        assert(inclusion::entails(d, case, inclusion::head_constraint(by[k].head)));
        assert(encoding::n_lang(theta, inclusion::denial(by[k]), w));
    }
    if encoding::n_lang(theta, inclusion::firing_denials(d, by, case), w) {
        let k = choose|k: int| 0 <= k < by.len()
            && inclusion::entails(d, case, inclusion::head_constraint(by[k].head))
            && #[trigger] encoding::n_lang(theta, inclusion::denial(by[k]), w);
        let id = selected[k];
        if let Some(excluded) = exclude {
            ids.lemma_filter_contains_rev(|id: RuleId| id.0 != excluded.0, id);
            ids.lemma_filter_pred(|id: RuleId| id.0 != excluded.0, k);
        }
        assert(ids.contains(id));
        let j = choose|j: int| 0 <= j < ids.len() && ids[j] == id;
        assert(!verdict::excluded_id(ids[j], exclude));
        assert(by[k] == stored_numeric(a.rules@[ids[j].0 as int]));
        assert(inclusion::entails(d, case, inclusion::head_constraint(stored_numeric(a.rules@[ids[j].0 as int]).head)));
        assert(encoding::n_lang(theta, inclusion::denial(stored_numeric(a.rules@[ids[j].0 as int])), w));
    }
}

pub(crate) proof fn lemma_selected_ids<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>)
    requires valid_ids(a, ids),
    ensures valid_ids(a, selected_ids(ids, exclude)),
        selected_rule_ids(ids, exclude) == match exclude {
            Some(excluded) => rule_ids(ids).filter(|id: nat| id != excluded@),
            None => rule_ids(ids),
        },
{
    if let Some(excluded) = exclude {
        vstd::seq_lib::lemma_filter_view_commute(ids, |id: RuleId| id.0 != excluded.0,
            |id: nat| id != excluded@);
        assert(ids.map_values(|id: RuleId| id@) =~= rule_ids(ids));
        assert(selected_ids(ids, exclude).map_values(|id: RuleId| id@)
            =~= selected_rule_ids(ids, exclude));
        assert forall|i: int| 0 <= i < selected_ids(ids, exclude).len()
            implies selected_ids(ids, exclude)[i].0 < a.rules@.len() by {
            let id = selected_ids(ids, exclude)[i];
            ids.lemma_filter_contains_rev(|id: RuleId| id.0 != excluded.0, id);
            let j = choose|j: int| 0 <= j < ids.len() && ids[j] == id;
        }
    }
}

pub(crate) proof fn lemma_stored_rule<E: Event>(a: PolicyAnalyzer<E>, id: RuleId)
    requires analyzer_state_wf(a), id.0 < a.rules@.len(),
    ensures bridge::rule_bridge_wf(a.constants, a.rules@[id.0 as int].original@,
        a.rules@[id.0 as int].flat@, a.rules@[id.0 as int].numeric,
        stored_numeric(a.rules@[id.0 as int])),
        stored_numeric(a.rules@[id.0 as int]).head.len() == views::ndomains(a.universes).len(),
{
    let r = a.rules@[id.0 as int];
    assert(stored_rule_wf(a.constants, a.universes, r));
    table::lemma_structural_dag(r.numeric);
    source::lemma_numeric_rule(r.numeric, r.mode);
}

pub(crate) proof fn lemma_stored_policy<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>, exclude: Option<RuleId>)
    requires analyzer_state_wf(a), valid_ids(a, ids),
    ensures bridge::policy_bridge_wf(a.constants, originals(a, ids, exclude), flats(a, ids, exclude),
            templates(a, ids, exclude), numeric_policy(a, ids, exclude)),
        bridge::rule_views(originals(a, ids, exclude))
            == rules_of(a@, selected_rule_ids(ids, exclude)),
        forall|i: int| 0 <= i < numeric_policy(a, ids, exclude).len()
            ==> #[trigger] numeric_policy(a, ids, exclude)[i].head.len() == views::ndomains(a.universes).len(),
{
    lemma_selected_ids(a, ids, exclude);
    assert forall|i: int| 0 <= i < originals(a, ids, exclude).len()
        implies bridge::rule_bridge_wf(a.constants, originals(a, ids, exclude)[i], flats(a, ids, exclude)[i],
            templates(a, ids, exclude)[i], numeric_policy(a, ids, exclude)[i]) by {
        lemma_stored_rule(a, selected_ids(ids, exclude)[i]);
    }
    assert forall|i: int| 0 <= i < numeric_policy(a, ids, exclude).len()
        implies numeric_policy(a, ids, exclude)[i].head.len() == views::ndomains(a.universes).len() by {
        lemma_stored_rule(a, selected_ids(ids, exclude)[i]);
    }
    assert(bridge::rule_views(originals(a, ids, exclude)) =~= rules_of(a@, selected_rule_ids(ids, exclude)));
}

pub(crate) proof fn lemma_covered_holds<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule.0 < a.rules@.len(), valid_ids(a, ids),
        inclusion::n_covers(views::ndomains(a.universes), numeric_policy(a, ids, exclude),
            stored_numeric(a.rules@[rule.0 as int])),
    ensures covers::<E>(a@.domains, rules_of(a@, selected_rule_ids(ids, exclude)), a@.rules[rule@ as int]),
{
    lemma_stored_rule(a, rule);
    lemma_stored_policy(a, ids, exclude);
    let left = a.rules@[rule.0 as int];
    bridge::lemma_policy_covers(a, left.original@, left.flat@, left.numeric, stored_numeric(left),
        originals(a, ids, exclude), flats(a, ids, exclude), templates(a, ids, exclude), numeric_policy(a, ids, exclude));
}

/// One case's Holds answer establishes inclusion only; the caller accumulates these facts over
/// the split. A refuted case has the arity and a real instance under capacity (wave 1);
/// `lemma_covered_decision_full` adds A1/A2 under `stored_known`, and minimality (A6) is
/// `policy_minimality::lemma_covered_decision_minimal`'s.
pub(crate) proof fn lemma_covered_decision<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>, input: verdict::NumericInput,
    g: implementation::ConstraintView, decision: NumericDecision<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule.0 < a.rules@.len(), valid_ids(a, ids),
        input.left == inclusion::denial(stored_numeric(a.rules@[rule.0 as int])),
        input.right == inclusion::firing_denials(views::ndomains(a.universes), numeric_policy(a, ids, exclude),
            implementation::constraint_of(g)),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g),
            inclusion::head_constraint(stored_numeric(a.rules@[rule.0 as int]).head)),
        forall|pair: (history_syntax::Component, nat)| inclusion::head_pairs(numeric_policy(a, ids, exclude)).contains(pair)
            ==> #[trigger] inclusion::decides(views::ndomains(a.universes), implementation::constraint_of(g), pair.0, pair.1),
        verdict::numeric_decision_ok(a, input, g, decision),
    ensures
        decision.inclusion is Holds ==> inclusion::included_under(views::ndomains(a.universes),
            implementation::constraint_of(g), input.left, input.right),
        decision.inclusion matches Inclusion::Counterexample(c) ==> cex_arity(c@, arity::<E>())
            && (capacity_for::<E>(a@.domains, a@.known, c@) ==> cex_has_instance::<E>(a@.domains, a@.known, c@)),
{
    lemma_stored_rule(a, rule);
    lemma_stored_policy(a, ids, exclude);
    let left = a.rules@[rule.0 as int];
    let by = numeric_policy(a, ids, exclude);
    let d = views::ndomains(a.universes);
    inclusion::lemma_policy_case_outcome(d, by, stored_numeric(left), implementation::constraint_of(g), decision.outcome@);
    if let Inclusion::Counterexample(c) = decision.inclusion {
        let (refutation, letters, alphabets) = choose|refutation: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                exec::chain_assignments(letters, alphabets))
            && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c);
        bridge::lemma_reconstructed_has_instance(a, refutation, letters, alphabets, c);
    }
}

/// A1/A2 for a refuted case: every real instance is uncovered, and an instance refutes coverage
/// (needs every interned constant known, `stored_known`).
pub(crate) proof fn lemma_covered_decision_full<E: Event>(a: PolicyAnalyzer<E>, rule: RuleId,
    ids: Seq<RuleId>, exclude: Option<RuleId>, input: verdict::NumericInput,
    g: implementation::ConstraintView, decision: NumericDecision<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), stored_known(a),
        rule.0 < a.rules@.len(), valid_ids(a, ids),
        input.left == inclusion::denial(stored_numeric(a.rules@[rule.0 as int])),
        input.right == inclusion::firing_denials(views::ndomains(a.universes), numeric_policy(a, ids, exclude),
            implementation::constraint_of(g)),
        inclusion::entails(views::ndomains(a.universes), implementation::constraint_of(g),
            inclusion::head_constraint(stored_numeric(a.rules@[rule.0 as int]).head)),
        forall|pair: (history_syntax::Component, nat)| inclusion::head_pairs(numeric_policy(a, ids, exclude)).contains(pair)
            ==> #[trigger] inclusion::decides(views::ndomains(a.universes), implementation::constraint_of(g), pair.0, pair.1),
        verdict::numeric_decision_ok(a, input, g, decision),
    ensures
        decision.inclusion matches Inclusion::Counterexample(c) ==> (
            counterexample_spec::<E>(a@, c@, uncovered::<E>(rules_of(a@, selected_rule_ids(ids, exclude)), a@.rules[rule@ as int]))
            && (cex_has_instance::<E>(a@.domains, a@.known, c@)
                ==> !covers::<E>(a@.domains, rules_of(a@, selected_rule_ids(ids, exclude)), a@.rules[rule@ as int]))),
{
    lemma_stored_rule(a, rule);
    lemma_stored_policy(a, ids, exclude);
    let left = a.rules@[rule.0 as int];
    let by = numeric_policy(a, ids, exclude);
    let d = views::ndomains(a.universes);
    inclusion::lemma_policy_case_outcome(d, by, stored_numeric(left), implementation::constraint_of(g), decision.outcome@);
    if let Inclusion::Counterexample(c) = decision.inclusion {
        let (refutation, letters, alphabets) = choose|refutation: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                exec::chain_assignments(letters, alphabets))
            && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c);
        bridge::lemma_policy_counterexample(a, left.original@, left.flat@, left.numeric, stored_numeric(left),
            originals(a, ids, exclude), flats(a, ids, exclude), templates(a, ids, exclude), by,
            refutation, letters, alphabets, c);
    }
}
}
