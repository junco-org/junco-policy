//! Policy-level clients of the existing typed/numeric pair and slot embeddings.
//!
//! Each rule retains its own head and mode. The same finite equality-class coding is shared
//! by all rules in a query; declared domains are transported by `typed_numeric` unchanged.

use super::frontend::*;
use super::{self as views, reconstruction as slots, search_exec as exec, typed_numeric as typed};
use crate::analyzer::{Constants, Counterexample, PolicyAnalyzer};
use crate::constraint::{Constraint, Letter};
use history_semantics::verify::refinement::{
    analyzer, encoding, implementation, inclusion, search, semantics,
};
use history_syntax::spec::events::{RuleView, arity};
use history_syntax::{Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::verify::flatten as fl;
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

pub(crate) open spec fn rule_bridge_wf<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, template: FlatPair<u64>, n: encoding::NRule) -> bool {
    encoding::front_end_ok(rule, flat, template, views::constant_book(c), fl::component_domain::<E>())
        && encoding::represents(n, rule.mode, template) && rule.head@.len() == arity::<E>()
}

pub(crate) open spec fn policy_bridge_wf<E: Event>(c: Constants<E>, rules: Seq<Rule<E>>,
    flats: Seq<FlatRule<E::Component>>, templates: Seq<FlatPair<u64>>,
    numeric: Seq<encoding::NRule>) -> bool {
    &&& rules.len() == flats.len() && rules.len() == templates.len() && rules.len() == numeric.len()
    &&& forall|i: int| 0 <= i < rules.len()
        ==> rule_bridge_wf(c, #[trigger] rules[i], flats[i], templates[i], numeric[i])
}

pub(crate) open spec fn rule_views<E: Event>(rules: Seq<Rule<E>>)
    -> Seq<RuleView<E::Component>> {
    rules.map(|i: int, r: Rule<E>| encoding::rule_view(r))
}

/// Unlike the tail-only helper, this equation preserves the rule's actual mode.
pub(crate) proof fn lemma_rule_denies<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, template: FlatPair<u64>, n: encoding::NRule,
    coding: typed::NatCoding<E>, candidate: Seq<E::Component>,
    history: Seq<Seq<E::Component>>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), rule_bridge_wf(c, rule, flat, template, n),
        typed::fixes_book::<E>(c, coding), typed::covered_event::<E>(coding, candidate),
        junco_core::verify::history_specs::event_wf(typed::numeric_event::<E>(coding, candidate), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> typed::covered_event::<E>(coding, history[i]),
    ensures semantics::rule_denies(encoding::rule_view(rule), candidate, history)
        == encoding::n_rule_denies(n, typed::numeric_event::<E>(coding, candidate), typed::numeric_history::<E>(coding, history)),
{
    typed::lemma_source_language(rule, flat, template, c, coding, candidate, history);
    assert(n.head == typed::template_head(template));
}

/// Pointwise rule transport needs neither a shared head nor a shared mode.
pub(crate) proof fn lemma_policy_denies<E: Event>(c: Constants<E>, rules: Seq<Rule<E>>,
    flats: Seq<FlatRule<E::Component>>, templates: Seq<FlatPair<u64>>, numeric: Seq<encoding::NRule>,
    coding: typed::NatCoding<E>, candidate: Seq<E::Component>,
    history: Seq<Seq<E::Component>>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), policy_bridge_wf(c, rules, flats, templates, numeric),
        typed::fixes_book::<E>(c, coding), typed::covered_event::<E>(coding, candidate),
        junco_core::verify::history_specs::event_wf(typed::numeric_event::<E>(coding, candidate), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> typed::covered_event::<E>(coding, history[i]),
    ensures semantics::policy_denies(rule_views(rules), candidate, history)
        == encoding::n_policy_denies(numeric, typed::numeric_event::<E>(coding, candidate), typed::numeric_history::<E>(coding, history)),
{
    assert forall|i: int| 0 <= i < rules.len() implies
        semantics::rule_denies(rule_views(rules)[i], candidate, history)
            == encoding::n_rule_denies(numeric[i], typed::numeric_event::<E>(coding, candidate), typed::numeric_history::<E>(coding, history)) by {
        lemma_rule_denies(c, rules[i], flats[i], templates[i], numeric[i], coding, candidate, history);
    }
}

/// A universal numeric coverage result is sound for all typed component types.
pub(crate) proof fn lemma_policy_covers<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        inclusion::n_covers(views::ndomains(a.universes), by_n, left_n),
    ensures semantics::covers(a@.domains, rule_views(by), encoding::rule_view(left)),
{
    assert forall|c: Seq<E::Component>, h: Seq<Seq<E::Component>>|
        semantics::event_in(a@.domains, c) && semantics::history_in(a@.domains, h)
            && semantics::rule_denies(encoding::rule_view(left), c, h)
        implies semantics::policy_denies(rule_views(by), c, h) by {
        assert forall|i: int| 0 <= i < h.len() implies h[i].len() == c.len() by {
            assert(semantics::event_in(a@.domains, h[i]));
        }
        let coding = typed::lemma_pair_embedding(a.constants, c, h);
        typed::lemma_analyzer_domain_embedding(a, coding, c, h);
        lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
        lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
    }
}

/// The numeric obligation required of a single decided case, independent of its split family.
pub(crate) open spec fn realized_uncovered(d: encoding::NDomains, by: Seq<encoding::NRule>,
    left: encoding::NRule, g: inclusion::Constraint, letters: Seq<search::Assignment>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, g) && search::follows(d, letters, theta, w)
        ==> encoding::n_rule_denies(left, theta, w) && !encoding::n_policy_denies(by, theta, w)
}

/// Reconstruction and one shared coding transfer every realization, including finite domains.
pub(crate) proof fn lemma_policy_counterexample<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>,
    result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        realized_uncovered(views::ndomains(a.universes), by_n, left_n,
            implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets)),
    ensures analyzer::every_instance(a@, result@, analyzer::uncovered(rule_views(by), encoding::rule_view(left))),
        analyzer::unrestricted_components_infinite(a@.domains) ==> (
            analyzer::cex_has_instance(a@, result@)
                && !semantics::covers(a@.domains, rule_views(by), encoding::rule_view(left))),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    assert forall|f: analyzer::FreshChoice<E::Component>|
        analyzer::admissible(a@, result@, f) implies {
            &&& semantics::event_in(a@.domains, analyzer::event_of(result@.candidate, f))
            &&& semantics::history_in(a@.domains, analyzer::history_of(result@, f))
            &&& analyzer::uncovered(rule_views(by), encoding::rule_view(left))(
                analyzer::event_of(result@.candidate, f), analyzer::history_of(result@, f))
        } by {
        let coding = typed::lemma_slot_embedding(a, candidate, history, f);
        let c = analyzer::event_of(result@.candidate, f);
        let h = analyzer::history_of(result@, f);
        let theta = typed::numeric_event::<E>(coding, c);
        let w = typed::numeric_history::<E>(coding, h);
        assert(encoding::n_event_in(views::ndomains(a.universes), theta));
        assert(encoding::n_history_in(views::ndomains(a.universes), w));
        assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
        assert(search::follows(views::ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
        typed::lemma_domain_event(a, coding, c);
        assert forall|j: int| 0 <= j < h.len() implies semantics::event_in(a@.domains, h[j]) by {
            assert(w[j] == typed::numeric_event::<E>(coding, h[j]));
            typed::lemma_domain_event(a, coding, h[j]);
        }
        lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
        lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
    }
    if analyzer::unrestricted_components_infinite(a@.domains) {
        lemma_reconstructed_has_instance(a, g, letters, alphabets, result);
        lemma_not_covers(a@, rule_views(by), encoding::rule_view(left), result@);
    }
}

/// Refinement loops accumulate one typed coverage fact for each right-hand rule.
pub(crate) proof fn lemma_refinement_holds<C: PartialEq>(
    a: analyzer::AnalyzerView<C>, p: Seq<nat>, q: Seq<nat>)
    requires forall|j: int| 0 <= j < q.len()
        ==> semantics::covers(a.domains, analyzer::rules_of(a, p), a.rules[q[j] as int]),
    ensures semantics::refines(a.domains, analyzer::rules_of(a, p), analyzer::rules_of(a, q)),
{
    semantics::theorem_refines_iff_covers::<C>();
    assert forall|j: int| 0 <= j < analyzer::rules_of(a, q).len()
        implies semantics::covers(a.domains, analyzer::rules_of(a, p), analyzer::rules_of(a, q)[j]) by {}
}

/// An uncovered rule of the right-hand policy witnesses non-refinement.
pub(crate) proof fn lemma_refinement_counterexample<C: PartialEq>(
    a: analyzer::AnalyzerView<C>, p: Seq<nat>, q: Seq<nat>, j: int, cex: analyzer::CexView<C>)
    requires 0 <= j < q.len(),
        analyzer::every_instance(a, cex, analyzer::uncovered(analyzer::rules_of(a, p), a.rules[q[j] as int])),
        analyzer::cex_has_instance(a, cex),
    ensures !semantics::refines(a.domains, analyzer::rules_of(a, p), analyzer::rules_of(a, q)),
{
    let f = choose|f: analyzer::FreshChoice<C>| analyzer::admissible(a, cex, f);
    let c = analyzer::event_of(cex.candidate, f);
    let h = analyzer::history_of(cex, f);
    assert(semantics::rule_denies(analyzer::rules_of(a, q)[j], c, h));
    assert(semantics::policy_denies(analyzer::rules_of(a, q), c, h));
    assert(semantics::event_in(a.domains, c) && semantics::history_in(a.domains, h));
    assert(semantics::policy_permits(analyzer::rules_of(a, p), c, h));
    assert(!semantics::policy_permits(analyzer::rules_of(a, q), c, h));
}

/// Keep existence separate so the symbolic semantics on small types stays unchanged.
pub(crate) proof fn lemma_not_covers<C: PartialEq>(a: analyzer::AnalyzerView<C>,
    by: Seq<RuleView<C>>, left: RuleView<C>, cex: analyzer::CexView<C>)
    requires analyzer::every_instance(a, cex, analyzer::uncovered(by, left)),
        analyzer::cex_has_instance(a, cex),
    ensures !semantics::covers(a.domains, by, left),
{
    let f = choose|f: analyzer::FreshChoice<C>| analyzer::admissible(a, cex, f);
    let c = analyzer::event_of(cex.candidate, f);
    let h = analyzer::history_of(cex, f);
    assert(semantics::event_in(a.domains, c) && semantics::history_in(a.domains, h));
    assert(semantics::rule_denies(left, c, h) && !semantics::policy_denies(by, c, h));
}

pub(crate) proof fn lemma_reconstructed_has_instance<E: Event>(a: PolicyAnalyzer<E>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        analyzer::unrestricted_components_infinite(a@.domains),
        slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
    ensures analyzer::cex_has_instance(a@, result@),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    slots::lemma_used_at(a.constants, candidate, history);
    assert forall|k: int| 0 <= k < a@.domains.len() && a@.domains[k] is Some
        implies analyzer::fresh_used(result@, k) == ISet::<nat>::empty() by {
        assert(a.universes@[k] is Some);
        assert(slots::slot_domain(candidate[k], views::domain_view(a.universes@[k])));
        assert forall|i: int| 0 <= i < history.len() implies history[i][k] is Code by {}
        assert(analyzer::fresh_used(result@, k) =~= ISet::<nat>::empty());
    }
    typed::lemma_native_equivalence::<E>();
    analyzer::lemma_fresh_finite(result@);
    analyzer::lemma_choice_exists_mixed(a@, result@);
}

pub(crate) proof fn lemma_redundancy_result<C: PartialEq>(a: analyzer::AnalyzerView<C>,
    rule: nat, policy: Seq<nat>, v: analyzer::InclusionView<C>)
    requires analyzer::covered_correct(a, rule, analyzer::without_rule(policy, rule), v),
    ensures analyzer::redundant_correct(a, rule, policy, v),
{}

pub(crate) proof fn lemma_refinement_result<C: PartialEq>(a: analyzer::AnalyzerView<C>,
    p: Seq<nat>, q: Seq<nat>, j: int, v: analyzer::InclusionView<C>)
    requires 0 <= j < q.len(), !(v is Holds), analyzer::covered_correct(a, q[j], p, v),
    ensures analyzer::at_least_as_strict_correct(a, p, q, v),
{
    if let analyzer::InclusionView::Counterexample(cex) = v {
        assert(analyzer::rules_of(a, q)[j] == a.rules[q[j] as int]);
        if analyzer::cex_has_instance(a, cex) {
            lemma_refinement_counterexample(a, p, q, j, cex);
        }
        assert(exists|k: int| 0 <= k < analyzer::rules_of(a, q).len()
            && analyzer::every_instance(a, cex, analyzer::uncovered(analyzer::rules_of(a, p), analyzer::rules_of(a, q)[k])));
    }
}
}
