//! Real-event policy clients of the finite numeric equality-class embedding.
//!
//! Each rule keeps its own head and mode. Holds needs no capacity premise;
//! nonvacuity is conditional only on the returned counterexample's R3 capacity.

use super::frontend::*;
use super::{self as views, reconstruction as slots, search_exec as exec, typed_numeric as typed};
use crate::analyzer::{Constants, Counterexample, PolicyAnalyzer};
use crate::constraint::{Constraint, Letter};
use crate::spec::analyzer;
use history_semantics::verify::refinement::{encoding, implementation, inclusion, search};
use history_syntax::spec::events::{arity, event_view};
use history_syntax::{Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::spec::{questions as q, semantics as s};
use junco_core::verify::flatten as fl;
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas,
    crate::verify::frontend::domain_view::lemma_analyzer_view};

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

pub(crate) open spec fn sources_known<E: Event>(rules: Seq<Rule<E>>, known: Seq<Set<E::Component>>) -> bool {
    known.len() == arity::<E>() && forall|j: int, k: int| 0 <= j < rules.len() && 0 <= k < arity::<E>()
        ==> #[trigger] q::rule_constants(rules[j]@)[k].subset_of(known[k])
}

pub(crate) proof fn lemma_sources_coding<E: Event>(c: Constants<E>, coding: typed::NatCoding<E>,
    rules: Seq<Rule<E>>, known: Seq<Set<E::Component>>)
    requires typed::fixes_known::<E>(c, coding, known), sources_known(rules, known),
        forall|j: int| 0 <= j < rules.len() ==> rules[j].head@.len() == arity::<E>(),
    ensures forall|j: int| 0 <= j < rules.len() ==> typed::fixes_known::<E>(c, coding, q::rule_constants(rules[j]@)),
{
    assert forall|j: int| 0 <= j < rules.len()
        implies typed::fixes_known::<E>(c, coding, q::rule_constants(rules[j]@)) by {
        typed::lemma_fixes_known_subset(c, coding, known, q::rule_constants(rules[j]@));
    }
}

/// Unlike the tail-only helper, this equation preserves the rule's actual mode.
pub(crate) proof fn lemma_rule_denies<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, template: FlatPair<u64>, n: encoding::NRule,
    coding: typed::NatCoding<E>, candidate: E, history: Seq<E>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(), rule_bridge_wf(c, rule, flat, template, n),
        (typed::fixes_book::<E>(c, coding) || typed::fixes_known::<E>(c, coding, q::rule_constants(rule@))),
        typed::covered_event::<E>(coding, event_view(candidate)),
        junco_core::verify::history_specs::event_wf(typed::numeric_event::<E>(coding, event_view(candidate)), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> typed::covered_event::<E>(coding, event_view(history[i])),
    ensures s::rule_violated(rule, candidate, history)
        == encoding::n_rule_denies(n, typed::numeric_event::<E>(coding, event_view(candidate)), typed::numeric_history::<E>(coding, typed::projected_history(history))),
{
    typed::lemma_source_language(rule, flat, template, c, coding, candidate, history);
    assert(n.head == typed::template_head(template));
}

/// Pointwise rule transport needs neither a shared head nor a shared mode.
pub(crate) proof fn lemma_policy_denies<E: Event>(c: Constants<E>, rules: Seq<Rule<E>>,
    flats: Seq<FlatRule<E::Component>>, templates: Seq<FlatPair<u64>>, numeric: Seq<encoding::NRule>,
    coding: typed::NatCoding<E>, candidate: E, history: Seq<E>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(), policy_bridge_wf(c, rules, flats, templates, numeric),
        (typed::fixes_book::<E>(c, coding) || forall|j: int| 0 <= j < rules.len()
            ==> typed::fixes_known::<E>(c, coding, q::rule_constants(rules[j]@))),
        typed::covered_event::<E>(coding, event_view(candidate)),
        junco_core::verify::history_specs::event_wf(typed::numeric_event::<E>(coding, event_view(candidate)), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> typed::covered_event::<E>(coding, event_view(history[i])),
    ensures s::policy_denies(rules, candidate, history)
        == encoding::n_policy_denies(numeric, typed::numeric_event::<E>(coding, event_view(candidate)), typed::numeric_history::<E>(coding, typed::projected_history(history))),
{
    assert forall|i: int| 0 <= i < rules.len() implies
        s::rule_violated(rules[i], candidate, history)
            == encoding::n_rule_denies(numeric[i], typed::numeric_event::<E>(coding, event_view(candidate)), typed::numeric_history::<E>(coding, typed::projected_history(history))) by {
        lemma_rule_denies(c, rules[i], flats[i], templates[i], numeric[i], coding, candidate, history);
    }
}

/// A universal numeric coverage result is sound for all real event types.
pub(crate) proof fn lemma_policy_covers<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        inclusion::n_covers(views::ndomains(a.universes), by_n, left_n),
    ensures q::covers(a@.domains, by, left),
{
    assert forall|c: E, h: Seq<E>| q::in_domains(a@.domains, c, h)
        && s::rule_violated(left, c, h) implies s::policy_denies(by, c, h) by {
        let coding = typed::lemma_pair_embedding(a.constants, event_view(c), typed::projected_history(h));
        assert forall|j: int| 0 <= j < h.len()
            implies typed::covered_event::<E>(coding, event_view(h[j])) by {
            assert(typed::projected_history(h)[j] == event_view(h[j]));
            assert(typed::covered_event::<E>(coding, typed::projected_history(h)[j]));
        }
        typed::lemma_analyzer_domain_embedding(a, coding, c, h);
        lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
        lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
    }
}

/// The numeric obligation of one decided case, independent of its split family.
pub(crate) open spec fn realized_uncovered(d: encoding::NDomains, by: Seq<encoding::NRule>,
    left: encoding::NRule, g: inclusion::Constraint, letters: Seq<search::Assignment>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, g) && search::follows(d, letters, theta, w)
        ==> encoding::n_rule_denies(left, theta, w) && !encoding::n_policy_denies(by, theta, w)
}

/// Reconstruction transports every real instance through one shared R3 choice.
pub(crate) proof fn lemma_policy_counterexample<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>,
    result: Counterexample<E>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        sources_known(by.push(left), result@.known),
        realized_uncovered(views::ndomains(a.universes), by_n, left_n,
            implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets)),
    ensures q::counterexample_wf::<E>(a@.domains, result@),
        q::every_instance(a@.domains, result@, |c: E, h: Seq<E>| s::rule_violated(left, c, h) && !s::policy_denies(by, c, h)),
        q::counterexample_capacity::<E>(a@.domains, result@) ==> (
            q::has_instance::<E>(a@.domains, result@) && !q::covers(a@.domains, by, left)),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history, result@.known)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    slots::lemma_counterexample_wf(a, g, letters, candidate, history, result@.known);
    assert forall|c: E, h: Seq<E>| q::instance(a@.domains, result@, c, h)
        implies s::rule_violated(left, c, h) && !s::policy_denies(by, c, h) by {
        let coding = typed::lemma_slot_embedding(a, candidate, history, c, h, result@.known);
        lemma_sources_coding(a.constants, coding, by.push(left), result@.known);
        assert(by.push(left)[by.len() as int] == left);
        assert(typed::fixes_known::<E>(a.constants, coding, q::rule_constants(left@)));
        assert forall|j: int| 0 <= j < by.len()
            implies typed::fixes_known::<E>(a.constants, coding, q::rule_constants(by[j]@)) by {
            assert(by.push(left)[j] == by[j]);
            assert(typed::fixes_known::<E>(a.constants, coding, q::rule_constants(by.push(left)[j]@)));
        }
        let theta = typed::numeric_event::<E>(coding, event_view(c));
        let w = typed::numeric_history::<E>(coding, typed::projected_history(h));
        assert(slots::candidate_field_ok(a.constants, a.universes, g, 0, candidate[0]));
        slots::lemma_candidate_slots(a.constants, a.universes, g, candidate, typed::numeric_fresh::<E>(a.constants));
        assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
        assert(search::follows(views::ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
        lemma_rule_denies(a.constants, left, left_flat, left_template, left_n, coding, c, h);
        lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
    }
    if q::counterexample_capacity::<E>(a@.domains, result@) {
        q::lemma_counterexample_has_instance::<E>(a@.domains, result@);
        lemma_not_covers(a@, by, left, result@);
    }
}

pub(crate) proof fn lemma_refinement_holds<E: Event>(a: analyzer::AnalyzerView<E>, p: Seq<nat>, other: Seq<nat>)
    requires forall|j: int| 0 <= j < other.len()
        ==> q::covers(a.domains, analyzer::rules_of(a, p), a.rules[other[j] as int]),
    ensures q::refines(a.domains, analyzer::rules_of(a, p), analyzer::rules_of(a, other)),
{
    assert forall|c: E, h: Seq<E>| q::in_domains(a.domains, c, h)
        && !s::policy_denies(analyzer::rules_of(a, p), c, h)
        implies !s::policy_denies(analyzer::rules_of(a, other), c, h) by {
        assert forall|j: int| 0 <= j < other.len() implies
            !s::rule_violated(a.rules[other[j] as int], c, h) by {}
    }
}

pub(crate) proof fn lemma_refinement_counterexample<E: Event>(a: analyzer::AnalyzerView<E>,
    p: Seq<nat>, other: Seq<nat>, j: int, cex: q::Counterexample<E::Component>)
    requires 0 <= j < other.len(),
        q::every_instance(a.domains, cex, |c: E, h: Seq<E>| s::rule_violated(a.rules[other[j] as int], c, h)
            && !s::policy_denies(analyzer::rules_of(a, p), c, h)),
        q::has_instance::<E>(a.domains, cex),
    ensures !q::refines(a.domains, analyzer::rules_of(a, p), analyzer::rules_of(a, other)),
{
    let (c, h) = choose|c: E, h: Seq<E>| q::instance(a.domains, cex, c, h);
    assert(s::rule_violated(analyzer::rules_of(a, other)[j], c, h));
    assert(s::policy_denies(analyzer::rules_of(a, other), c, h));
}

pub(crate) proof fn lemma_not_covers<E: Event>(a: analyzer::AnalyzerView<E>,
    by: Seq<Rule<E>>, left: Rule<E>, cex: q::Counterexample<E::Component>)
    requires q::every_instance(a.domains, cex, |c: E, h: Seq<E>| s::rule_violated(left, c, h) && !s::policy_denies(by, c, h)),
        q::has_instance::<E>(a.domains, cex),
    ensures !q::covers(a.domains, by, left),
{
    let (c, h) = choose|c: E, h: Seq<E>| q::instance(a.domains, cex, c, h);
    assert(q::in_domains(a.domains, c, h));
    assert(s::rule_violated(left, c, h) && !s::policy_denies(by, c, h));
}


/// The same selected right-hand rule supplies soundness and case-local minimality.
pub(crate) proof fn lemma_refinement_result<E: Event>(a: analyzer::AnalyzerView<E>,
    p: Seq<nat>, other: Seq<nat>, j: int, v: analyzer::QueryResult<E::Component>)
    requires 0 <= j < other.len(), !(v is Holds),
        other[j] < a.rules.len(), analyzer::covered_spec(a, other[j], p, v),
    ensures analyzer::at_least_as_strict_spec(a, p, other, v),
{
    if let analyzer::QueryResult::Counterexample(cex) = v {
        if q::counterexample_capacity::<E>(a.domains, cex) {
            lemma_refinement_counterexample(a, p, other, j, cex);
        }
        assert(exists|k: int| 0 <= k < other.len() && other[k] < a.rules.len()
            && q::every_instance(a.domains, cex, |c: E, h: Seq<E>|
                s::rule_violated(a.rules[other[k] as int], c, h) && !s::policy_denies(analyzer::rules_of(a, p), c, h))
            && (forall|c: E, h: Seq<E>| q::instance(a.domains, cex, c, h) ==>
                q::shortest_in_case(a.domains, cex.known, c, cex.history.len(), |c2: E, h2: Seq<E>|
                    s::rule_violated(a.rules[other[k] as int], c2, h2) && !s::policy_denies(analyzer::rules_of(a, p), c2, h2)))) by {
            assert(0 <= j < other.len());
        }
    }
}
}
