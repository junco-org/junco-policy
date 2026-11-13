//! Policy-level clients of the existing typed/numeric pair and slot embeddings, concluding the
//! R3/R6 predicates over real events.
//!
//! Each rule retains its own head and mode. The same finite equality-class coding is shared
//! by all rules in a query; declared domains are transported by `typed_numeric` unchanged.

use super::frontend::*;
use super::{
    self as views, component_at, reconstruction as slots, search_exec as exec,
    typed_numeric as typed,
};
use crate::analyzer::{Constants, Counterexample, PolicyAnalyzer};
use crate::constraint::{Constraint, Letter};
use crate::spec::analyzer::{
    AnalyzerView, at_least_as_strict_spec, counterexample_spec, covered_spec, rules_of, uncovered,
};
use history_semantics::verify::refinement::{
    encoding, implementation, inclusion, search, semantics,
};
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{RuleView, arity, event_view};
use history_syntax::{Event, Rule};
use junco_core::flat::{FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::spec::questions::{
    CexView, FreshChoice, InclusionView, ValueView, admissible, capacity_for, cex_arity,
    cex_has_instance, covers, every_instance, in_domains, instantiates, refines,
};
use junco_core::spec::semantics::{history_view, policy_denies, rule_violated};
use junco_core::verify::capacity::{cex_constants_tagged, lemma_capacity_gives_instance};
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

/// A coding covering the candidate's and the history's tuples.
pub(crate) open spec fn pair_covered<E: Event>(coding: typed::NatCoding<E>, candidate: E, history: Seq<E>) -> bool {
    &&& typed::covered_event::<E>(coding, event_view(candidate))
    &&& junco_core::verify::history_specs::event_wf(typed::numeric_event::<E>(coding, event_view(candidate)), arity::<E>())
    &&& forall|i: int| 0 <= i < history.len() ==> typed::covered_event::<E>(coding, #[trigger] history_view(history)[i])
}

/// Unlike the tail-only helper, this equation preserves the rule's actual mode (`def:violates`).
pub(crate) proof fn lemma_rule_violated<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, template: FlatPair<u64>, n: encoding::NRule,
    coding: typed::NatCoding<E>, candidate: E, history: Seq<E>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), rule_bridge_wf(c, rule, flat, template, n),
        typed::fixes_book::<E>(c, coding), pair_covered::<E>(coding, candidate, history),
    ensures rule_violated(encoding::rule_view(rule), candidate, history)
        == encoding::n_rule_denies(n, typed::numeric_event::<E>(coding, event_view(candidate)),
            typed::numeric_history::<E>(coding, history_view(history))),
{
    typed::lemma_source_language(rule, flat, template, c, coding, event_view(candidate), history_view(history));
    assert(n.head == typed::template_head(template));
}

/// Pointwise rule transport needs neither a shared head nor a shared mode (`def:policy-violates`).
pub(crate) proof fn lemma_policy_denies<E: Event>(c: Constants<E>, rules: Seq<Rule<E>>,
    flats: Seq<FlatRule<E::Component>>, templates: Seq<FlatPair<u64>>, numeric: Seq<encoding::NRule>,
    coding: typed::NatCoding<E>, candidate: E, history: Seq<E>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), policy_bridge_wf(c, rules, flats, templates, numeric),
        typed::fixes_book::<E>(c, coding), pair_covered::<E>(coding, candidate, history),
    ensures policy_denies(rule_views(rules), candidate, history)
        == encoding::n_policy_denies(numeric, typed::numeric_event::<E>(coding, event_view(candidate)),
            typed::numeric_history::<E>(coding, history_view(history))),
{
    assert forall|i: int| 0 <= i < rules.len() implies
        rule_violated(rule_views(rules)[i], candidate, history)
            == encoding::n_rule_denies(numeric[i], typed::numeric_event::<E>(coding, event_view(candidate)),
                typed::numeric_history::<E>(coding, history_view(history))) by {
        lemma_rule_violated(c, rules[i], flats[i], templates[i], numeric[i], coding, candidate, history);
    }
}

/// A real pair in the domains embeds into the analyzer's numeric domains.
pub(crate) proof fn lemma_pair_in_domains<E: Event>(a: PolicyAnalyzer<E>, candidate: E, history: Seq<E>)
    -> (coding: typed::NatCoding<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), in_domains::<E>(a@.domains, candidate, history),
    ensures typed::fixes_book::<E>(a.constants, coding), pair_covered::<E>(coding, candidate, history),
        encoding::n_theta_ok(views::ndomains(a.universes), typed::numeric_event::<E>(coding, event_view(candidate))),
        encoding::n_history_in(views::ndomains(a.universes), typed::numeric_history::<E>(coding, history_view(history))),
        typed::numeric_history::<E>(coding, history_view(history)).len() == history.len(),
{
    let c = event_view(candidate);
    let h = history_view(history);
    assert forall|i: int| 0 <= i < h.len() implies h[i].len() == c.len() by {
        assert(junco_core::spec::questions::event_in(a@.domains, h[i]));
    }
    let coding = typed::lemma_pair_embedding(a.constants, c, h);
    typed::lemma_analyzer_domain_embedding(a, coding, c, h);
    coding
}

/// A universal numeric coverage result is sound for all typed component types (A1, Holds).
pub(crate) proof fn lemma_policy_covers<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        inclusion::n_covers(views::ndomains(a.universes), by_n, left_n),
    ensures covers::<E>(a@.domains, rule_views(by), encoding::rule_view(left)),
{
    assert forall|c: E, h: Seq<E>|
        in_domains::<E>(a@.domains, c, h) && #[trigger] rule_violated(encoding::rule_view(left), c, h)
        implies policy_denies(rule_views(by), c, h) by {
        let coding = lemma_pair_in_domains(a, c, h);
        lemma_rule_violated(a.constants, left, left_flat, left_template, left_n, coding, c, h);
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

/// The slot embedding of a real instance of a reconstructed counterexample.
pub(crate) proof fn lemma_instance_embedding<E: Event>(a: PolicyAnalyzer<E>, g: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>,
    candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>,
    f: FreshChoice<E::Component>, c: E, h: Seq<E>) -> (coding: typed::NatCoding<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), stored_known(a),
        slots::constructed(a.constants, a.universes, g, letters, candidate, history),
        result@ == slots::cex_of_slots(a.constants, candidate, history),
        implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
            exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants)),
        admissible::<E>(a@.domains, a@.known, result@, f), instantiates::<E>(result@, f, c, h),
    ensures typed::fixes_book::<E>(a.constants, coding), pair_covered::<E>(coding, c, h),
        in_domains::<E>(a@.domains, c, h),
        encoding::n_theta_ok(views::ndomains(a.universes), typed::numeric_event::<E>(coding, event_view(c))),
        inclusion::sat_by(typed::numeric_event::<E>(coding, event_view(c)), implementation::constraint_of(g@)),
        search::follows(views::ndomains(a.universes), exec::chain_assignments(letters, alphabets),
            typed::numeric_event::<E>(coding, event_view(c)), typed::numeric_history::<E>(coding, history_view(h))),
        typed::numeric_history::<E>(coding, history_view(h)).len() == h.len(),
{
    let coding = typed::lemma_slot_embedding(a, candidate, history, f);
    let ct = event_view(c);
    let ht = history_view(h);
    assert(ct == junco_core::spec::questions::event_of(result@.candidate, f));
    assert(ht == junco_core::spec::questions::history_of(result@, f));
    let theta = typed::numeric_event::<E>(coding, ct);
    let w = typed::numeric_history::<E>(coding, ht);
    assert(encoding::n_event_in(views::ndomains(a.universes), theta));
    assert(encoding::n_history_in(views::ndomains(a.universes), w));
    assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
    assert(search::follows(views::ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
    typed::lemma_domain_event(a, coding, ct);
    assert forall|j: int| 0 <= j < ht.len() implies junco_core::spec::questions::event_in(a@.domains, #[trigger] ht[j]) by {
        assert(w[j] == typed::numeric_event::<E>(coding, ht[j]));
        typed::lemma_domain_event(a, coding, ht[j]);
    }
    coding
}

/// Reconstruction and one shared coding transfer every realization, including finite domains
/// (A2 for the policy queries).
pub(crate) proof fn lemma_policy_counterexample<E: Event>(a: PolicyAnalyzer<E>, left: Rule<E>,
    left_flat: FlatRule<E::Component>, left_template: FlatPair<u64>, left_n: encoding::NRule,
    by: Seq<Rule<E>>, by_flat: Seq<FlatRule<E::Component>>, by_templates: Seq<FlatPair<u64>>,
    by_n: Seq<encoding::NRule>, g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>,
    result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), stored_known(a),
        rule_bridge_wf(a.constants, left, left_flat, left_template, left_n),
        policy_bridge_wf(a.constants, by, by_flat, by_templates, by_n),
        slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        realized_uncovered(views::ndomains(a.universes), by_n, left_n,
            implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets)),
    ensures counterexample_spec::<E>(a@, result@, uncovered::<E>(rule_views(by), encoding::rule_view(left))),
        cex_has_instance::<E>(a@.domains, a@.known, result@)
            ==> !covers::<E>(a@.domains, rule_views(by), encoding::rule_view(left)),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    let fails = uncovered::<E>(rule_views(by), encoding::rule_view(left));
    assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(a@.domains, a@.known, result@, f) && #[trigger] instantiates::<E>(result@, f, c, h)
        implies in_domains::<E>(a@.domains, c, h) && fails(c, h) by {
        let coding = lemma_instance_embedding(a, g, letters, alphabets, result, candidate, history, f, c, h);
        lemma_rule_violated(a.constants, left, left_flat, left_template, left_n, coding, c, h);
        lemma_policy_denies(a.constants, by, by_flat, by_templates, by_n, coding, c, h);
    }
    lemma_reconstructed_has_instance(a, g, letters, alphabets, result);
    if cex_has_instance::<E>(a@.domains, a@.known, result@) {
        lemma_not_covers::<E>(a@, rule_views(by), encoding::rule_view(left), result@);
    }
}

/// Refinement loops accumulate one typed coverage fact for each right-hand rule.
pub(crate) proof fn lemma_refinement_holds<E: Event>(
    a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>)
    requires forall|j: int| 0 <= j < q.len()
        ==> covers::<E>(a.domains, rules_of(a, p), a.rules[q[j] as int]),
    ensures refines::<E>(a.domains, rules_of(a, p), rules_of(a, q)),
{
    semantics::theorem_refines_iff_covers::<E>();
    assert forall|j: int| 0 <= j < rules_of(a, q).len()
        implies covers::<E>(a.domains, rules_of(a, p), rules_of(a, q)[j]) by {}
}

/// An uncovered rule of the right-hand policy witnesses non-refinement.
pub(crate) proof fn lemma_refinement_counterexample<E: Event>(
    a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>, j: int, cex: CexView<E::Component>)
    requires 0 <= j < q.len(),
        every_instance::<E>(a.domains, a.known, cex, uncovered::<E>(rules_of(a, p), a.rules[q[j] as int])),
        cex_has_instance::<E>(a.domains, a.known, cex),
    ensures !refines::<E>(a.domains, rules_of(a, p), rules_of(a, q)),
{
    let (f, c, h) = choose|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h);
    assert(uncovered::<E>(rules_of(a, p), a.rules[q[j] as int])(c, h));
    assert(rules_of(a, q)[j] == a.rules[q[j] as int]);
    assert(rule_violated(rules_of(a, q)[j], c, h));
    assert(policy_denies(rules_of(a, q), c, h));
    assert(in_domains::<E>(a.domains, c, h) && junco_core::spec::semantics::policy_permits(rules_of(a, p), c, h));
    assert(!junco_core::spec::semantics::policy_permits(rules_of(a, q), c, h));
}

/// Keep existence separate so the symbolic semantics on small types stays unchanged.
pub(crate) proof fn lemma_not_covers<E: Event>(a: AnalyzerView<E::Component>,
    by: Seq<RuleView<E::Component>>, left: RuleView<E::Component>, cex: CexView<E::Component>)
    requires every_instance::<E>(a.domains, a.known, cex, uncovered::<E>(by, left)),
        cex_has_instance::<E>(a.domains, a.known, cex),
    ensures !covers::<E>(a.domains, by, left),
{
    let (f, c, h) = choose|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h);
    assert(rule_violated(left, c, h) && !policy_denies(by, c, h));
}

/// Every constant of a reconstructed counterexample comes from the book of its own coordinate.
pub(crate) proof fn lemma_reconstructed_shape<E: Event>(a: PolicyAnalyzer<E>,
    candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    requires constants_wf(a.constants), slots::slot_wf(a.constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> slots::slot_wf(a.constants, history[i]),
    ensures cex_arity(slots::cex_of_slots(a.constants, candidate, history), arity::<E>()),
        cex_constants_tagged::<E>(slots::cex_of_slots(a.constants, candidate, history)),
{
    let cex = slots::cex_of_slots(a.constants, candidate, history);
    assert forall|i: int| 0 <= i < cex.candidate.len() implies match #[trigger] cex.candidate[i] {
        ValueView::Constant(k) => E::coordinate_spec(k) == i,
        ValueView::Fresh(_) => true,
    } by {
        if let implementation::SlotView::Code(v) = candidate[i] {
            assert(slots::code_field(a.constants, component_at(i as usize), v));
        }
    }
    assert forall|j: int, i: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
        implies match #[trigger] cex.history[j][i] {
            ValueView::Constant(k) => E::coordinate_spec(k) == i,
            ValueView::Fresh(_) => true,
        } by {
        assert(cex.history[j] == slots::components_of_slots(a.constants, history[j]));
        if let implementation::SlotView::Code(v) = history[j][i] {
            assert(slots::code_field(a.constants, component_at(i as usize), v));
        }
    }
}

/// Under capacity for its own fresh values, a reconstructed counterexample has a real instance.
pub(crate) proof fn lemma_reconstructed_has_instance<E: Event>(a: PolicyAnalyzer<E>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
    ensures cex_arity(result@, arity::<E>()),
        capacity_for::<E>(a@.domains, a@.known, result@) ==> cex_has_instance::<E>(a@.domains, a@.known, result@),
{
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history)
            && implementation::reconstruction_ok(views::ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    lemma_reconstructed_shape::<E>(a, candidate, history);
    if capacity_for::<E>(a@.domains, a@.known, result@) {
        lemma_capacity_gives_instance::<E>(a@.domains, a@.known, result@);
    }
}

/// Refinement: a non-Holds coverage verdict for `q[j]` is the refinement verdict (A3).
pub(crate) proof fn lemma_refinement_result<E: Event>(a: AnalyzerView<E::Component>,
    p: Seq<nat>, q: Seq<nat>, j: int, v: InclusionView<E::Component>)
    requires 0 <= j < q.len(), !(v is Holds), covered_spec::<E>(a, q[j], p, v),
    ensures at_least_as_strict_spec::<E>(a, p, q, v),
{
    if let InclusionView::Counterexample(cex) = v {
        assert(rules_of(a, q)[j] == a.rules[q[j] as int]);
        if cex_has_instance::<E>(a.domains, a.known, cex) {
            lemma_refinement_counterexample::<E>(a, p, q, j, cex);
        }
        assert(counterexample_spec::<E>(a, cex, uncovered::<E>(rules_of(a, p), rules_of(a, q)[j])));
    }
}
}
