//! Reviewer theorems for the analyzer and its bridge to the monitor.
//!
//! Every statement uses only public items: the specification modules, `PolicyAnalyzer`, `Domains`, `Validator`.
//! The `theorem_*` take the `*_spec` postcondition of a query as hypothesis and conclude the
//! readable property; `analyzer_client` shows the postconditions are reachable from the public
//! contracts alone; the `stmt_analyzer_*` are the rows `paper.rs` points at.
#![cfg(all(verus_keep_ghost, feature = "runtime"))]

extern crate alloc;

use history_analysis::spec::analyzer::{
    AnalyzerView, add_rule_capacity, at_least_as_strict_spec, constructor_capacity,
    counterexample_spec, covered_spec, declared_sets, ids_of, known_count, known_with,
    query_capacity, redundant_spec, removal_preserves_decisions, rules_of, tail_fails,
    tail_included_spec, uncovered, without_rule,
};
use history_analysis::verify::analyzer_obligations;
use history_analysis::{Domains, Inclusion, PolicyAnalyzer};
use history_semantics::spec::monitor::{ValidatorView, check_step};
use history_semantics::validator::Decision;
use history_semantics::verify::refinement::inclusion::theorem_vacuity_via_refinement;
use history_syntax::event::Component2;
use history_syntax::spec::events::{HeadView, RegexView, RuleView, arity, event_view};
use history_syntax::{Event, Head, RegexExpr, Rule, RuleMode};
use junco_core::event::Request;
use junco_core::spec::hypotheses::{event_obligations, hash_coherent};
use junco_core::spec::questions::{
    CexView, DomainsView, FreshChoice, InclusionView, admissible, always_denies, capacity_for,
    cex_has_instance, covers, domains_wf, every_instance, forbid_all, fresh_capacity, fresh_used,
    in_domains, instantiates, minimal_in_case, never_denies, refines, rule_constants, same_profile,
    shortest, tails_included,
};
use junco_core::spec::semantics::{
    head_matches, history_view, lang, least_violation, policy_denies, policy_permits, rule_violated,
};
use junco_core::verify::capacity::{lemma_fresh_capacity_u32, lemma_fresh_capacity_u64};
use junco_core::verify::flatten::regex_cost;
use junco_core::verify::history_specs::no_invariant_failure;
use junco_core::verify::hypotheses::lemma_u32_u64_event_hypotheses;
use junco_core::{CompileError, HistoryError};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::array::group_array_axioms, vstd::slice::group_slice_axioms};

// ----- coverage decisions -----

/// `covered` answers coverage. `Holds` is coverage; a counterexample with a real instance
/// refutes it; when the counterexample's fresh values have capacity, `Holds` iff coverage.
pub open spec fn stmt_analyzer_coverage<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, v: InclusionView<E::Component>|
        #[trigger] covered_spec::<E>(a, rule, by, v) ==> {
            &&& v is Holds ==> covers::<E>(a.domains, rules_of(a, by), a.rules[rule as int])
            &&& v matches InclusionView::Counterexample(cex) ==> (cex_has_instance::<E>(a.domains, a.known, cex)
                ==> !covers::<E>(a.domains, rules_of(a, by), a.rules[rule as int]))
            &&& v matches InclusionView::Counterexample(cex) ==> (capacity_for::<E>(a.domains, a.known, cex)
                ==> !covers::<E>(a.domains, rules_of(a, by), a.rules[rule as int]))
        }
}

pub proof fn theorem_covered_decision<E: Event>()
    ensures stmt_analyzer_coverage::<E>(),
{
}

// ----- counterexamples are real -----

/// Every real instance `(c, h)` of a returned counterexample lies in the declared domains,
/// violates the rule and is denied by no rule of the policy; under capacity an instance exists.
pub open spec fn stmt_analyzer_real_counterexamples<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, cex: CexView<E::Component>|
        #[trigger] covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex)) ==> {
            &&& forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                ==> in_domains::<E>(a.domains, c, h)
                    && rule_violated(a.rules[rule as int], c, h)
                    && !policy_denies(rules_of(a, by), c, h)
            &&& capacity_for::<E>(a.domains, a.known, cex) ==> exists|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
        }
}

pub proof fn theorem_real_counterexamples<E: Event>()
    ensures stmt_analyzer_real_counterexamples::<E>(),
{
    assert forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, cex: CexView<E::Component>|
        #[trigger] covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex)) implies {
            &&& forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                ==> in_domains::<E>(a.domains, c, h)
                    && rule_violated(a.rules[rule as int], c, h)
                    && !policy_denies(rules_of(a, by), c, h)
            &&& capacity_for::<E>(a.domains, a.known, cex) ==> exists|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
        } by {
        let fails = uncovered::<E>(rules_of(a, by), a.rules[rule as int]);
        assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
            admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
            implies in_domains::<E>(a.domains, c, h)
                && rule_violated(a.rules[rule as int], c, h)
                && !policy_denies(rules_of(a, by), c, h) by {
            assert(fails(c, h));
        }
    }
}

/// A returned counterexample needs capacity only at undeclared coordinates.
pub proof fn theorem_counterexample_has_instance<E: Event>(
    a: AnalyzerView<E::Component>, cex: CexView<E::Component>, fails: spec_fn(E, Seq<E>) -> bool,
)
    requires counterexample_spec::<E>(a, cex, fails),
        forall|i: int| 0 <= i < arity::<E>() && a.domains[i] is None
            ==> fresh_capacity::<E>(a.domains, a.known, i, fresh_used(cex, i).len()),
    ensures cex_has_instance::<E>(a.domains, a.known, cex),
{
}

/// A fresh value at a declared coordinate cannot masquerade as a refutation.
pub proof fn theorem_declared_fresh_rejected<E: Event>(
    a: AnalyzerView<E::Component>, cex: CexView<E::Component>, i: int, n: nat,
    fails: spec_fn(E, Seq<E>) -> bool,
)
    requires 0 <= i < arity::<E>(), a.domains[i] is Some, fresh_used(cex, i).contains(n),
    ensures !counterexample_spec::<E>(a, cex, fails),
{
    if counterexample_spec::<E>(a, cex, fails) {
        assert(fresh_used(cex, i) =~= ISet::empty());
    }
}

/// A declared coordinate uses no fresh numbers, from the public counterexample contract.
pub proof fn lemma_declared_coordinate_zero<E: Event>(
    a: AnalyzerView<E::Component>, cex: CexView<E::Component>, coordinate: int,
    fails: spec_fn(E, Seq<E>) -> bool,
)
    requires counterexample_spec::<E>(a, cex, fails),
        0 <= coordinate < arity::<E>(), a.domains[coordinate] is Some,
    ensures fresh_used(cex, coordinate).len() == 0,
        fresh_capacity::<E>(a.domains, a.known, coordinate, fresh_used(cex, coordinate).len()),
{
    assert(fresh_used(cex, coordinate) =~= ISet::empty());
    let empty = Seq::<E::Component>::empty();
    assert(empty.len() == 0);
    assert(fresh_capacity::<E>(a.domains, a.known, coordinate, 0));
}

// ----- refinement and redundancy -----

/// Refinement: `at_least_as_strict(p, q)` decides `P ⊑ Q`; a counterexample with an
/// instance refutes it.
pub open spec fn stmt_analyzer_refinement<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>, v: InclusionView<E::Component>|
        #[trigger] at_least_as_strict_spec::<E>(a, p, q, v) ==> {
            &&& v is Holds ==> refines::<E>(a.domains, rules_of(a, p), rules_of(a, q))
            &&& v matches InclusionView::Counterexample(cex) ==> (cex_has_instance::<E>(a.domains, a.known, cex)
                ==> !refines::<E>(a.domains, rules_of(a, p), rules_of(a, q)))
        }
}

/// Redundancy: for a rule of the policy, `Holds` iff removing every occurrence
/// of it changes no decision inside the domains (when a counterexample has an instance).
pub open spec fn stmt_analyzer_redundancy<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>, v: InclusionView<E::Component>|
        #[trigger] redundant_spec::<E>(a, rule, policy, v) ==> {
            &&& v is Holds ==> removal_preserves_decisions::<E>(a, rule, policy)
                && covers::<E>(a.domains, rules_of(a, without_rule(policy, rule)), a.rules[rule as int])
            &&& v matches InclusionView::Counterexample(cex) ==> (policy.contains(rule)
                && cex_has_instance::<E>(a.domains, a.known, cex)
                ==> !removal_preserves_decisions::<E>(a, rule, policy))
        }
}

pub proof fn theorem_refinement<E: Event>()
    ensures stmt_analyzer_refinement::<E>(),
{
}

pub proof fn theorem_redundancy<E: Event>()
    ensures stmt_analyzer_redundancy::<E>(),
{
}

// ----- tail inclusion -----

/// `tail_included` decides inclusion of the tails for every matching candidate in the
/// domains; a counterexample is a matching pair in `left` but not `right`, of minimum history
/// length among all such pairs.
pub open spec fn stmt_analyzer_tail_inclusion<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, head: HeadView<E::Component>, left: RegexView<E::Component>,
        right: RegexView<E::Component>, v: InclusionView<E::Component>|
        #[trigger] tail_included_spec::<E>(a, head, left, right, v) ==> {
            &&& v is Holds ==> tails_included::<E>(a.domains, head, left, right)
            &&& v matches InclusionView::Counterexample(cex) ==> {
                &&& forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                    admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                    ==> in_domains::<E>(a.domains, c, h) && head_matches(head, event_view(c))
                        && lang(left, head, event_view(c), history_view(h))
                        && !lang(right, head, event_view(c), history_view(h))
                &&& shortest::<E>(a.domains, cex.history.len(), tail_fails::<E>(head, left, right))
                &&& cex_has_instance::<E>(a.domains, a.known, cex) ==> !tails_included::<E>(a.domains, head, left, right)
            }
        }
}

pub proof fn theorem_tail_inclusion<E: Event>()
    ensures stmt_analyzer_tail_inclusion::<E>(),
{
    assert forall|a: AnalyzerView<E::Component>, head: HeadView<E::Component>, left: RegexView<E::Component>,
        right: RegexView<E::Component>, v: InclusionView<E::Component>|
        #[trigger] tail_included_spec::<E>(a, head, left, right, v) implies {
            &&& v is Holds ==> tails_included::<E>(a.domains, head, left, right)
            &&& v matches InclusionView::Counterexample(cex) ==> {
                &&& forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                    admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                    ==> in_domains::<E>(a.domains, c, h) && head_matches(head, event_view(c))
                        && lang(left, head, event_view(c), history_view(h))
                        && !lang(right, head, event_view(c), history_view(h))
                &&& shortest::<E>(a.domains, cex.history.len(), tail_fails::<E>(head, left, right))
                &&& cex_has_instance::<E>(a.domains, a.known, cex) ==> !tails_included::<E>(a.domains, head, left, right)
            }
        } by {
        if let InclusionView::Counterexample(cex) = v {
            let fails = tail_fails::<E>(head, left, right);
            assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                implies in_domains::<E>(a.domains, c, h) && head_matches(head, event_view(c))
                    && lang(left, head, event_view(c), history_view(h))
                    && !lang(right, head, event_view(c), history_view(h)) by {
                assert(fails(c, h));
            }
        }
    }
}

// ----- escapes -----

/// Escapes, as the contracts state it: a query's error is never an invariant failure, and `Exhausted`
/// carries no claim (every `*_spec` is `true` on it). The remaining escape guarantees (when `Exhausted`
/// is returned, termination) are prose in the header of `history_analysis::spec::analyzer`.
pub open spec fn stmt_analyzer_escapes<E: Event>() -> bool {
    &&& forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>| #[trigger] covered_spec::<E>(a, rule, by, InclusionView::Exhausted)
    &&& forall|a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>| #[trigger] redundant_spec::<E>(a, rule, policy, InclusionView::Exhausted)
    &&& forall|a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>| #[trigger] at_least_as_strict_spec::<E>(a, p, q, InclusionView::Exhausted)
    &&& forall|a: AnalyzerView<E::Component>, head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>|
        #[trigger] tail_included_spec::<E>(a, head, left, right, InclusionView::Exhausted)
}

pub proof fn theorem_escapes<E: Event>()
    ensures stmt_analyzer_escapes::<E>(),
{
}

// ----- minimality within the split case -----

/// Every real instance `(c, h)` of a `covered` counterexample is shortest among the failing
/// pairs whose candidate has the same constant profile as `c`: no `(c2, h2)` in the domains with
/// `h2` shorter than `h` and `c2` agreeing with `c` on equality with every known constant is
/// violated by the rule and uncovered by the policy.
pub open spec fn stmt_analyzer_minimality<E: Event>() -> bool {
    forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, cex: CexView<E::Component>|
        #[trigger] covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex)) ==>
        forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>, c2: E, h2: Seq<E>|
            admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
            && #[trigger] in_domains::<E>(a.domains, c2, h2) && h2.len() < h.len()
            && same_profile(a.known, event_view(c), event_view(c2))
            ==> !(rule_violated(a.rules[rule as int], c2, h2) && !policy_denies(rules_of(a, by), c2, h2))
}

pub proof fn theorem_minimality<E: Event>()
    ensures stmt_analyzer_minimality::<E>(),
{
    assert forall|a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, cex: CexView<E::Component>|
        #[trigger] covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex)) implies
        forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>, c2: E, h2: Seq<E>|
            admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
            && #[trigger] in_domains::<E>(a.domains, c2, h2) && h2.len() < h.len()
            && same_profile(a.known, event_view(c), event_view(c2))
            ==> !(rule_violated(a.rules[rule as int], c2, h2) && !policy_denies(rules_of(a, by), c2, h2)) by {
        let fails = uncovered::<E>(rules_of(a, by), a.rules[rule as int]);
        assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>, c2: E, h2: Seq<E>|
            admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
            && #[trigger] in_domains::<E>(a.domains, c2, h2) && h2.len() < h.len()
            && same_profile(a.known, event_view(c), event_view(c2))
            implies !(rule_violated(a.rules[rule as int], c2, h2) && !policy_denies(rules_of(a, by), c2, h2)) by {
            // instance length equals the symbolic history length
            assert(history_view(h).len() == cex.history.len());
            assert(h.len() == cex.history.len());
            assert(!fails(c2, h2));
        }
    }
}

// ----- vacuity through refinement  -----

/// `never_denies` is `at_least_as_strict([], [r])`, `always_denies` is
/// `at_least_as_strict([r], [forbid head Univ])`, with the rule stored at index `f`.
pub proof fn theorem_vacuity_corollaries<E: Event>(a: AnalyzerView<E::Component>, r: nat, f: nat,
    v_never: InclusionView<E::Component>, v_always: InclusionView<E::Component>)
    requires r < a.rules.len(), f < a.rules.len(), a.rules[f as int] == forbid_all(a.rules[r as int].head),
        at_least_as_strict_spec::<E>(a, Seq::empty(), seq![r], v_never),
        at_least_as_strict_spec::<E>(a, seq![r], seq![f], v_always),
    ensures
        v_never is Holds ==> never_denies::<E>(a.domains, a.rules[r as int]),
        v_always is Holds ==> always_denies::<E>(a.domains, a.rules[r as int]),
{
    theorem_vacuity_via_refinement::<E>();
    let rule = a.rules[r as int];
    let none = Seq::<RuleView<E::Component>>::empty();
    assert(rules_of(a, Seq::<nat>::empty()) =~= none);
    assert(rules_of(a, seq![r]) =~= seq![rule]);
    assert(rules_of(a, seq![f]) =~= seq![forbid_all(rule.head)]);
    // the statement's trigger is the pair of vacuity predicates: name both so Z3 sees them together
    let never = never_denies::<E>(a.domains, rule);
    let always = always_denies::<E>(a.domains, rule);
    assert(never == refines::<E>(a.domains, none, seq![rule]) && always == refines::<E>(a.domains, seq![rule], seq![forbid_all(rule.head)]));
    if v_never is Holds {
        assert(refines::<E>(a.domains, rules_of(a, Seq::<nat>::empty()), rules_of(a, seq![r])));
    }
    if v_always is Holds {
        assert(refines::<E>(a.domains, rules_of(a, seq![r]), rules_of(a, seq![f])));
    }
}

// ----- bridge to the monitor -----

/// If `at_least_as_strict(p, q)` returned `Holds`, then whenever a validator over the rules `p`
/// grants a request inside the declared domains, a validator over `q` with the same history
/// permits it and so cannot deny it.
pub proof fn theorem_analyzer_to_monitor<E: Event, M>(
    a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>,
    vp: ValidatorView<E>, vq: ValidatorView<E>, request: Request<E, M>,
    result_p: Result<Decision<E, M>, HistoryError>, result_q: Result<Decision<E, M>, HistoryError>,
)
    requires
        at_least_as_strict_spec::<E>(a, p, q, InclusionView::Holds),
        vp.rules == rules_of(a, p), vq.rules == rules_of(a, q), vq.history == vp.history,
        in_domains::<E>(a.domains, request.event, vp.history),
        check_step(vp, request, result_p), check_step(vq, request, result_q),
        result_p is Ok && result_p->Ok_0 is Grant,
    ensures
        policy_permits(vq.rules, request.event, vq.history),
        !(result_q matches Ok(Decision::Denied(_))),
{
    assert(policy_permits(vp.rules, request.event, vp.history));
    assert(refines::<E>(a.domains, vp.rules, vq.rules));
    assert(policy_permits(vq.rules, request.event, vq.history));
    if let Ok(Decision::Denied(denial)) = result_q {
        let i = choose|i: int| #[trigger] least_violation(vq.rules, request.event, vq.history, i)
            && denial.mode == vq.rules[i].mode;
        assert(least_violation(vq.rules, request.event, vq.history, i));
        assert(rule_violated(vq.rules[i], request.event, vq.history));
        assert(policy_denies(vq.rules, request.event, vq.history));
        assert(false);
    }
}

// ----- capacity for the concrete type (u32, u64) -----

/// Capacity at an undeclared coordinate of `(u32, u64)` events: coordinate 0 offers `k` fresh
/// values whenever `known[0].len() + k <= 2^32`, coordinate 1 whenever `known[1].len() + k <= 2^64`.
pub proof fn theorem_capacity_u32_u64(domains: DomainsView<Component2<u32, u64>>, known: Seq<Set<Component2<u32, u64>>>, k: nat)
    requires hash_coherent::<Component2<u32, u64>>(), domains.len() == 2, known.len() == 2,
    ensures
        domains[0] is None && known[0].len() + k <= 0x1_0000_0000 ==> fresh_capacity::<(u32, u64)>(domains, known, 0, k),
        domains[1] is None && known[1].len() + k <= 0x1_0000_0000_0000_0000 ==> fresh_capacity::<(u32, u64)>(domains, known, 1, k),
{
    lemma_u32_u64_event_hypotheses();
    if domains[0] is None && known[0].len() + k <= 0x1_0000_0000 {
        lemma_fresh_capacity_u32::<(u32, u64)>(domains, known, 0, k, |a: u32| Component2::<u32, u64>::C0(a));
    }
    if domains[1] is None && known[1].len() + k <= 0x1_0000_0000_0000_0000 {
        lemma_fresh_capacity_u64::<(u32, u64)>(domains, known, 1, k, |b: u64| Component2::<u32, u64>::C1(b));
    }
}

// ----- exec client -----

/// `known_count` of arity-many empty sets is zero.
proof fn lemma_known_count_empty<C>(sets: Seq<Set<C>>)
    requires forall|i: int| 0 <= i < sets.len() ==> (#[trigger] sets[i]).len() == 0,
    ensures known_count(sets) == 0,
    decreases sets.len(),
{
    if sets.len() > 0 {
        lemma_known_count_empty(sets.drop_last());
    }
}

/// Exec client: `Domains::infinite()`, `new`, one `add_rule`, then the four queries, every
/// precondition discharged from the previous postconditions. Each `Ok` answer satisfies its
/// `*_spec` over the analyzer's view, with the rule at index 0.
fn analyzer_client<E: Event>(rule: &Rule<E>, head: &Head<E>, left: &RegexExpr<E>, right: &RegexExpr<E>)
    -> (result: Result<(PolicyAnalyzer<E>, Result<Inclusion<E>, HistoryError>, Result<Inclusion<E>, HistoryError>,
        Result<Inclusion<E>, HistoryError>, Result<Inclusion<E>, CompileError>), CompileError>)
    requires event_obligations::<E>(),
        arity::<E>() + regex_cost::<E>(rule.tail@) <= u32::MAX,
        known_count(known_with(declared_sets(Seq::new(arity::<E>(), |i: int| None::<Set<E::Component>>)), rule_constants(rule@)))
            + 2 * arity::<E>() + regex_cost::<E>(left@) + regex_cost::<E>(right@) <= u32::MAX,
    ensures result matches Ok((a, covered, redundant, strict, tails)) ==> {
        let v = AnalyzerView { domains: a@.domains, rules: seq![rule@], known: known_with(declared_sets(a@.domains), rule_constants(rule@)) };
        &&& a.wf()
        &&& junco_core::spec::semantics::rule_wf(rule@)
        &&& rule@.head.len() == arity::<E>()
        &&& junco_core::verify::flatten::head_coordinates_wf::<E>(rule@.head)
        &&& a@.domains == Seq::new(arity::<E>(), |i: int| None::<Set<E::Component>>)
        &&& covered matches Ok(c) ==> covered_spec::<E>(v, 0, seq![0nat], c@)
        &&& redundant matches Ok(c) ==> redundant_spec::<E>(v, 0, seq![0nat], c@)
        &&& strict matches Ok(c) ==> at_least_as_strict_spec::<E>(v, seq![0nat], seq![0nat], c@)
        &&& tails matches Ok(c) ==> tail_included_spec::<E>(a@, head@, left@, right@, c@)
        &&& no_invariant_failure(covered) && no_invariant_failure(redundant) && no_invariant_failure(strict)
        &&& covered matches Err(error) ==> junco_core::spec::semantics::resource_error(error)
        &&& redundant matches Err(error) ==> junco_core::spec::semantics::resource_error(error)
        &&& strict matches Err(error) ==> junco_core::spec::semantics::resource_error(error)
    },
{
    let domains = Domains::<E>::infinite();
    let ghost infinite = Seq::new(arity::<E>(), |i: int| None::<Set<E::Component>>);
    proof {
        assert forall|i: int| 0 <= i < infinite.len() implies (#[trigger] declared_sets(infinite)[i]).len() == 0 by {
            assert(declared_sets(infinite)[i] =~= Set::<E::Component>::empty());
        }
        lemma_known_count_empty(declared_sets(infinite));
    }
    let mut a = PolicyAnalyzer::new(domains);
    let id = a.add_rule(rule)?;
    let ids: [history_analysis::RuleId; 1] = [id];
    proof {
        id.lemma_view_is_index();
        assert(a@.rules =~= seq![rule@]);
        assert(ids@ =~= seq![id]);
        assert((seq![id] + seq![id])[0] == id);
        assert((seq![id] + seq![id])[1] == id);
        assert(ids_of(seq![id]) =~= seq![0nat]);
    }
    let covered = a.covered(id, &ids);
    let redundant = a.redundant(id, &ids);
    let strict = a.at_least_as_strict(&ids, &ids);
    let tails = a.tail_included(head, left, right);
    Ok((a, covered, redundant, strict, tails))
}

/// The client for `(u32, u64)` events under the single premise `hash_coherent`.
fn analyzer_client_u32_u64(rule: &Rule<(u32, u64)>, head: &Head<(u32, u64)>, left: &RegexExpr<(u32, u64)>, right: &RegexExpr<(u32, u64)>)
    -> (result: Result<(PolicyAnalyzer<(u32, u64)>, Result<Inclusion<(u32, u64)>, HistoryError>, Result<Inclusion<(u32, u64)>, HistoryError>,
        Result<Inclusion<(u32, u64)>, HistoryError>, Result<Inclusion<(u32, u64)>, CompileError>), CompileError>)
    requires hash_coherent::<Component2<u32, u64>>(),
        2 + regex_cost::<(u32, u64)>(rule.tail@) <= u32::MAX,
        known_count(known_with(declared_sets(Seq::new(2, |i: int| None::<Set<Component2<u32, u64>>>)), rule_constants(rule@)))
            + 4 + regex_cost::<(u32, u64)>(left@) + regex_cost::<(u32, u64)>(right@) <= u32::MAX,
    ensures result matches Ok((a, covered, redundant, strict, tails)) ==> a.wf()
        && (covered matches Ok(c) ==> covered_spec::<(u32, u64)>(
            AnalyzerView { domains: a@.domains, rules: seq![rule@], known: known_with(declared_sets(a@.domains), rule_constants(rule@)) },
            0, seq![0nat], c@)),
{
    proof { lemma_u32_u64_event_hypotheses(); }
    analyzer_client(rule, head, left, right)
}

/// Valid source rules have no input-error exit from registration.
fn resource_checked_registration<E: Event>(a: &mut PolicyAnalyzer<E>, rule: &Rule<E>)
    -> (result: Result<history_analysis::RuleId, CompileError>)
    requires old(a).wf(), analyzer_obligations::<E>(), add_rule_capacity::<E>(old(a)@, rule@),
        junco_core::spec::semantics::rule_wf(rule@), rule@.head.len() == arity::<E>(),
        junco_core::spec::semantics::rule_constants_tagged::<E>(rule@),
    ensures final(a).wf(), result is Ok || (result matches Err(CompileError::Runtime(error))
        && junco_core::spec::semantics::resource_error(error)),
{
    a.add_rule(rule)
}

/// Valid head/tail queries have no arity, coordinate, or scope-error exit.
fn resource_checked_tail_inclusion<E: Event>(
    a: &mut PolicyAnalyzer<E>, head: &Head<E>, left: &RegexExpr<E>, right: &RegexExpr<E>,
) -> (result: Result<Inclusion<E>, CompileError>)
    requires old(a).wf(), analyzer_obligations::<E>(), query_capacity::<E>(old(a)@, left@, right@),
        junco_core::spec::semantics::head_tails_wf(head@, left@, right@),
        head@.len() == arity::<E>(),
        junco_core::spec::semantics::rule_constants_tagged::<E>(Rule { mode: RuleMode::Forbid, head: *head, tail: *left }@),
        junco_core::spec::semantics::rule_constants_tagged::<E>(Rule { mode: RuleMode::Forbid, head: *head, tail: *right }@),
    ensures final(a).wf(), result is Ok || (result matches Err(CompileError::Runtime(error))
        && junco_core::spec::semantics::resource_error(error)),
{
    a.tail_included(head, left, right)
}

} // verus!

#[test]
fn compiles() {}
