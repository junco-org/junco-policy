//! THROWAWAY vacuity probes (audit). `neg_*` must FAIL to verify; `pos_*` must verify.
#![cfg(all(verus_keep_ghost, feature = "runtime"))]
#![allow(unused_imports)]

extern crate alloc;

use history_analysis::spec::analyzer::*;
use history_analysis::verify::analyzer_obligations;
use history_analysis::verify::key_axioms::*;
use history_semantics::spec::monitor::{ValidatorView, check_step};
use history_semantics::validator::Decision;
use history_syntax::event::{Component2, Component3};
use history_syntax::spec::events::*;
use history_syntax::{Event, RuleMode};
use junco_core::event::{Grant, Request};
use junco_core::kernel::{RegexId, TestId};
use junco_core::spec::hypotheses::*;
use junco_core::spec::questions::*;
use junco_core::spec::semantics::*;
use junco_core::verify::hypotheses::*;
use junco_core::HistoryError;
use smallvec::SmallVec;
use vstd::prelude::*;
use history_syntax::event::specs::EventSpec;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::array::group_array_axioms, vstd::slice::group_slice_axioms};

pub type C = Component2<u32, u64>;
pub type E2 = (u32, u64);

pub open spec fn var(n: char) -> PatternView<C> { PatternView::Variable(seq![n]) }
pub open spec fn k0(v: u32) -> PatternView<C> { PatternView::Constant(Component2::C0(v)) }
pub open spec fn k1(v: u64) -> PatternView<C> { PatternView::Constant(Component2::C1(v)) }
pub open spec fn forbid(head: HeadView<C>, tail: RegexView<C>) -> RuleView<C> {
    RuleView { mode: RuleMode::Forbid, head, tail }
}
pub open spec fn inf2() -> DomainsView<C> { seq![None::<Set<C>>, None::<Set<C>>] }
pub open spec fn none_known() -> Seq<Set<C>> { seq![Set::<C>::empty(), Set::<C>::empty()] }
pub open spec fn av(rules: Seq<RuleView<C>>) -> AnalyzerView<C> {
    AnalyzerView { domains: inf2(), rules, known: none_known() }
}
/// forbid (x, y) . All : violated by every candidate.
pub open spec fn r_all() -> RuleView<C> { forbid(seq![var('x'), var('y')], RegexView::All) }
/// forbid (7, y) . All
pub open spec fn r7() -> RuleView<C> { forbid(seq![k0(7), var('y')], RegexView::All) }
/// forbid (x, 9) . All
pub open spec fn r9() -> RuleView<C> { forbid(seq![var('x'), k1(9)], RegexView::All) }
pub open spec fn cc(a: u32, b: u64) -> ComponentsView<C> {
    seq![ValueView::Constant(Component2::C0(a)), ValueView::Constant(Component2::C1(b))]
}
pub open spec fn any_f() -> FreshChoice<C> {
    seq![|n: nat| Component2::<u32, u64>::C0(0u32), |n: nat| Component2::<u32, u64>::C1(0u64)]
}

proof fn lemma_in_domains(c: E2, h: Seq<E2>)
    ensures in_domains::<E2>(inf2(), c, h),
{
    assert(event_view(c).len() == 2);
    assert forall|i: int| 0 <= i < history_view(h).len() implies #[trigger] event_in(inf2(), history_view(h)[i]) by {
        assert(history_view(h)[i] == event_view(h[i]));
    }
}

proof fn lemma_constant_cex_admissible(cex: CexView<C>, known: Seq<Set<C>>)
    requires known.len() == 2, cex_arity(cex, 2),
        forall|i: int| 0 <= i < 2 ==> #[trigger] cex.candidate[i] is Constant,
        forall|j: int, i: int| 0 <= j < cex.history.len() && 0 <= i < 2 ==> #[trigger] cex.history[j][i] is Constant,
    ensures admissible::<E2>(inf2(), known, cex, any_f()),
{
    assert forall|i: int| 0 <= i < 2 implies choice_ok::<E2>(#[trigger] any_f()[i], fresh_used(cex, i), known[i], inf2()[i], i) by {
        assert forall|n: nat| !fresh_used(cex, i).contains(n) by {
            if fresh_used(cex, i).contains(n) {
                if exists|j: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
                    && #[trigger] cex.history[j][i] == ValueView::<C>::Fresh(n) {
                    let j = choose|j: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
                        && #[trigger] cex.history[j][i] == ValueView::<C>::Fresh(n);
                    assert(cex.history[j][i] is Constant);
                } else {
                    assert(cex.candidate[i] is Constant);
                }
            }
        }
    }
}

// ===================== Probe 1: axiom consistency =====================

proof fn neg_p1_key_axioms_consistent()
    ensures false,
{
    broadcast use {group_internal_key_axioms, junco_core::kernel::verify::group_kernel_views,
        vstd::set::group_set_lemmas, vstd::std_specs::vec::group_vec_axioms,
        vstd::laws_cmp::group_laws_cmp, vstd::laws_eq::group_laws_eq,
        vstd::std_specs::hash::group_hash_axioms};
    assert(hash_coherent::<(RegexId, RegexId)>());
    assert(hash_coherent::<(TestId, TestId)>());
    assert(hash_coherent::<SmallVec<[RegexId; 4]>>());
    assert(<SmallVec<[RegexId; 4]> as PartialEqSpec>::obeys_eq_spec());
    let a = arbitrary::<SmallVec<[RegexId; 4]>>();
    assert(a.eq_spec(&a));
}

proof fn neg_p1b_key_axioms_with_u32_u64_hypotheses()
    requires hash_coherent::<C>(),
    ensures false,
{
    broadcast use {group_internal_key_axioms, junco_core::kernel::verify::group_kernel_views,
        vstd::set::group_set_lemmas, vstd::std_specs::vec::group_vec_axioms,
        vstd::laws_cmp::group_laws_cmp, vstd::laws_eq::group_laws_eq,
        vstd::std_specs::hash::group_hash_axioms};
    lemma_u32_u64_event_hypotheses();
    assert(event_obligations::<E2>());
    assert(<SmallVec<[RegexId; 4]> as PartialEqSpec>::obeys_eq_spec());
}

/// Positive: exec `==` on SmallVec follows the axiom (two empty vectors are equal).
fn pos_p1c_smallvec_eq_exec() {
    broadcast use group_internal_key_axioms;
    let a: SmallVec<[RegexId; 4]> = SmallVec::new();
    let b: SmallVec<[RegexId; 4]> = SmallVec::new();
    let e = a == b;
    assert(e);
}

fn neg_p1d_smallvec_eq_exec()
    ensures false,
{
    broadcast use group_internal_key_axioms;
    let a: SmallVec<[RegexId; 4]> = SmallVec::new();
    let b: SmallVec<[RegexId; 4]> = SmallVec::new();
    let e = a == b;
    assert(e);
}

// ===================== Probe 2: hypotheses satisfiable =====================

proof fn neg_p2a_hash_coherent_u32_u64()
    requires hash_coherent::<C>(),
    ensures false,
{
    lemma_u32_u64_event_hypotheses();
    assert(event_obligations::<E2>());
    assert(analyzer_obligations::<E2>());
    assert(views_surjective::<E2>());
}

proof fn neg_p2b_event_obligations_u32_u64()
    requires event_obligations::<E2>(),
    ensures false,
{
    let xs = seq![Component2::<u32, u64>::C0(1u32), Component2::<u32, u64>::C1(2u64)];
    assert(well_tagged::<E2>(xs));
}

proof fn neg_p2c_analyzer_obligations_u32_u64()
    requires analyzer_obligations::<E2>(),
    ensures false,
{
}

proof fn neg_p2d_event_obligations_generic<E: Event>()
    requires event_obligations::<E>(),
    ensures false,
{
}

proof fn neg_p2e_all_concrete_witnesses()
    requires hash_coherent::<C>(), hash_coherent::<Component3<u8, u8, u8>>(),
        hash_coherent::<Component3<u32, u8, bool>>(),
    ensures false,
{
    broadcast use group_internal_key_axioms;
    lemma_u32_u64_event_hypotheses();
    lemma_u8_triple_event_hypotheses();
    lemma_u32_mixed_event_hypotheses();
}

// ===================== Probe 3: reviewer theorem premises satisfiable =====================

/// theorem_analyzer_to_monitor (analysis/tests/reviewer.rs): premises => false must fail.
proof fn neg_p3a_analyzer_to_monitor_premises<E: Event, M>(
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
    ensures false,
{
}

/// Concrete witness for every premise of theorem_analyzer_to_monitor, with nontrivial rules:
/// a.rules = [forbid (7,y).All, forbid (x,9).All], p = [0,1], q = [0], request (1,2) granted by both.
proof fn pos_p3b_analyzer_to_monitor_witness() {
    let a = av(seq![r7(), r9()]);
    let p = seq![0nat, 1nat];
    let q = seq![0nat];
    let req = Request::<E2, ()> { event: (1u32, 2u64), metadata: () };
    let g = Decision::<E2, ()>::Grant(Grant { event: (1u32, 2u64), metadata: () });
    let result_p = Ok::<Decision<E2, ()>, HistoryError>(g);
    let result_q = Ok::<Decision<E2, ()>, HistoryError>(g);
    let vp = ValidatorView::<E2> { rules: rules_of(a, p), history: Seq::empty() };
    let vq = ValidatorView::<E2> { rules: rules_of(a, q), history: Seq::empty() };
    assert(rules_of(a, p) =~= seq![r7(), r9()]);
    assert(rules_of(a, q) =~= seq![r7()]);
    assert(refines::<E2>(a.domains, rules_of(a, p), rules_of(a, q))) by {
        assert forall|c: E2, h: Seq<E2>| in_domains::<E2>(a.domains, c, h) && policy_permits(rules_of(a, p), c, h)
            implies #[trigger] policy_permits(rules_of(a, q), c, h) by {
            if policy_denies(rules_of(a, q), c, h) {
                let i = choose|i: int| 0 <= i < rules_of(a, q).len() && #[trigger] rule_violated(rules_of(a, q)[i], c, h);
                assert(i == 0);
                assert(rule_violated(rules_of(a, p)[0], c, h));
            }
        }
    }
    assert(at_least_as_strict_spec::<E2>(a, p, q, InclusionView::Holds));
    lemma_in_domains((1u32, 2u64), Seq::empty());
    assert(in_domains::<E2>(a.domains, req.event, vp.history));
    // (1,2) matches neither head
    assert(!head_matches(r7().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req.event)[0]));
    }
    assert(!head_matches(r9().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r9().head[1], event_view(req.event)[1]));
    }
    assert(policy_permits(vp.rules, req.event, vp.history)) by {
        if policy_denies(vp.rules, req.event, vp.history) {
            let i = choose|i: int| 0 <= i < vp.rules.len() && #[trigger] rule_violated(vp.rules[i], req.event, vp.history);
            assert(i == 0 || i == 1);
        }
    }
    assert(policy_permits(vq.rules, req.event, vq.history)) by {
        if policy_denies(vq.rules, req.event, vq.history) {
            let i = choose|i: int| 0 <= i < vq.rules.len() && #[trigger] rule_violated(vq.rules[i], req.event, vq.history);
            assert(i == 0);
        }
    }
    assert(check_step(vp, req, result_p));
    assert(check_step(vq, req, result_q));
    assert(result_p is Ok && result_p->Ok_0 is Grant);
}

/// Witness: covered_spec Holds (rule forbid (x,y).All covered by itself).
proof fn pos_p3c_covered_holds_witness() {
    let a = av(seq![r_all()]);
    assert(rules_of(a, seq![0nat]) =~= seq![r_all()]);
    assert forall|c: E2, h: Seq<E2>| in_domains::<E2>(a.domains, c, h) && #[trigger] rule_violated(a.rules[0], c, h)
        implies policy_denies(rules_of(a, seq![0nat]), c, h) by {
        assert(rule_violated(rules_of(a, seq![0nat])[0], c, h));
    }
    assert(covered_spec::<E2>(a, 0, seq![0nat], InclusionView::Holds));
}

/// Witness: covered_spec Counterexample (A1/A2/A6 premise) for forbid (x,y).All by the empty
/// policy, cex = ((C0 1, C1 1), []).
proof fn pos_p3d_covered_counterexample_witness() {
    let a = av(seq![r_all()]);
    let by = Seq::<nat>::empty();
    let cex = CexView { candidate: cc(1, 1), history: Seq::<ComponentsView<C>>::empty() };
    let p = rules_of(a, by);
    assert(p =~= Seq::<RuleView<C>>::empty());
    let r = a.rules[0];
    let fails = uncovered::<E2>(p, r);
    lemma_constant_cex_admissible(cex, a.known);
    let c = (1u32, 1u64);
    let h = Seq::<E2>::empty();
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    assert(cex_has_instance::<E2>(a.domains, a.known, cex));
    assert(head_matches(r.head, event_view(c)));
    assert(rule_violated(r, c, h));
    lemma_in_domains(c, h);
    assert(!covers::<E2>(a.domains, p, r));
    assert forall|f: FreshChoice<C>, c2: E2, h2: Seq<E2>|
        admissible::<E2>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E2>(cex, f, c2, h2)
        implies in_domains::<E2>(a.domains, c2, h2) && fails(c2, h2) by {
        lemma_in_domains(c2, h2);
        assert(head_matches(r.head, event_view(c2)));
        assert(rule_violated(r, c2, h2));
    }
    assert(every_instance::<E2>(a.domains, a.known, cex, fails));
    assert(counterexample_spec::<E2>(a, cex, fails));
    assert(minimal_in_case::<E2>(a.domains, a.known, cex, fails));
    assert(covered_spec::<E2>(a, 0, by, InclusionView::Counterexample(cex)));
}

/// Witness: theorem_vacuity_corollaries premises with v_always = Holds.
proof fn pos_p3e_vacuity_corollaries_witness() {
    let a = av(seq![r7(), forbid_all(r7().head)]);
    assert(a.rules[1] == forbid_all(a.rules[0].head));
    assert(at_least_as_strict_spec::<E2>(a, Seq::empty(), seq![0nat], InclusionView::Exhausted));
    assert(rules_of(a, seq![0nat]) =~= seq![r7()]);
    assert(rules_of(a, seq![1nat]) =~= seq![r7()]);
    assert(at_least_as_strict_spec::<E2>(a, seq![0nat], seq![1nat], InclusionView::Holds));
}

// ===================== Probe 4: spec non-triviality =====================

/// A4 Holds is false when inclusion fails: head (5, y), left = All, right = Empty.
proof fn pos_p4a_tail_holds_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(head, event_view(c)));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!lang(RegexView::<C>::Empty, head, event_view(c), history_view(h)));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::Empty, InclusionView::Holds));
}

proof fn neg_p4a_tail_holds_accepted()
    ensures tail_included_spec::<E2>(av(Seq::empty()), seq![k0(5), var('y')], RegexView::All, RegexView::Empty, InclusionView::Holds),
{
}

/// A4 Counterexample is false when inclusion holds (right = All): a bogus cex is rejected.
proof fn pos_p4b_tail_bogus_cex_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let cex = CexView { candidate: cc(5, 0), history: Seq::<ComponentsView<C>>::empty() };
    lemma_constant_cex_admissible(cex, a.known);
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::All, InclusionView::Counterexample(cex)));
}

/// A4 minimality is real: a cex of history length 1 is rejected when a length-0 failure exists.
proof fn pos_p4c_tail_nonshortest_cex_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let cex = CexView { candidate: cc(5, 0), history: seq![cc(5, 0)] };
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(head, event_view(c)));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!lang(RegexView::<C>::Empty, head, event_view(c), history_view(h)));
    assert(tail_fails::<E2>(head, RegexView::All, RegexView::Empty)(c, h));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::Empty, InclusionView::Counterexample(cex)));
}

/// A1 Holds is false when the rule is not covered (empty policy, forbid (5,y).All).
proof fn pos_p4d_covered_holds_rejected() {
    let r = forbid(seq![k0(5), var('y')], RegexView::All);
    let a = av(seq![r]);
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(r.head, event_view(c)));
    assert(rule_violated(a.rules[0], c, h));
    assert(rules_of(a, Seq::<nat>::empty()) =~= Seq::<RuleView<C>>::empty());
    assert(!covered_spec::<E2>(a, 0, Seq::empty(), InclusionView::Holds));
}

/// A6 minimality is real: a covered cex of history length 1 is rejected when the same
/// candidate already fails with the empty history.
proof fn pos_p4e_covered_nonminimal_cex_rejected() {
    let a = av(seq![r_all()]);
    let by = Seq::<nat>::empty();
    let cex = CexView { candidate: cc(1, 1), history: seq![cc(1, 1)] };
    let p = rules_of(a, by);
    assert(p =~= Seq::<RuleView<C>>::empty());
    lemma_constant_cex_admissible(cex, a.known);
    let c = (1u32, 1u64);
    let h = seq![(1u32, 1u64)];
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    let h0 = Seq::<E2>::empty();
    lemma_in_domains(c, h0);
    assert(same_profile(a.known, event_view(c), event_view(c)));
    assert(head_matches(a.rules[0].head, event_view(c)));
    assert(rule_violated(a.rules[0], c, h0));
    assert(uncovered::<E2>(p, a.rules[0])(c, h0));
    assert(!shortest_in_case::<E2>(a.domains, a.known, c, 1, uncovered::<E2>(p, a.rules[0])));
    assert(!covered_spec::<E2>(a, 0, by, InclusionView::Counterexample(cex)));
}

/// A3 Holds is false when refinement fails: [] does not refine [forbid (x,y).All].
proof fn pos_p4f_strict_holds_rejected() {
    let a = av(seq![r_all()]);
    let c = (1u32, 1u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(rules_of(a, Seq::<nat>::empty()) =~= Seq::<RuleView<C>>::empty());
    assert(rules_of(a, seq![0nat]) =~= seq![r_all()]);
    assert(head_matches(r_all().head, event_view(c)));
    assert(rule_violated(rules_of(a, seq![0nat])[0], c, h));
    assert(policy_permits(rules_of(a, Seq::<nat>::empty()), c, h));
    assert(policy_denies(rules_of(a, seq![0nat]), c, h));
    assert(!policy_permits(rules_of(a, seq![0nat]), c, h));
    assert(!refines::<E2>(a.domains, rules_of(a, Seq::<nat>::empty()), rules_of(a, seq![0nat])));
    assert(!at_least_as_strict_spec::<E2>(a, Seq::empty(), seq![0nat], InclusionView::Holds));
}

// ===================== AnalyzerClaims request: junk cex at a declared coordinate =====================

pub open spec fn junk_cex<E: Event>() -> CexView<E::Component> {
    CexView::<E::Component> { candidate: Seq::new(arity::<E>(), |i: int| ValueView::<E::Component>::Fresh(0)), history: Seq::empty() }
}

/// POS (should verify if the claim holds): with domains[0] = {x} and x known, the all-Fresh(0)
/// counterexample has no admissible instance and no capacity, so it satisfies the
/// Counterexample arms of covered_spec and tail_included_spec for ANY rule/policy/tails.
proof fn pos_ac1_junk_cex_declared<E: Event>(a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>,
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>, x: E::Component)
    requires junco_core::spec::hypotheses::eq_equivalence::<E::Component>(), arity::<E>() >= 1,
        a.domains.len() == arity::<E>(), a.known.len() == arity::<E>(),
        a.domains[0] == Some(Set::<E::Component>::empty().insert(x)), a.known[0].contains(x),
    ensures ({ let cex = junk_cex::<E>();
        covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex))
        && tail_included_spec::<E>(a, head, left, right, InclusionView::Counterexample(cex))
        && !cex_has_instance::<E>(a.domains, a.known, cex) && !capacity_for::<E>(a.domains, a.known, cex) }),
{
    broadcast use {vstd::iset::group_iset_lemmas, vstd::set::group_set_lemmas};
    let cex = junk_cex::<E>();
    assert(cex.candidate[0] == ValueView::<E::Component>::Fresh(0));
    assert(fresh_used(cex, 0).contains(0nat));
    assert(fresh_used(cex, 0) =~= ISet::<nat>::empty().insert(0nat));
    assert(fresh_used(cex, 0).len() == 1);
    // no admissible choice
    assert forall|f: FreshChoice<E::Component>| !admissible::<E>(a.domains, a.known, cex, f) by {
        if admissible::<E>(a.domains, a.known, cex, f) {
            assert(choice_ok::<E>(f[0], fresh_used(cex, 0), a.known[0], a.domains[0], 0));
            assert(in_domain(a.domains[0], f[0](0nat)));
            let w = choose|w: E::Component| Set::<E::Component>::empty().insert(x).contains(w) && f[0](0nat).eq_spec(&w);
            assert(w == x);
            assert(!f[0](0nat).eq_spec(&x));
        }
    }
    assert(!cex_has_instance::<E>(a.domains, a.known, cex));
    // no capacity at coordinate 0
    assert(!fresh_capacity::<E>(a.domains, a.known, 0, 1)) by {
        if fresh_capacity::<E>(a.domains, a.known, 0, 1) {
            let vs = choose|vs: Seq<E::Component>| #[trigger] vs.len() == 1
                && (forall|i: int, j: int| 0 <= i < j < vs.len() ==> !vs[i].eq_spec(&vs[j]))
                && forall|i: int| 0 <= i < vs.len() ==> E::coordinate_spec(#[trigger] vs[i]) == 0
                    && in_domain(a.domains[0], vs[i]) && misses(a.known[0], vs[i]);
            assert(in_domain(a.domains[0], vs[0]));
            let w = choose|w: E::Component| Set::<E::Component>::empty().insert(x).contains(w) && vs[0].eq_spec(&w);
            assert(w == x);
            assert(misses(a.known[0], vs[0]));
        }
    }
    assert(!capacity_for::<E>(a.domains, a.known, cex));
    assert(cex_arity(cex, arity::<E>()));
}

/// POS bonus: simultaneously the rule IS covered (by == [rule]), yet the Counterexample arm holds.
proof fn pos_ac2_junk_cex_for_covered_rule<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>, x: E::Component)
    requires junco_core::spec::hypotheses::eq_equivalence::<E::Component>(), arity::<E>() >= 1,
        a.domains.len() == arity::<E>(), a.known.len() == arity::<E>(),
        a.domains[0] == Some(Set::<E::Component>::empty().insert(x)), a.known[0].contains(x),
        rule < a.rules.len(),
    ensures
        covers::<E>(a.domains, rules_of(a, seq![rule]), a.rules[rule as int]),
        covered_spec::<E>(a, rule, seq![rule], InclusionView::Counterexample(junk_cex::<E>())),
{
    pos_ac1_junk_cex_declared::<E>(a, rule, seq![rule], head, left, right, x);
    assert(rules_of(a, seq![rule]) =~= seq![a.rules[rule as int]]);
    assert forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h) && #[trigger] rule_violated(a.rules[rule as int], c, h)
        implies policy_denies(rules_of(a, seq![rule]), c, h) by {
        assert(rule_violated(rules_of(a, seq![rule])[0], c, h));
    }
}

/// POS: the premises of pos_ac2 are satisfiable for (u32, u64) with domains [Some({C0 3}), None]
/// and the analyzer view `new`/`add_rule` would produce (known[0] = declared set).
proof fn pos_ac3_junk_cex_concrete()
    requires hash_coherent::<C>(),
{
    lemma_u32_u64_event_hypotheses();
    let x = Component2::<u32, u64>::C0(3u32);
    let a = AnalyzerView::<C> { domains: seq![Some(Set::<C>::empty().insert(x)), None::<Set<C>>],
        rules: seq![r_all()], known: seq![Set::<C>::empty().insert(x), Set::<C>::empty()] };
    assert(a.known[0].contains(x));
    pos_ac2_junk_cex_for_covered_rule::<E2>(a, 0, r_all().head, RegexView::All, RegexView::All, x);
    assert(covers::<E2>(a.domains, rules_of(a, seq![0nat]), a.rules[0]));
    assert(covered_spec::<E2>(a, 0, seq![0nat], InclusionView::Counterexample(junk_cex::<E2>())));
}

// ===================== TrustHypotheses request P2: hash_coherent neither provable nor refutable =====================

proof fn neg_th2_hash_coherent_provable()
    ensures hash_coherent::<C>(),
{
    broadcast use group_internal_key_axioms;
}

proof fn neg_th2_hash_coherent_refutable()
    ensures !hash_coherent::<C>(),
{
    broadcast use group_internal_key_axioms;
}

} // verus!

#[test]
fn compiles() {}
