//! THROWAWAY vacuity probes (audit). `neg_*` must FAIL to verify; `pos_*` must verify.
#![cfg(all(verus_keep_ghost, feature = "runtime"))]
#![allow(unused_imports)]

extern crate alloc;

use history_semantics::spec::monitor::{
    ValidatorView, check_frame, check_step, permits_result, rollback_step, trace_safe,
};
use history_semantics::validator::verify::{
    lemma_check_preserves_trace_safe, lemma_rollback_preserves_trace_safe,
};
use history_semantics::validator::{Decision, Validator};
use history_syntax::event::Component2;
use history_syntax::spec::events::*;
use history_syntax::{Event, RuleMode};
use junco_core::event::{Grant, Request};
use junco_core::spec::hypotheses::{event_obligations, hash_coherent};
use junco_core::spec::questions::{DomainsView, in_domains, refines};
use junco_core::spec::semantics::*;
use junco_core::verify::hypotheses::lemma_u32_u64_event_hypotheses;
use junco_core::HistoryError;
use vstd::prelude::*;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

pub type C = Component2<u32, u64>;
pub type E2 = (u32, u64);

pub open spec fn var(n: char) -> PatternView<C> { PatternView::Variable(seq![n]) }
pub open spec fn k0(v: u32) -> PatternView<C> { PatternView::Constant(Component2::C0(v)) }
/// forbid (7, y) . All
pub open spec fn r7() -> RuleView<C> {
    RuleView { mode: RuleMode::Forbid, head: seq![k0(7), var('y')], tail: RegexView::All }
}

// Copied verbatim from crates/history-semantics/tests/reviewer.rs (not importable across test crates).
pub enum Step<E: Event, M> {
    Check(Request<E, M>, Result<Decision<E, M>, HistoryError>),
    Rollback(Result<(), HistoryError>),
}
pub open spec fn step_ok<E: Event, M>(before: ValidatorView<E>, after: ValidatorView<E>, step: Step<E, M>) -> bool {
    match step {
        Step::Check(request, result) => check_frame(before, after, request, result)
            && check_step(before, request, result),
        Step::Rollback(result) => rollback_step(before, after, result),
    }
}
pub open spec fn run_ok<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>) -> bool {
    &&& states.len() == steps.len() + 1
    &&& states[0].history == Seq::<E>::empty()
    &&& forall|k: int| 0 <= k < steps.len() ==> step_ok(states[k], states[k + 1], #[trigger] steps[k])
}

// ===================== Probe 3: reviewer theorem premises =====================

proof fn neg_p3m_trace_safe_premises<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>, k: int)
    requires run_ok(states, steps), 0 <= k < states.len(),
    ensures false,
{
}

proof fn neg_p3m_monitor_check_premises<E: Event, M>(
    before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>,
    result: Result<Decision<E, M>, HistoryError>,
)
    requires check_frame(before, after, request, result), check_step(before, request, result),
    ensures false,
{
}

proof fn neg_p3m_analyzer_to_monitor_premises<E: Event, M>(
    domains: DomainsView<E::Component>, p: ValidatorView<E>, q: ValidatorView<E>,
    request: Request<E, M>, result_p: Result<Decision<E, M>, HistoryError>,
    result_q: Result<Decision<E, M>, HistoryError>,
)
    requires
        refines::<E>(domains, p.rules, q.rules),
        q.history == p.history,
        in_domains::<E>(domains, request.event, p.history),
        check_step(p, request, result_p), check_step(q, request, result_q),
        result_p is Ok && result_p->Ok_0 is Grant,
    ensures false,
{
}

/// Concrete 2-state run: validator over [forbid (7,y).All], Check((1,2)) granted, then
/// Check((7,0)) denied with mode Forbid. run_ok holds and the final state is trace safe.
proof fn pos_p3m_run_witness(msg: alloc::string::String) {
    let rules = seq![r7()];
    let s0 = ValidatorView::<E2> { rules, history: Seq::empty() };
    let s1 = ValidatorView::<E2> { rules, history: seq![(1u32, 2u64)] };
    let req1 = Request::<E2, ()> { event: (1u32, 2u64), metadata: () };
    let res1 = Ok::<Decision<E2, ()>, HistoryError>(Decision::Grant(Grant { event: (1u32, 2u64), metadata: () }));
    let req2 = Request::<E2, ()> { event: (7u32, 0u64), metadata: () };
    let denial = history_semantics::validator::Denial::<E2> { mode: RuleMode::Forbid, event: (7u32, 0u64), message: msg };
    let res2 = Ok::<Decision<E2, ()>, HistoryError>(Decision::Denied(denial));
    let states = seq![s0, s1, s1];
    let steps = seq![Step::Check(req1, res1), Step::Check(req2, res2)];
    // step 1: grant
    assert(!head_matches(r7().head, event_view(req1.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req1.event)[0]));
    }
    assert(policy_permits(s0.rules, req1.event, s0.history)) by {
        if policy_denies(s0.rules, req1.event, s0.history) {
            let i = choose|i: int| 0 <= i < s0.rules.len() && #[trigger] rule_violated(s0.rules[i], req1.event, s0.history);
            assert(i == 0);
        }
    }
    assert(s1.history == s0.history.push(req1.event));
    assert(step_ok(states[0], states[1], steps[0]));
    // step 2: denial
    assert(head_matches(r7().head, event_view(req2.event)));
    assert(rule_violated(s1.rules[0], req2.event, s1.history));
    assert(least_violation(s1.rules, req2.event, s1.history, 0));
    assert(step_ok(states[1], states[2], steps[1]));
    assert(run_ok(states, steps));
    assert(trace_safe(s1)) by {
        assert(s1.history.take(0) =~= Seq::<E2>::empty());
        assert(s1.history[0] == req1.event);
    }
}

// ===================== Probe 4: check_step forbids Grant on a violated rule =====================

proof fn pos_p4m_check_step_no_grant_when_violated() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: Seq::empty() };
    let req = Request::<E2, ()> { event: (7u32, 0u64), metadata: () };
    assert(head_matches(r7().head, event_view(req.event)));
    assert(rule_violated(v.rules[0], req.event, v.history));
    assert forall|r: Result<Decision<E2, ()>, HistoryError>| r matches Ok(Decision::Grant(_))
        implies !check_step(v, req, r) by {
        assert(policy_denies(v.rules, req.event, v.history));
    }
}

/// Also: Denied is rejected when no rule is violated.
proof fn pos_p4m_check_step_no_denial_when_permitted() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: Seq::empty() };
    let req = Request::<E2, ()> { event: (1u32, 0u64), metadata: () };
    assert(!head_matches(r7().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req.event)[0]));
    }
    assert forall|r: Result<Decision<E2, ()>, HistoryError>| r matches Ok(Decision::Denied(_))
        implies !check_step(v, req, r) by {
        if check_step(v, req, r) {
            let i = choose|i: int| #[trigger] least_violation(v.rules, req.event, v.history, i);
            assert(least_violation(v.rules, req.event, v.history, i));
            assert(i == 0);
        }
    }
}

/// Err is accepted by check_step in every situation except Invariant (observation, not a bug probe).
proof fn pos_p4m_check_step_err_always_allowed<E: Event, M>(v: ValidatorView<E>, req: Request<E, M>)
    ensures check_step(v, req, Err(HistoryError::GraphBudget { limit: 0 })),
{
}

/// trace_safe is not trivially true: a history containing a forbidden event is not trace safe.
proof fn pos_p4m_trace_safe_nontrivial() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: seq![(7u32, 0u64)] };
    assert(v.history.take(0) =~= Seq::<E2>::empty());
    assert(head_matches(r7().head, event_view(v.history[0])));
    assert(rule_violated(v.rules[0], v.history[0], v.history.take(0)));
    assert(!trace_safe(v));
}

// ===================== MonitorClaims request: always-Err meets check's contract =====================

// Copied verbatim from crates/history-semantics/tests/reviewer.rs.
pub open spec fn stmt_monitor_check<E: Event, M>(
    before: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>,
) -> bool {
    match result {
        Ok(Decision::Grant(grant)) => grant.event == request.event
            && forall|i: int| 0 <= i < before.rules.len()
                ==> !rule_violated(#[trigger] before.rules[i], request.event, before.history),
        Ok(Decision::Denied(denial)) => denial.event == request.event && exists|i: int|
            0 <= i < before.rules.len()
            && rule_violated(#[trigger] before.rules[i], request.event, before.history)
            && denial.mode == before.rules[i].mode
            && forall|j: int| 0 <= j < i ==> !rule_violated(#[trigger] before.rules[j], request.event, before.history),
        Err(error) => !(error is Invariant),
    }
}

proof fn pos_mc1_always_error_satisfies_contract<E: Event, M>(before: ValidatorView<E>, request: Request<E, M>)
    ensures check_frame(before, before, request, Err(HistoryError::AllocationFailed)),
        check_step(before, request, Err(HistoryError::AllocationFailed)),
        stmt_monitor_check(before, request, Err(HistoryError::AllocationFailed)),
{}

// ===================== Probe 2 (semantics side) =====================

proof fn neg_p2m_hash_coherent_u32_u64()
    requires hash_coherent::<C>(),
    ensures false,
{
    lemma_u32_u64_event_hypotheses();
}

} // verus!

#[test]
fn compiles() {}
