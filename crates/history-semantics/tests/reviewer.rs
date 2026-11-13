//! Reviewer theorems for the monitor (R5, Theorem `thm:matcher` at the level of `Validator`).
//!
//! Every statement here uses only public items: R1–R5, `Validator` and `Store`. The generic
//! theorems take R4's `event_obligations::<E>()`; the concrete `(u32, u64)` instances take only
//! `hash_coherent::<Component2<u32, u64>>()` (TRUST.md: the single uninterpreted hashing
//! hypothesis; `junco_core::verify::hypotheses` proves every other conjunct).
#![cfg(all(verus_keep_ghost, feature = "runtime"))]

extern crate alloc;

use alloc::sync::Arc;
use history_semantics::spec::monitor::{
    ValidatorView, check_frame, check_step, permits_result, rollback_step, trace_safe,
};
use history_semantics::validator::verify::{
    lemma_check_preserves_trace_safe, lemma_rollback_preserves_trace_safe,
};
use history_semantics::validator::{Decision, Validator};
use history_store::typed::Store;
use history_syntax::event::Component2;
use history_syntax::spec::events::event_view;
use history_syntax::{Event, Head, RegexExpr, Rule, RuleMode};
use junco_core::event::Request;
use junco_core::spec::hypotheses::{event_obligations, hash_coherent};
use junco_core::spec::questions::{DomainsView, in_domains, refines};
use junco_core::spec::semantics::{
    head_matches, least_violation, policy_denies, policy_permits, rule_violated,
};
use junco_core::verify::hypotheses::lemma_u32_u64_event_hypotheses;
use junco_core::{CompileError, HistoryError};
use vstd::prelude::*;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ----- thm:matcher at the monitor level -----

/// The three readable cases of `check_step` (R5): a grant means no rule is violated; a denial
/// names the first violated rule, in source order, by index and mode; errors are never invariant
/// failure. Spelled out with R2's `rule_violated` so a reader needs no further unfolding.
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
            && i == denial.index as int
            && forall|j: int| 0 <= j < i ==> !rule_violated(#[trigger] before.rules[j], request.event, before.history),
        Err(error) => !(error is Invariant),
    }
}

/// `thm:matcher` for `Validator::check`: the contract's `check_step` and `check_frame` give the
/// readable statement.
pub proof fn theorem_monitor_check<E: Event, M>(
    before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>,
    result: Result<Decision<E, M>, HistoryError>,
)
    requires check_frame(before, after, request, result), check_step(before, request, result),
    ensures stmt_monitor_check(before, request, result),
{
    match result {
        Ok(Decision::Grant(_)) => {
            assert forall|i: int| 0 <= i < before.rules.len()
                implies !rule_violated(#[trigger] before.rules[i], request.event, before.history) by {
                if rule_violated(before.rules[i], request.event, before.history) {
                    assert(policy_denies(before.rules, request.event, before.history));
                }
            }
        },
        Ok(Decision::Denied(denial)) => {
            let i = denial.index as int;
            assert(rule_violated(before.rules[i], request.event, before.history));
        },
        Err(_) => {},
    }
}

/// `permits` answers exactly whether every rule accepts the candidate after the committed history.
pub proof fn theorem_monitor_permits<E: Event>(
    v: ValidatorView<E>, candidate: E, result: Result<bool, HistoryError>,
)
    requires permits_result(v, candidate, result),
    ensures result matches Ok(permitted) ==> permitted == forall|i: int| 0 <= i < v.rules.len()
        ==> !rule_violated(#[trigger] v.rules[i], candidate, v.history),
{
    if let Ok(permitted) = result {
        if permitted {
            assert forall|i: int| 0 <= i < v.rules.len()
                implies !rule_violated(#[trigger] v.rules[i], candidate, v.history) by {
                if rule_violated(v.rules[i], candidate, v.history) {
                    assert(policy_denies(v.rules, candidate, v.history));
                }
            }
        }
    }
}

// ----- trace safety of every reachable state -----

/// One observable step of a `Validator`: a `check` with its result, or a `rollback` with its result.
pub enum Step<E: Event, M> {
    Check(Request<E, M>, Result<Decision<E, M>, HistoryError>),
    Rollback(Result<(), HistoryError>),
}

/// What `Validator::check`/`rollback` guarantee about one step (their contracts, under
/// `event_obligations::<E>()` for `check_step`).
pub open spec fn step_ok<E: Event, M>(before: ValidatorView<E>, after: ValidatorView<E>, step: Step<E, M>) -> bool {
    match step {
        Step::Check(request, result) => check_frame(before, after, request, result)
            && check_step(before, request, result),
        Step::Rollback(result) => rollback_step(before, after, result),
    }
}

/// A run: `states[0]` is a freshly finished validator (empty history) and every step is one
/// `check` or `rollback`.
pub open spec fn run_ok<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>) -> bool {
    &&& states.len() == steps.len() + 1
    &&& states[0].history == Seq::<E>::empty()
    &&& forall|k: int| 0 <= k < steps.len() ==> step_ok(states[k], states[k + 1], #[trigger] steps[k])
}

/// Every state of a run is trace safe: each committed event was permitted by every rule against
/// the history before it. Induction over the run, using the two preservation lemmas.
pub proof fn theorem_trace_safe<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>, k: int)
    requires run_ok(states, steps), 0 <= k < states.len(),
    ensures trace_safe(states[k]),
    decreases k,
{
    if k == 0 {
        assert(states[0].history.len() == 0);
    } else {
        theorem_trace_safe(states, steps, k - 1);
        match steps[k - 1] {
            Step::Check(request, result) => lemma_check_preserves_trace_safe(states[k - 1], states[k], request, result),
            Step::Rollback(result) => lemma_rollback_preserves_trace_safe(states[k - 1], states[k], result),
        }
    }
}

// ----- analyzer-to-monitor bridge (S9), stated with R3 `refines` -----

/// If `p` refines `q` on the declared domains (`at_least_as_strict(p, q)` returned `Holds`, R6),
/// then whenever a validator over `p` grants a request inside the domains, the validator over `q`
/// with the same history permits it, so it cannot deny it.
pub proof fn theorem_analyzer_to_monitor<E: Event, M>(
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
    ensures
        policy_permits(q.rules, request.event, q.history),
        !(result_q matches Ok(Decision::Denied(_))),
{
    assert(policy_permits(p.rules, request.event, p.history));
    if let Ok(Decision::Denied(denial)) = result_q {
        let i = choose|i: int| #[trigger] least_violation(q.rules, request.event, q.history, i)
            && denial.mode == q.rules[i].mode;
        assert(policy_denies(q.rules, request.event, q.history));
    }
}

// ----- the concrete event type (u32, u64) -----

/// `(u32, u64)` events satisfy every hypothesis once `hash_coherent` of their component type is
/// assumed (the only premise; TRUST.md).
pub proof fn theorem_event_obligations_u32_u64()
    requires hash_coherent::<Component2<u32, u64>>(),
    ensures event_obligations::<(u32, u64)>(),
{
    lemma_u32_u64_event_hypotheses();
}

/// Exec client: builds a validator with one rule over `head` and checks one request; the result
/// satisfies `thm:matcher` and the state is trace safe, discharged from the public contracts only.
fn monitor_client<E: Event, M>(head: Head<E>, request: Request<E, M>)
    -> (result: Result<(Validator<E>, Result<Decision<E, M>, HistoryError>), CompileError>)
    requires event_obligations::<E>(),
    ensures result matches Ok((state, answer)) ==> {
        let before = ValidatorView { rules: state@.rules, history: Seq::<E>::empty() };
        &&& state.wf()
        &&& state@.rules == seq![Rule { mode: RuleMode::Forbid, head, tail: RegexExpr::All }@]
        &&& junco_core::spec::semantics::rule_wf(state@.rules[0])
        &&& head@.len() == history_syntax::spec::events::arity::<E>()
        &&& junco_core::verify::flatten::head_coordinates_wf::<E>(head@)
        &&& check_frame(before, state@, request, answer)
        &&& stmt_monitor_check(before, request, answer)
        &&& trace_safe(state@)
        &&& head_matches(head@, event_view(request.event)) ==> !(answer matches Ok(Decision::Grant(_)))
    },
{
    let store = Arc::new(Store::<E>::new()?);
    let mut builder = Validator::builder(store);
    let rule = Rule::new(RuleMode::Forbid, head, RegexExpr::All);
    let ghost source = rule;
    builder.add_rule(rule)?;
    proof { assert(builder.rules() =~= seq![source@]); }
    let mut state = builder.finish()?;
    let ghost before = state@;
    let answer = state.check(request);
    proof {
        theorem_monitor_check(before, state@, request, answer);
        assert(trace_safe(before));
        lemma_check_preserves_trace_safe(before, state@, request, answer);
        if head_matches(head@, event_view(request.event)) {
            assert(rule_violated(before.rules[0], request.event, before.history));
        }
    }
    Ok((state, answer))
}

/// The same client for `(u32, u64)` events under the single premise `hash_coherent`.
fn monitor_client_u32_u64<M>(head: Head<(u32, u64)>, request: Request<(u32, u64), M>)
    -> (result: Result<(Validator<(u32, u64)>, Result<Decision<(u32, u64), M>, HistoryError>), CompileError>)
    requires hash_coherent::<Component2<u32, u64>>(),
    ensures result matches Ok((state, answer)) ==> state.wf()
        && stmt_monitor_check(ValidatorView { rules: state@.rules, history: Seq::<(u32, u64)>::empty() }, request, answer)
        && trace_safe(state@),
{
    proof { theorem_event_obligations_u32_u64(); }
    monitor_client(head, request)
}

} // verus!

#[test]
fn compiles() {}
