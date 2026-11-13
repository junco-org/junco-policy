//! Owned DSL → finite component books → retained numeric runtime composition.
//!
//! The public constructor and decision bodies supply the structural flattening,
//! finite published snapshots, history correspondence, and cached numeric answer.
//! Native Eq/Hash/projection remain conditional; retained provenance follows lifecycle resources.
//! Ordered Vec construction, first-source denial, callback pairing, and validator
//! append/no-append transactions are exercised by actual checked API clients below.

use crate::compile::verify as numeric;
use crate::compiled_rule::CompiledRule;
use crate::compiled_rule::verify as typed;
use crate::policy::evaluate::{policy_storage_result, verify as policy};
use crate::policy::rule::verify::{policy_rule_diagnostic, policy_rule_source};
use crate::policy::{CompiledPolicy, PolicyDecision, PolicyRule};
use crate::runtime::{RuleRuntime, verify as cache};
use crate::spec::monitor;
use crate::validator::{Decision, Validator, verify as validator};
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_store::history::{History, verify as raw};
use history_store::typed::{Store, borrow_store, share_store, verify as books};
use history_syntax::Event;
use history_syntax::syntax::Rule;
use history_syntax::{Head, RegexExpr, RuleMode};
use junco_core::error::{CompileError, HistoryError};
use junco_core::event::Request;
use junco_core::flat::FlatPair;
use junco_core::kernel::verify as graph;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::spec::semantics;
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use {junco_core::kernel::verify::group_kernel_views,
    vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// The numeric constructor's property is preserved by successful and failed batches.
pub(crate) open spec fn runtime_represents(template: FlatPair<u64>, runtime: RuleRuntime) -> bool {
    cache::runtime_wf(runtime)
        && numeric::regex_correct(runtime.pair.store.graph(), template, template.root as nat, runtime.pair.root)
}

pub(crate) proof fn lemma_runtime_frame(template: FlatPair<u64>, before: RuleRuntime, after: RuleRuntime)
    requires runtime_represents(template, before), cache::runtime_wf(after),
        crate::progress::verify::pair_frame(before.pair, after.pair),
    ensures runtime_represents(template, after),
{
    let first = before.pair.store.graph();
    let last = after.pair.store.graph();
    graph::lemma_graph_wf_elim(first);
    graph::lemma_lift_regex_stable(first, last, before.pair.root@);
    assert forall|theta: junco_core::verify::history_specs::Subst,
        word: Seq<junco_core::verify::history_specs::EventView>|
        junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
            graph::regex_lang(last, theta, after.pair.root@, word)
                == numeric::source_regex(template, template.root as nat, theta, word) by {
        assert(graph::regex_lang(first, theta, before.pair.root@, word)
            == numeric::source_regex(template, template.root as nat, theta, word));
    }
}

/// Shared Arc adapters establish matching ownership before the public decision.
pub(crate) fn shared_store_owner_decision_client<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, candidate: &E,
) -> (result: Result<(CompiledRule<E>, History<E>, Result<Option<bool>, HistoryError>), CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok((compiled, history, answer)) ==>
        crate::compiled_rule::decision_requires(compiled, history)
            && books::same_store_owner(compiled.store, raw::store_of(history))
            && answer != Err(HistoryError::WrongHistoryOwner),
{
    let history_owner = share_store(&store);
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    let history = History::new(history_owner)?;
    proof {
        raw::lemma_empty_history(history, history_owner);
        typed::lemma_constructed_decision(compiled, source, store, history);
        books::lemma_same_store_owner_identity(compiled.store, raw::store_of(history));
    }
    let ghost before = compiled;
    let answer = compiled.accepts_history(&history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, history, *candidate, answer); }
    proof {
        typed::lemma_compiled_store_representation(before);
        typed::lemma_compiled_store_representation(compiled);
    }
    Ok((compiled, history, answer))
}

/// Distinct constructor receipts contradict successful native pointer comparison.
pub(crate) fn independent_store_owner_decision_client<E: Event>(
    rule: Rule<E>, candidate: &E,
) -> (result: Result<(CompiledRule<E>, History<E>, Result<Option<bool>, HistoryError>), CompileError>)
    ensures result matches Ok((compiled, history, answer)) ==>
        crate::compiled_rule::decision_requires(compiled, history)
            && !books::same_store_owner(compiled.store, raw::store_of(history))
            && answer == Err(HistoryError::WrongHistoryOwner),
{
    let (left, right) = match books::independently_constructed_stores_client::<E, E>() {
        Ok(owners) => owners,
        Err(error) => { rule.dispose(); return Err(CompileError::Runtime(error)); },
    };
    let left = Arc::new(left);
    let right = Arc::new(right);
    let left_referent = borrow_store(&left);
    let right_referent = borrow_store(&right);
    let same = CompiledRule::same_owner(&left, &right);
    proof {
        assert(books::store_id(*left_referent) != books::store_id(*right_referent));
        assert(!same);
    }
    let ghost source = rule;
    let mut compiled = CompiledRule::new(left, rule)?;
    let history = History::new(right)?;
    proof {
        raw::lemma_empty_history(history, right);
        typed::lemma_constructed_decision(compiled, source, left, history);
    }
    let ghost before = compiled;
    let answer = compiled.accepts_history(&history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, history, *candidate, answer); }
    proof {
        typed::lemma_compiled_store_representation(before);
        typed::lemma_compiled_store_representation(compiled);
    }
    Ok((compiled, history, answer))
}

/// This is the actual public consuming constructor followed by the public decision.
/// No numeric-only event restriction or semantic-equivalence premise is supplied.
pub(crate) fn public_compiled_decision<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, history: &History<E>, candidate: &E,
) -> (result: Result<Option<bool>, CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history),
    ensures junco_core::spec::hypotheses::monitor_hypotheses::<E>() ==> (result matches Ok(answer)
        ==> answer == (if semantics::head_matches(rule.head@, *candidate) { Some(semantics::lang(rule.tail@, rule.head@, *candidate, raw::raw_events(*history))) } else { None })),
{
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    proof { typed::lemma_constructed_decision(compiled, source, store, *history); }
    let ghost before = compiled;
    let answer = compiled.accepts_history(history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, *history, *candidate, answer); }
    let accepted = answer?;
    Ok(accepted)
}

/// Real retained decisions span append, rollback, same-length replacement, truncate,
/// and a fresh-owner fork, without any caller-supplied cache-provenance premise.
pub(crate) fn retained_history_lifecycle<E: Event>(
    store: Arc<Store<E>>, rule: Rule<E>, history: &mut History<E>, appended: E,
    replacement: E, truncate_to: usize, candidate: &E,
) -> (result: Result<Option<bool>, CompileError>)
    requires books::store_wf(*store), raw::history_wf(*old(history)),
    ensures raw::history_wf(*final(history)),
        junco_core::spec::hypotheses::monitor_hypotheses::<E>() ==> (result matches Ok(answer)
            ==> answer == (if semantics::head_matches(rule.head@, *candidate) { Some(semantics::lang(rule.tail@, rule.head@, *candidate, raw::raw_events(*final(history)))) } else { None })),
{
    let ghost source = rule;
    let mut compiled = CompiledRule::new(store, rule)?;
    proof { typed::lemma_constructed_decision(compiled, source, store, *history); }
    let checkpoint = history.checkpoint();
    let ghost before = compiled;
    let answer = compiled.accepts_history(history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, *history, *candidate, answer); }
    let _ = answer?;
    history.push(appended)?;
    proof { typed::lemma_decision_requires(compiled, *history); }
    let ghost before = compiled;
    let answer = compiled.accepts_history(history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, *history, *candidate, answer); }
    let _ = answer?;
    history.rollback(checkpoint)?;
    proof { typed::lemma_decision_requires(compiled, *history); }
    let ghost before = compiled;
    let answer = compiled.accepts_history(history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, *history, *candidate, answer); }
    let _ = answer?;
    history.push(replacement)?;
    history.truncate(truncate_to)?;
    proof { typed::lemma_decision_requires(compiled, *history); }
    let ghost before = compiled;
    let answer = compiled.accepts_history(history, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, *history, *candidate, answer); }
    let _ = answer?;
    let fork = history.try_clone()?;
    proof {
        raw::lemma_clone_raw_word(*history, fork);
        typed::lemma_decision_requires(compiled, fork);
    }
    let ghost before = compiled;
    let answer = compiled.accepts_history(&fork, candidate);
    proof { typed::lemma_decision_result_facts(before, compiled, fork, *candidate, answer); }
    let accepted = answer?;
    Ok(accepted)
}

/// Retained-prefix clients exercise the very same body with explicit host fault leaves.
/// Later book extensions are acquired inside that body from both the constants'
/// and the history's finite published snapshots before deriving DSL semantics.
pub(crate) fn compiled_cached_decision<E: Event, L: Limits>(
    compiled: &mut CompiledRule<E>, history: &History<E>, candidate: &E,
    limits: &mut L, world: &mut ObservationWorld,
) -> (result: Result<Option<bool>, HistoryError>)
    requires crate::compiled_rule::decision_requires(*old(compiled), *history),
    ensures crate::compiled_rule::decision_result(*old(compiled), *final(compiled), *history, *candidate, result),
        junco_core::spec::hypotheses::monitor_hypotheses::<E>() ==>
            typed::dsl_result(crate::compiled_rule::source_rule(*old(compiled)), *history, *candidate, result),
{
    let ghost before = *compiled;
    let result = compiled.accepts_history_with_limits(history, candidate, limits, world);
    proof { typed::lemma_decision_result_facts(before, *compiled, *history, *candidate, result); }
    result
}

// These clients exercise construction and transactions, rather than assuming a verdict.
pub(crate) fn validator_check_client<E: Event, M>(
    state: &mut Validator<E>, request: Request<E, M>,
) -> (result: Result<Decision<E, M>, HistoryError>)
    requires (*old(state)).wf(),
    ensures final(state).wf(), monitor::validator_frame(old(state)@, final(state)@),
        crate::validator::check_storage(*old(state), *final(state), request, result),
        junco_core::spec::hypotheses::monitor_hypotheses::<E>()
            ==> monitor::check_step(old(state)@, final(state)@, request, result),
{
    state.check(request)
}

pub(crate) fn compiled_policy_decide_client<E: Event, C, F: FnOnce() -> C>(
    state: &mut CompiledPolicy<E, C>, history: &History<E>, candidate: &E, context: F,
) -> (result: Result<PolicyDecision, HistoryError>)
    requires crate::policy::evaluate::policy_wf(*old(state)), raw::history_wf(*history), call_requires(context, ()),
    ensures policy_storage_result(*old(state), *final(state), *history, *candidate, result),
        junco_core::spec::hypotheses::monitor_hypotheses::<E>() ==>
            monitor::policy_decision_spec(crate::policy::evaluate::policy_sources(*old(state)), raw::raw_events(*history),
                *candidate, crate::policy::evaluate::policy_selected_index(*final(state)) as int, result),
{
    state.decide(history, candidate, context)
}

pub(crate) fn validator_from_rules_client<E: Event>(
    store: Arc<Store<E>>, rules: Vec<Rule<E>>,
) -> (result: Result<Validator<E>, CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok(state) ==> (state).wf()
        && raw::history_wf(state.history) && state@.history == Seq::<E>::empty()
        && (state)@.rules == rules@
        && raw::empty_history((state).history, store),
{
    let ghost original = rules@;
    let count = rules.len();
    let mut builder = Validator::builder(store);
    let mut remaining = rules.into_iter();
    let mut index: usize = 0;
    while index < count
        invariant count == original.len(), index <= original.len(), (builder).wf(),
            (builder).store_spec() == store,
            (builder)@ == original.take(index as int),
            remaining.remaining() == original.skip(index as int),
            remaining.obeys_prophetic_iter_laws(),
        decreases original.len() - index,
    {
        let item = remaining.next();
        match item {
            Some(source) => { builder.add_rule(source)?; },
            None => { proof { assert(false); } },
        }
        index += 1;
        proof { assert((builder)@ =~= original.take(index as int)); }
    }
    let ghost finished_builder = builder;
    let state = builder.finish()?;
    proof { assert(original.take(original.len() as int) =~= original); }
    proof { validator::lemma_finish_storage(finished_builder, state); }
    Ok(state)
}

pub(crate) fn compiled_policy_from_vec_client<E: Event, C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>,
) -> (result: Result<CompiledPolicy<E, C>, CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok(state) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_store(state) == store
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && crate::policy::evaluate::policy_trace_empty(state),
{
    CompiledPolicy::new(store, rules)
}

pub(crate) fn validator_require_empty_then_forbid_all_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), semantics::head_matches(head@, request.event), second_head == head,
    ensures result matches Ok((state, decision)) ==> (state).wf()
        && (state)@.rules == seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty }, Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::All }]
        && (state)@.history == Seq::<E>::empty()
        && junco_core::spec::semantics::least_violation((state)@.rules, (state)@.history, request.event, 0)
        && decision is Denied && (decision matches Decision::Denied(denial) ==> denial.mode == RuleMode::Require && denial.event == request.event),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty });
    rules.push(Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::All });
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        raw::lemma_empty_history((state).history, store);
        assert(junco_core::spec::semantics::least_violation((state)@.rules, (state)@.history, request.event, 0));
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { raw::lemma_history_frame_facts((before).history, (state).history); }
    Ok((state, decision))
}

pub(crate) fn validator_forbid_all_then_require_empty_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), semantics::head_matches(head@, request.event), second_head == head,
    ensures result matches Ok((state, decision)) ==> (state).wf()
        && (state)@.rules == seq![Rule { mode: RuleMode::Forbid, head: head, tail: RegexExpr::All }, Rule { mode: RuleMode::Require, head: second_head, tail: RegexExpr::Empty }]
        && (state)@.history == Seq::<E>::empty()
        && junco_core::spec::semantics::least_violation((state)@.rules, (state)@.history, request.event, 0)
        && decision is Denied && (decision matches Decision::Denied(denial) ==> denial.mode == RuleMode::Forbid && denial.event == request.event),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Forbid, head: head, tail: RegexExpr::All });
    rules.push(Rule { mode: RuleMode::Require, head: second_head, tail: RegexExpr::Empty });
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        raw::lemma_empty_history((state).history, store);
        assert(junco_core::spec::semantics::least_violation((state)@.rules, (state)@.history, request.event, 0));
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { raw::lemma_history_frame_facts((before).history, (state).history); }
    Ok((state, decision))
}

pub(crate) fn validator_require_all_and_forbid_empty_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>, second_head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), semantics::head_matches(head@, request.event), second_head == head,
    ensures result matches Ok((state, decision)) ==> (state).wf()
        && (state)@.rules == seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::All }, Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::Empty }]
        && (state)@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::All });
    rules.push(Rule { mode: RuleMode::Forbid, head: second_head, tail: RegexExpr::Empty });
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        raw::lemma_empty_history((state).history, store);
        assert forall|i: int| 0 <= i < (state)@.rules.len() implies
            !semantics::rule_violated((state)@.rules[i], request.event, (state)@.history) by {}
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { validator::lemma_check_storage(before, state, request, Ok(decision)); }
    Ok((state, decision))
}

pub(crate) fn validator_head_mismatch_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>, head: Head<E>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), !semantics::head_matches(head@, request.event),
    ensures result matches Ok((state, decision)) ==> (state).wf()
        && (state)@.rules == seq![Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty }]
        && (state)@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let mut rules = Vec::new();
    rules.push(Rule { mode: RuleMode::Require, head: head, tail: RegexExpr::Empty });
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        raw::lemma_empty_history((state).history, store);
        assert forall|i: int| 0 <= i < (state)@.rules.len() implies
            !semantics::rule_violated((state)@.rules[i], request.event, (state)@.history) by {}
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { validator::lemma_check_storage(before, state, request, Ok(decision)); }
    Ok((state, decision))
}

pub(crate) fn validator_empty_table_client<E: Event, M>(
    store: Arc<Store<E>>, request: Request<E, M>,
) -> (result: Result<(Validator<E>, Decision<E, M>), CompileError>)
    requires books::store_wf(*store), junco_core::spec::hypotheses::monitor_hypotheses::<E>(),
    ensures result matches Ok((state, decision)) ==> (state).wf()
        && (state)@.rules == seq![]
        && (state)@.history == seq![request.event]
        && decision is Grant && (decision matches Decision::Grant(grant) ==> grant.event == request.event && grant.metadata == request.metadata),
{
    let mut rules = Vec::new();
    let mut state = validator_from_rules_client(store, rules)?;
    let ghost before = state;
    proof {
        raw::lemma_empty_history((state).history, store);
        assert forall|i: int| 0 <= i < (state)@.rules.len() implies
            !semantics::rule_violated((state)@.rules[i], request.event, (state)@.history) by {}
    }
    let decision = validator_check_client(&mut state, request)?;
    proof { validator::lemma_check_storage(before, state, request, Ok(decision)); }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_require_empty_then_forbid_all_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::Empty }, Rule { mode: RuleMode::Forbid, head: second_head@, tail: RegexExpr::All }], semantics::head_matches(head@@, *candidate), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Deny && policy::policy_trace(state).calls.len() == 1
        && policy::policy_trace(state).context_calls == 1 && policy::policy_trace(state).diagnostic_calls == 1
        && policy::policy_trace(state).calls[0].index == 0
        && policy::policy_trace(state).calls[0].source == policy_rule_source(rules@[0])
        && policy::policy_trace(state).calls[0].diagnostic_id == policy_rule_diagnostic(rules@[0]),
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        policy::lemma_policy_wf(state);
        policy::lemma_policy_trace_observations(state);
        assert(junco_core::spec::semantics::least_violation(crate::policy::evaluate::policy_sources(state), raw::raw_events(*history), *candidate, 0));
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        policy::lemma_policy_decision_result_facts(before, state, *history, *candidate, Ok(decision));
        policy::lemma_policy_trace_observations(state);
        if decision is Deny {
            let index = policy::policy_trace(state).calls.last().index;
            assert(index == 0) by {
                if index > 0 { assert(!semantics::rule_violated(crate::policy::evaluate::policy_sources(before)[0], *candidate, raw::raw_events(*history))); }
            }
        }
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_forbid_all_then_require_empty_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Forbid, head: head@, tail: RegexExpr::All }, Rule { mode: RuleMode::Require, head: second_head@, tail: RegexExpr::Empty }], semantics::head_matches(head@@, *candidate), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Deny && policy::policy_trace(state).calls.len() == 1
        && policy::policy_trace(state).context_calls == 1 && policy::policy_trace(state).diagnostic_calls == 1
        && policy::policy_trace(state).calls[0].index == 0
        && policy::policy_trace(state).calls[0].source == policy_rule_source(rules@[0])
        && policy::policy_trace(state).calls[0].diagnostic_id == policy_rule_diagnostic(rules@[0]),
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        policy::lemma_policy_wf(state);
        policy::lemma_policy_trace_observations(state);
        assert(junco_core::spec::semantics::least_violation(crate::policy::evaluate::policy_sources(state), raw::raw_events(*history), *candidate, 0));
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        policy::lemma_policy_decision_result_facts(before, state, *history, *candidate, Ok(decision));
        policy::lemma_policy_trace_observations(state);
        if decision is Deny {
            let index = policy::policy_trace(state).calls.last().index;
            assert(index == 0) by {
                if index > 0 { assert(!semantics::rule_violated(crate::policy::evaluate::policy_sources(before)[0], *candidate, raw::raw_events(*history))); }
            }
        }
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_require_all_and_forbid_empty_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>, second_head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::All }, Rule { mode: RuleMode::Forbid, head: second_head@, tail: RegexExpr::Empty }], semantics::head_matches(head@@, *candidate), second_head@ == head@,
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && crate::policy::evaluate::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        policy::lemma_policy_wf(state);
        policy::lemma_policy_trace_observations(state);
        assert forall|i: int| 0 <= i < crate::policy::evaluate::policy_sources(state).len() implies
            !semantics::rule_violated(crate::policy::evaluate::policy_sources(state)[i], *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        policy::lemma_policy_decision_result_facts(before, state, *history, *candidate, Ok(decision));
        policy::lemma_policy_trace_observations(state);
        assert(decision is Grant);
        assert(policy::policy_trace(state).calls =~= Seq::empty());
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_head_mismatch_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F, head: Ghost<Head<E>>,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![Rule { mode: RuleMode::Require, head: head@, tail: RegexExpr::Empty }], !semantics::head_matches(head@@, *candidate),
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && crate::policy::evaluate::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        policy::lemma_policy_wf(state);
        policy::lemma_policy_trace_observations(state);
        assert forall|i: int| 0 <= i < crate::policy::evaluate::policy_sources(state).len() implies
            !semantics::rule_violated(crate::policy::evaluate::policy_sources(state)[i], *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        policy::lemma_policy_decision_result_facts(before, state, *history, *candidate, Ok(decision));
        policy::lemma_policy_trace_observations(state);
        assert(decision is Grant);
        assert(policy::policy_trace(state).calls =~= Seq::empty());
    }
    Ok((state, decision))
}

pub(crate) fn compiled_policy_empty_table_client<E: Event, C, F: FnOnce() -> C>(
    store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>, history: &History<E>, candidate: &E, context: F,
) -> (result: Result<(CompiledPolicy<E, C>, PolicyDecision), CompileError>)
    requires books::store_wf(*store), raw::history_wf(*history), junco_core::spec::hypotheses::monitor_hypotheses::<E>(), rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item)) == seq![],
        call_requires(context, ()),
    ensures result matches Ok((state, decision)) ==> crate::policy::evaluate::policy_wf(state)
        && crate::policy::evaluate::policy_sources(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_source(item))
        && crate::policy::evaluate::policy_diagnostic_ids(state) == rules@.map(|i: int, item: PolicyRule<E, C>| policy_rule_diagnostic(item))
        && decision is Grant && crate::policy::evaluate::policy_trace_empty(state)
        && policy::policy_trace(state).context_calls == 0 && policy::policy_trace(state).diagnostic_calls == 0,
{
    let mut state = compiled_policy_from_vec_client(store, rules)?;
    let ghost before = state;
    proof {
        policy::lemma_policy_wf(state);
        policy::lemma_policy_trace_observations(state);
        assert forall|i: int| 0 <= i < crate::policy::evaluate::policy_sources(state).len() implies
            !semantics::rule_violated(crate::policy::evaluate::policy_sources(state)[i], *candidate, raw::raw_events(*history)) by {}
    }
    let decision = compiled_policy_decide_client(&mut state, history, candidate, context)?;
    proof {
        policy::lemma_policy_decision_result_facts(before, state, *history, *candidate, Ok(decision));
        policy::lemma_policy_trace_observations(state);
        assert(decision is Grant);
        assert(policy::policy_trace(state).calls =~= Seq::empty());
    }
    Ok((state, decision))
}

}
