#![cfg(all(verus_keep_ghost, feature = "runtime"))]

extern crate alloc;

use alloc::{boxed::Box, string::String, sync::Arc, vec::Vec};
use history_semantics::compiled_rule::{CompiledRule, verify as compiled};
use history_semantics::policy::evaluate::verify as policy;
use history_semantics::policy::rule::verify::diagnostic_output;
use history_semantics::policy::trace::verify as trace;
use history_semantics::policy::{CompiledPolicy, PolicyDecision, TracePolicy, TraceRule};
use history_semantics::runtime::{RuleRuntime, verify as runtime};
use history_semantics::validator::{Decision, Validator, verify as validator};
use history_store::history::{History, verify as history};
use history_store::store::{HistoryStore, verify as records};
use history_store::typed::{Store, share_store, verify as books};
use history_syntax::event::specs::{EventSpec, arity, event_view, projection_laws};
use history_syntax::verify::dsl::{HeadView, RegexView, TestView};
use history_syntax::{Component, Event, Head, MAX_ARITY, RegexExpr, Rule, RuleMode};
use junco_core::event::Request;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::verify::{dsl, history_specs};
use junco_core::{CompileError, HistoryError};
use vstd::prelude::*;
use vstd::view::DeepView;

verus! {
broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

fn indexed_projection<E: Event>(event: E, index: usize) -> (result: (E::Component, usize))
    requires E::obeys_projection_spec(), projection_laws::<E>(), index < arity::<E>(),
    ensures result.0 == event_view(event)[index as int], result.1 == index,
{
    let component = event.component(index);
    let coordinate = E::coordinate(component);
    proof {
        assert(E::coordinate_spec(event.component_spec(index as int)) == index);
    }
    (component, coordinate)
}

// Native event laws are needed for semantic answers, not for construction or exact sequences.
fn vec_history<E: Event>(events: Vec<E>) -> (result: Result<History<E>, HistoryError>)
    ensures result matches Ok(value) ==> history::history_wf(value)
        && history::raw_events(value) == events@
        && value.spec_numeric().spec_revision() == 0,
{
    let store = Arc::new(Store::<E>::new()?);
    proof { history_specs::lemma_vec_into_iter_yields(events); }
    let value = History::from_events(store, events)?;
    proof { history::lemma_initialized_history_facts(value, store); }
    Ok(value)
}

// Scoped native sources cannot manufacture structural or scope errors.
fn scoped_production_compile<E: Event>(source: Rule<E>)
    -> (result: Result<CompiledRule<E>, CompileError>)
    requires books::native_obligations::<E>(), dsl::head_scoped(source.head@),
        dsl::regex_scoped(source.tail@, source.head@),
    ensures history_specs::no_internal_compile_error(result),
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
        !(result matches Err(CompileError::UnboundVariable { .. })),
        !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
{
    let store = Arc::new(Store::<E>::new()?);
    CompiledRule::new(store, source)
}

// One executable client is universally instantiated over all five truth-table cases.
fn compiled_truth_table<E: Event>(
    head: Head<E>, mode: RuleMode, universal: bool, events: Vec<E>, candidate: &E,
) -> (result: Result<(History<E>, CompiledRule<E>, Result<Option<bool>, HistoryError>), CompileError>)
    requires books::native_obligations::<E>(),
    ensures result matches Ok((value, rule, answer)) ==>
        history::raw_events(value) == events@
        && compiled::source_rule(rule) == (Rule { mode, head,
            tail: if universal { RegexExpr::All } else { RegexExpr::Empty } })
        && answer != Err(HistoryError::WrongHistoryOwner)
        && history_specs::no_invariant_failure(answer)
        && (answer matches Ok(option) ==>
            option == (if dsl::head_matches(head@, event_view(*candidate)) {
                Some(universal)
            } else { None }))
        && (answer is Ok ==> dsl::rule_violated(compiled::source_rule(rule), *candidate, events@)
            == (dsl::head_matches(head@, event_view(*candidate))
                && match mode { RuleMode::Require => !universal, RuleMode::Forbid => universal })),
{
    let store = Arc::new(Store::<E>::new()?);
    let owner = share_store(&store);
    proof { books::lemma_same_store_owner_identity(store, owner); }
    proof { history_specs::lemma_vec_into_iter_yields(events); }
    let value = History::from_events(owner, events)?;
    let tail = if universal { RegexExpr::All } else { RegexExpr::Empty };
    let source = Rule::new(mode, head, tail);
    let ghost original = source;
    let mut rule = CompiledRule::new(store, source)?;
    proof {
        history::lemma_initialized_history_facts(value, owner);
        compiled::lemma_constructed_decision(rule, original, store, value);
    }
    let ghost before = rule;
    let answer = rule.accepts_history(&value, candidate);
    proof {
        compiled::lemma_decision_result_facts(before, rule, value, *candidate, answer);
        if answer is Ok {
            assert(answer == Ok(dsl::rule_evaluation(original, *candidate, events@)));
        }
    }
    Ok((value, rule, answer))
}

fn five_decision_cases<E: Event>(mismatch: Head<E>, require_all: Head<E>, forbid_all: Head<E>,
    require_empty: Head<E>, forbid_empty: Head<E>, candidate: &E) -> Result<(), CompileError>
    requires books::native_obligations::<E>(),
        !dsl::head_matches(mismatch@, event_view(*candidate)),
        dsl::head_matches(require_all@, event_view(*candidate)),
        dsl::head_matches(forbid_all@, event_view(*candidate)),
        dsl::head_matches(require_empty@, event_view(*candidate)),
        dsl::head_matches(forbid_empty@, event_view(*candidate)),
{
    let (value, rule, answer) = compiled_truth_table(mismatch, RuleMode::Require, false, Vec::new(), candidate)?;
    assert(answer is Ok ==> answer == Ok(None));
    assert(answer is Ok ==> !dsl::rule_violated(compiled::source_rule(rule), *candidate, history::raw_events(value)));
    let (value, rule, answer) = compiled_truth_table(require_all, RuleMode::Require, true, Vec::new(), candidate)?;
    assert(answer is Ok ==> answer == Ok(Some(true)));
    assert(answer is Ok ==> !dsl::rule_violated(compiled::source_rule(rule), *candidate, history::raw_events(value)));
    let (value, rule, answer) = compiled_truth_table(forbid_all, RuleMode::Forbid, true, Vec::new(), candidate)?;
    assert(answer is Ok ==> answer == Ok(Some(true)));
    assert(answer is Ok ==> dsl::rule_violated(compiled::source_rule(rule), *candidate, history::raw_events(value)));
    let (value, rule, answer) = compiled_truth_table(require_empty, RuleMode::Require, false, Vec::new(), candidate)?;
    assert(answer is Ok ==> answer == Ok(Some(false)));
    assert(answer is Ok ==> dsl::rule_violated(compiled::source_rule(rule), *candidate, history::raw_events(value)));
    let (value, rule, answer) = compiled_truth_table(forbid_empty, RuleMode::Forbid, false, Vec::new(), candidate)?;
    assert(answer is Ok ==> answer == Ok(Some(false)));
    assert(answer is Ok ==> !dsl::rule_violated(compiled::source_rule(rule), *candidate, history::raw_events(value)));
    Ok(())
}

// No Event/projection premise is needed to rule out selection from an empty table.
fn empty_policy<E: Event>(events: Vec<E>, candidate: &E)
    -> (result: Result<(CompiledPolicy<E, ()>, Result<PolicyDecision, HistoryError>), CompileError>)
    ensures result matches Ok((state, answer)) ==>
        policy::policy_sources(state) == Seq::<Rule<E>>::empty()
        && policy::policy_context_calls(state) == 0
        && policy::policy_diagnostic_calls(state) == 0
        && (answer is Ok ==> answer == Ok(PolicyDecision::Grant)),
{
    let store = Arc::new(Store::<E>::new()?);
    let owner = share_store(&store);
    proof { history_specs::lemma_vec_into_iter_yields(events); }
    let value = History::from_events(owner, events)?;
    let rules = Vec::<history_semantics::policy::PolicyRule<E, ()>>::new();
    let mut state = CompiledPolicy::new(store, rules)?;
    proof { policy::lemma_policy_wf(state); }
    let ghost before = state;
    let context = || ();
    let answer = state.decide(&value, candidate, context);
    proof { policy::lemma_policy_decision_result_facts(before, state, value, *candidate, answer); }
    Ok((state, answer))
}

// Both rules violate. Selection is by index, without assuming distinct callback identities.
fn trace_first_diagnostic<E: Event + 'static,
    D0: Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static,
    D1: Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static>(
    first_head: Head<E>, second_head: Head<E>, events: Vec<E>, candidate: &E,
    first_diagnostic: D0, second_diagnostic: D1,
) -> (result: Result<(History<E>, TracePolicy<E>, Result<PolicyDecision, HistoryError>), CompileError>)
    requires books::native_obligations::<E>(),
        dsl::head_matches(first_head@, event_view(*candidate)),
        dsl::head_matches(second_head@, event_view(*candidate)),
        forall|argument: &E| call_requires(first_diagnostic, (argument,)),
        forall|argument: &E| call_requires(second_diagnostic, (argument,)),
    ensures result matches Ok((value, state, answer)) ==>
        history::raw_events(value) == events@
        && trace::trace_sources(state) == seq![
            Rule { mode: RuleMode::Forbid, head: first_head, tail: RegexExpr::All },
            Rule { mode: RuleMode::Require, head: second_head, tail: RegexExpr::Empty }]
        && trace::trace_diagnostic_ids(state) == seq![
            trace::trace_callback_identity(first_diagnostic), trace::trace_callback_identity(second_diagnostic)]
        && answer != Err(HistoryError::WrongHistoryOwner)
        && match answer {
            Err(_) => trace::trace_context_calls(state) == 0 && trace::trace_diagnostic_calls(state) == 0,
            Ok(PolicyDecision::Grant) => false,
            Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) =>
                trace::trace_context_calls(state) == 1 && trace::trace_diagnostic_calls(state) == 1
                && trace::trace_selected_index(state) == 0
                && trace::trace_selected_diagnostic_id(state) == trace::trace_callback_identity(first_diagnostic)
                && diagnostic_output(trace::trace_callback_identity(first_diagnostic), *candidate,
                    failed_precondition@, allowed_fixes.deep_view())
                && exists|argument: &E| *argument == *candidate
                    && call_ensures(first_diagnostic, (argument,), (failed_precondition, allowed_fixes)),
        },
{
    let store = Arc::new(Store::<E>::new()?);
    let owner = share_store(&store);
    proof { books::lemma_same_store_owner_identity(store, owner); }
    proof { history_specs::lemma_vec_into_iter_yields(events); }
    let value = History::from_events(owner, events)?;
    proof { history::lemma_initialized_history_facts(value, owner); }
    let first = Rule::new(RuleMode::Forbid, first_head, RegexExpr::All);
    let second = Rule::new(RuleMode::Require, second_head, RegexExpr::Empty);
    let ghost first_source = first;
    let ghost second_source = second;
    proof {
        assert(first_source.tail@ == RegexView::All);
        assert(second_source.tail@ == RegexView::Empty);
        assert(dsl::lang(first_source.tail@, first_head@, event_view(*candidate),
            events@.map(|i: int, event: E| event_view(event))));
        assert(!dsl::lang(second_source.tail@, second_head@, event_view(*candidate),
            events@.map(|i: int, event: E| event_view(event))));
        assert(dsl::rule_evaluation(first_source, *candidate, events@) == Some(true));
        assert(dsl::rule_evaluation(second_source, *candidate, events@) == Some(false));
        assert(dsl::rule_violated(first_source, *candidate, events@));
        assert(dsl::rule_violated(second_source, *candidate, events@));
    }
    let first = TraceRule::new(first, first_diagnostic);
    let second = TraceRule::new(second, second_diagnostic);
    let ghost first_rule = first;
    proof {
        assert forall|value: E, output: (String, Vec<String>)|
            #[trigger] diagnostic_output(trace::trace_rule_diagnostic_id(first_rule), value, output.0@, output.1.deep_view())
            implies exists|argument: &E| *argument == value && call_ensures(first_diagnostic, (argument,), output) by {}
    }
    let mut rules = Vec::new();
    rules.push(first);
    rules.push(second);
    proof { history_specs::lemma_vec_into_iter_yields(rules); }
    let ghost items = rules@;
    let mut state = TracePolicy::new(store, rules)?;
    proof {
        assert(trace::trace_sources(state)
            == items.map(|i: int, item: TraceRule<E>| trace::trace_rule_source(item)));
        assert(trace::trace_diagnostic_ids(state)
            == items.map(|i: int, item: TraceRule<E>| trace::trace_rule_diagnostic_id(item)));
        assert(trace::trace_sources(state) =~= seq![first_source, second_source]);
        assert(trace::trace_diagnostic_ids(state) =~= seq![
            trace::trace_callback_identity(first_diagnostic), trace::trace_callback_identity(second_diagnostic)]);
        assert(trace::trace_context_calls(state) == 0);
        assert(trace::trace_diagnostic_calls(state) == 0);
        assert(trace::trace_store(state) == store);
        assert(books::same_store_owner(trace::trace_store(state), history::store_of(value)));
    }
    let ghost before = state;
    let ghost raw_before = history::raw_events(value);
    let answer = state.decide(&value, candidate);
    proof {
        trace::lemma_trace_decision_result_facts(before, state, value, *candidate, answer);
        assert(history::raw_events(value) == raw_before);
        if let Ok(PolicyDecision::Grant) = answer {
            assert(!dsl::rule_violated(trace::trace_sources(before)[0], *candidate, events@));
            assert(false);
        }
        if let Ok(PolicyDecision::Deny { ref failed_precondition, ref allowed_fixes }) = answer {
            let index = trace::trace_selected_index(state) as int;
            assert(compiled::least_violation(trace::trace_sources(before), value, *candidate, index));
            assert(0 <= index < 2);
            if index != 0 {
                assert(0 <= 0 < index);
                assert(!dsl::rule_violated(trace::trace_sources(before)[0], *candidate, events@));
                assert(false);
            }
            assert(trace::trace_selected_index(state) == 0);
            assert(diagnostic_output(trace::trace_rule_diagnostic_id(first_rule), *candidate,
                failed_precondition@, allowed_fixes.deep_view()));
            let output = (*failed_precondition, *allowed_fixes);
            assert(diagnostic_output(trace::trace_rule_diagnostic_id(first_rule), *candidate, output.0@, output.1.deep_view()));
            assert(exists|argument: &E| *argument == *candidate
                && call_ensures(first_diagnostic, (argument,), (*failed_precondition, *allowed_fixes)));
        }
    }
    Ok((value, state, answer))
}

fn validator_transaction<E: Event, M>(head: Head<E>, universal: bool, request: Request<E, M>)
    -> (result: Result<(Validator<E>, Result<Decision<E, M>, HistoryError>), CompileError>)
    requires books::native_obligations::<E>(), dsl::head_matches(head@, event_view(request.event)),
    ensures result matches Ok((state, answer)) ==>
        match answer {
            Ok(Decision::Grant(grant)) => universal && grant.event == request.event
                && grant.metadata == request.metadata
                && history::raw_events(validator::validator_history(state)) == seq![request.event],
            Ok(Decision::Denied(denial)) => !universal && denial.event == request.event
                && denial.mode == RuleMode::Require
                && history::raw_events(validator::validator_history(state)) == Seq::<E>::empty(),
            Err(_) => history::raw_events(validator::validator_history(state)) == Seq::<E>::empty(),
        },
{
    let store = Arc::new(Store::<E>::new()?);
    let mut builder = Validator::builder(store);
    let tail = if universal { RegexExpr::All } else { RegexExpr::Empty };
    let rule = Rule::new(RuleMode::Require, head, tail);
    let ghost source = rule;
    builder.add_rule(rule)?;
    proof { assert(validator::builder_sources(builder) =~= seq![source]); }
    let mut state = builder.finish()?;
    let ghost before = state;
    proof {
        validator::lemma_validator_wf(state);
        history::lemma_empty_history(validator::validator_history(state), store);
        assert(validator::validator_sources(before) == seq![source]);
        assert(history::raw_events(validator::validator_history(before)) == Seq::<E>::empty());
        assert(source.tail@ == if universal { RegexView::All } else { RegexView::Empty });
        assert(dsl::lang(source.tail@, head@, event_view(request.event),
            Seq::<E>::empty().map(|i: int, event: E| event_view(event))) == universal);
        assert(dsl::rule_evaluation(source, request.event, Seq::<E>::empty()) == Some(universal));
        assert(dsl::rule_violated(source, request.event, Seq::<E>::empty()) == !universal);
    }
    let answer = state.check(request);
    proof {
        validator::lemma_check_result_facts(before, state, request, answer);
        match answer {
            Ok(Decision::Grant(_)) => {
                assert(!dsl::rule_violated(validator::validator_sources(before)[0], request.event,
                    history::raw_events(validator::validator_history(before))));
                assert(universal);
            },
            Ok(Decision::Denied(ref denial)) => {
                let index = choose|index: int| validator::denial_at(before, request, *denial, index)
                    && (books::native_obligations::<E>() ==>
                        denial.mode == validator::validator_sources(before)[index].mode
                            && compiled::least_violation(validator::validator_sources(before),
                                validator::validator_history(before), request.event, index));
                assert(compiled::least_violation(validator::validator_sources(before),
                    validator::validator_history(before), request.event, index));
                assert(index == 0);
                assert(denial.mode == RuleMode::Require);
                assert(!universal);
            },
            Err(_) => {},
        }
    }
    Ok((state, answer))
}

fn trace_observations<E: Event + 'static>(rules: Vec<TraceRule<E>>, events: Vec<E>, candidate: &E)
    -> (result: Result<(History<E>, TracePolicy<E>, Result<PolicyDecision, HistoryError>), CompileError>)
    ensures result matches Ok((value, state, answer)) ==>
        history::raw_events(value) == events@
        && trace::trace_sources(state) == rules@.map(|i: int, item: TraceRule<E>| trace::trace_rule_source(item))
        && trace::trace_diagnostic_ids(state) == rules@.map(|i: int, item: TraceRule<E>| trace::trace_rule_diagnostic_id(item))
        && match answer {
            Err(_) => trace::trace_context_calls(state) == 0 && trace::trace_diagnostic_calls(state) == 0,
            Ok(PolicyDecision::Grant) => trace::trace_context_calls(state) == 0
                && trace::trace_diagnostic_calls(state) == 0
                && (books::native_obligations::<E>() ==> forall|i: int| 0 <= i < rules@.len() ==>
                    !dsl::rule_violated(trace::trace_rule_source(rules@[i]), *candidate, events@)),
            Ok(PolicyDecision::Deny { failed_precondition, allowed_fixes }) =>
                trace::trace_context_calls(state) == 1 && trace::trace_diagnostic_calls(state) == 1
                && trace::trace_selected_index(state) < rules@.len()
                && trace::trace_selected_diagnostic_id(state)
                    == trace::trace_rule_diagnostic_id(rules@[trace::trace_selected_index(state) as int])
                && diagnostic_output(trace::trace_selected_diagnostic_id(state), *candidate,
                    failed_precondition@, allowed_fixes.deep_view())
                && (books::native_obligations::<E>() ==>
                    dsl::rule_violated(trace::trace_rule_source(rules@[trace::trace_selected_index(state) as int]),
                        *candidate, events@)
                    && forall|i: int| 0 <= i < trace::trace_selected_index(state) ==>
                        !dsl::rule_violated(trace::trace_rule_source(rules@[i]), *candidate, events@)),
        },
{
    let store = Arc::new(Store::<E>::new()?);
    let owner = share_store(&store);
    proof {
        history_specs::lemma_vec_into_iter_yields(events);
        history_specs::lemma_vec_into_iter_yields(rules);
    }
    let value = History::from_events(owner, events)?;
    let ghost items = rules@;
    let mut state = TracePolicy::new(store, rules)?;
    proof {
        assert(history::raw_events(value) == events@);
        assert(trace::trace_sources(state)
            == items.map(|i: int, item: TraceRule<E>| trace::trace_rule_source(item)));
        assert(trace::trace_diagnostic_ids(state)
            == items.map(|i: int, item: TraceRule<E>| trace::trace_rule_diagnostic_id(item)));
        assert(trace::trace_sources(state).len() == items.len());
        assert(trace::trace_context_calls(state) == 0);
        assert(trace::trace_diagnostic_calls(state) == 0);
    }
    let ghost before = state;
    let ghost raw_before = history::raw_events(value);
    let answer = state.decide(&value, candidate);
    proof {
        trace::lemma_trace_decision_result_facts(before, state, value, *candidate, answer);
        assert(history::raw_events(value) == raw_before);
        match answer {
            Ok(PolicyDecision::Grant) => {
                if books::native_obligations::<E>() {
                    assert forall|i: int| 0 <= i < items.len() implies
                        !dsl::rule_violated(trace::trace_rule_source(items[i]), *candidate, events@) by {
                        assert(trace::trace_sources(before)[i] == trace::trace_rule_source(items[i]));
                        assert(!dsl::rule_violated(trace::trace_sources(before)[i], *candidate,
                            history::raw_events(value)));
                    }
                }
            },
            Ok(PolicyDecision::Deny { .. }) => {
                let index = trace::trace_selected_index(state) as int;
                assert(0 <= index < items.len());
                assert(trace::trace_diagnostic_ids(before)[index] == trace::trace_rule_diagnostic_id(items[index]));
                if books::native_obligations::<E>() {
                    assert(compiled::least_violation(trace::trace_sources(before), value, *candidate, index));
                    assert(trace::trace_sources(before)[index] == trace::trace_rule_source(items[index]));
                    assert(dsl::rule_violated(trace::trace_rule_source(items[index]), *candidate, events@));
                    assert forall|i: int| 0 <= i < index implies
                        !dsl::rule_violated(trace::trace_rule_source(items[i]), *candidate, events@) by {
                        assert(trace::trace_sources(before)[i] == trace::trace_rule_source(items[i]));
                        assert(!dsl::rule_violated(trace::trace_sources(before)[i], *candidate,
                            history::raw_events(value)));
                    }
                }
            },
            Err(_) => {},
        }
    }
    Ok((value, state, answer))
}

fn last_state_change_helper<E: Event>(
    setter: history_syntax::TestExpr<E>, stable: history_syntax::TestExpr<E>,
    head: Ghost<HeadView<E::Component>>,
    candidate: Ghost<Seq<E::Component>>,
    word: Ghost<Seq<Seq<E::Component>>>,
) -> (tail: RegexExpr<E>)
    ensures tail@ == RegexView::Concat(seq![RegexView::All, RegexView::Test(setter@),
        RegexView::Star(Box::new(RegexView::Test(stable@)))]),
        dsl::lang(tail@, head@, candidate@, word@) <==> exists|i: int| 0 <= i < word@.len()
            && dsl::test_sem(setter@, head@, candidate@, word@[i])
            && forall|j: int| i < j < word@.len() ==> dsl::test_sem(stable@, head@, candidate@, word@[j]),
{
    let ghost setter_view = setter@;
    let ghost stable_view = stable@;
    let tail = history_semantics::policy::last_state_change(setter, stable);
    proof { dsl::lemma_last_state_change_lang(setter_view, stable_view, head@, candidate@, word@); }
    tail
}

// These are component-language facts: arbitrary native Event, Hash, and callback laws are irrelevant.
proof fn last_state_change_cases<C: PartialEq>(
    setter: TestView<C>, stable: TestView<C>, head: HeadView<C>,
    candidate: Seq<C>, set: Seq<C>, kept: Seq<C>, broken: Seq<C>,
)
    requires dsl::test_sem(setter, head, candidate, set),
        dsl::test_sem(stable, head, candidate, kept),
        !dsl::test_sem(setter, head, candidate, broken),
        !dsl::test_sem(stable, head, candidate, broken),
    ensures
        !dsl::lang(RegexView::Concat(seq![RegexView::All, RegexView::Test(setter),
            RegexView::Star(Box::new(RegexView::Test(stable)))]), head, candidate, seq![]),
        dsl::lang(RegexView::Concat(seq![RegexView::All, RegexView::Test(setter),
            RegexView::Star(Box::new(RegexView::Test(stable)))]), head, candidate, seq![set, kept]),
        !dsl::lang(RegexView::Concat(seq![RegexView::All, RegexView::Test(setter),
            RegexView::Star(Box::new(RegexView::Test(stable)))]), head, candidate, seq![set, broken]),
        dsl::lang(RegexView::Concat(seq![RegexView::All, RegexView::Test(TestView::True),
            RegexView::Star(Box::new(RegexView::Test(TestView::True)))]), head, candidate, seq![set, kept]),
{
    dsl::lemma_last_state_change_lang(setter, stable, head, candidate, seq![]);
    dsl::lemma_last_state_change_lang(setter, stable, head, candidate, seq![set, kept]);
    assert(exists|i: int| 0 <= i < 2 && dsl::test_sem(setter, head, candidate, seq![set, kept][i])
        && forall|j: int| i < j < 2 ==> dsl::test_sem(stable, head, candidate, seq![set, kept][j])) by {
        assert(dsl::test_sem(setter, head, candidate, seq![set, kept][0]));
    }
    dsl::lemma_last_state_change_lang(setter, stable, head, candidate, seq![set, broken]);
    assert forall|i: int| 0 <= i < 2 implies
        !(dsl::test_sem(setter, head, candidate, seq![set, broken][i])
            && forall|j: int| i < j < 2 ==> dsl::test_sem(stable, head, candidate, seq![set, broken][j])) by {
        if i == 0 { assert(!dsl::test_sem(stable, head, candidate, seq![set, broken][1])); }
    }
    dsl::lemma_last_state_change_lang(TestView::True, TestView::True, head, candidate, seq![set, kept]);
    assert(exists|i: int| 0 <= i < 2 && dsl::test_sem(TestView::True, head, candidate, seq![set, kept][i])
        && forall|j: int| i < j < 2 ==> dsl::test_sem(TestView::True, head, candidate, seq![set, kept][j])) by {
        assert(dsl::test_sem(TestView::True, head, candidate, seq![set, kept][0]));
    }
}

fn shared_owner<E: Event>(source: Rule<E>, candidate: &E)
    -> (result: Result<Result<Option<bool>, HistoryError>, CompileError>)
    ensures result matches Ok(answer) ==> answer != Err(HistoryError::WrongHistoryOwner),
{
    let store = Arc::new(Store::<E>::new()?);
    let owner = share_store(&store);
    proof { books::lemma_same_store_owner_identity(store, owner); }
    let value = History::new(owner)?;
    let ghost original = source;
    let mut rule = CompiledRule::new(store, source)?;
    proof {
        history::lemma_empty_history(value, owner);
        compiled::lemma_constructed_decision(rule, original, store, value);
    }
    let ghost before = rule;
    let answer = rule.accepts_history(&value, candidate);
    proof { compiled::lemma_decision_result_facts(before, rule, value, *candidate, answer); }
    Ok(answer)
}

fn independent_owners<E: Event>(head: Head<E>, candidate: &E)
    -> (result: Result<Result<Option<bool>, HistoryError>, CompileError>)
    ensures result matches Ok(answer) ==> answer == Err(HistoryError::WrongHistoryOwner),
{
    let (left, right) = books::independently_constructed_stores_client::<E, E>()?;
    let left = Arc::new(left);
    let right = Arc::new(right);
    let same = CompiledRule::same_owner(&left, &right);
    proof { assert(!same); }
    let left_owner = share_store(&left);
    let left_history = History::new(left_owner)?;
    let checkpoint = left_history.checkpoint();
    let mut value = History::new(right)?;
    proof {
        history::lemma_empty_history(left_history, left_owner);
        history::lemma_empty_history(value, right);
        history::lemma_distinct_checkpoint_owner(left_history, value, checkpoint);
    }
    let ghost before_rollback = value;
    let rollback = value.rollback(checkpoint);
    proof {
        history::lemma_rollback_result(before_rollback, value, checkpoint, rollback);
        history::lemma_state_frame_facts(before_rollback, value);
        assert(rollback == Err(HistoryError::WrongCheckpointOwner));
    }
    let source = Rule::new(RuleMode::Require, head, RegexExpr::All);
    let ghost original = source;
    let mut rule = CompiledRule::new(left, source)?;
    proof {
        compiled::lemma_constructed_decision(rule, original, left, value);
    }
    let ghost before = rule;
    let answer = rule.accepts_history(&value, candidate);
    proof { compiled::lemma_decision_result_facts(before, rule, value, *candidate, answer); }
    Ok(answer)
}

// Exhaustive typed tables are consumed after actual mutations, not supplied as premises.
fn typed_truncate_table<E: Event>(value: &mut History<E>, len: usize)
    -> (result: Result<(), HistoryError>)
    requires history::history_wf(*old(value)),
    ensures history::history_wf(*final(value)),
        if len >= history::raw_events(*old(value)).len() {
            result == Ok(()) && history::raw_events(*final(value)) == history::raw_events(*old(value))
                && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision()
                && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric())
        } else if old(value).spec_numeric().spec_revision() == u64::MAX {
            result == Err(HistoryError::RevisionExhausted)
                && history::raw_events(*final(value)) == history::raw_events(*old(value))
                && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision()
                && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric())
        } else {
            result == Ok(())
                && history::raw_events(*final(value)) == history::raw_events(*old(value)).take(len as int)
                && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric()).take(len as int)
                && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision() + 1
        },
{
    let ghost before = *value;
    let result = value.truncate(len);
    proof {
        history::lemma_truncate_result(before, *value, len, result);
        if len >= history::raw_events(before).len() || before.spec_numeric().spec_revision() == u64::MAX {
            history::lemma_state_frame_facts(before, *value);
        }
    }
    result
}

fn typed_rollback_table<E: Event>(value: &mut History<E>, checkpoint: history_store::history::Checkpoint)
    -> (result: Result<(), HistoryError>)
    requires history::history_wf(*old(value)),
    ensures history::history_wf(*final(value)),
        !history::checkpoint_owned(*old(value), checkpoint) ==>
            result == Err(HistoryError::WrongCheckpointOwner),
        history::checkpoint_owned(*old(value), checkpoint)
            && history::checkpoint_len(checkpoint) > history::raw_events(*old(value)).len() ==>
                result == Err(HistoryError::CheckpointBeyondHistory),
        history::checkpoint_owned(*old(value), checkpoint)
            && history::checkpoint_len(checkpoint) == history::raw_events(*old(value)).len() ==>
                result == Ok(())
                    && history::raw_events(*final(value)) == history::raw_events(*old(value))
                    && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric())
                    && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision(),
        history::checkpoint_owned(*old(value), checkpoint)
            && history::checkpoint_len(checkpoint) < history::raw_events(*old(value)).len() ==>
                if old(value).spec_numeric().spec_revision() == u64::MAX {
                    result == Err(HistoryError::RevisionExhausted)
                } else {
                    result == Ok(())
                        && history::raw_events(*final(value)) == history::raw_events(*old(value)).take(history::checkpoint_len(checkpoint) as int)
                        && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric()).take(history::checkpoint_len(checkpoint) as int)
                        && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision() + 1
                },
        result is Err ==> history::raw_events(*final(value)) == history::raw_events(*old(value))
            && history::stored_events(final(value).spec_numeric()) == history::stored_events(old(value).spec_numeric())
            && final(value).spec_numeric().spec_revision() == old(value).spec_numeric().spec_revision(),
{
    let ghost before = *value;
    let result = value.rollback(checkpoint);
    proof {
        history::lemma_rollback_result(before, *value, checkpoint, result);
        if result is Err || (history::checkpoint_owned(before, checkpoint)
            && history::checkpoint_len(checkpoint) == history::raw_events(before).len()) {
            history::lemma_state_frame_facts(before, *value);
        }
    }
    result
}

// These concrete reachable states cover no-op, shrink, owner precedence, and a future marker.
fn typed_history_transactions<E: Event>(event: E)
    -> (result: Result<History<E>, HistoryError>)
    ensures result matches Ok(value) ==> history::raw_events(value) == seq![event]
        && value.spec_numeric().spec_revision() == 2,
{
    let mut events = Vec::new();
    events.push(event);
    events.push(event);
    let mut value = vec_history(events)?;
    let full = value.checkpoint();
    let ghost original = value;
    proof { history::lemma_checkpoint_matches(value, full); }
    let no_op = value.truncate(2);
    proof {
        history::lemma_truncate_result(original, value, 2, no_op);
        history::lemma_state_frame_facts(original, value);
        assert(no_op == Ok(()));
        history::lemma_checkpoint_owner_preserved(original, value, full);
    }
    let ghost before_shrink = value;
    let shrink = value.truncate(1);
    proof {
        history::lemma_truncate_result(before_shrink, value, 1, shrink);
        assert(shrink == Ok(()));
        history::lemma_checkpoint_owner_preserved(before_shrink, value, full);
    }
    let ghost before_beyond = value;
    let beyond = value.rollback(full);
    proof {
        history::lemma_rollback_result(before_beyond, value, full, beyond);
        history::lemma_state_frame_facts(before_beyond, value);
        assert(beyond == Err(HistoryError::CheckpointBeyondHistory));
    }
    let marker = value.checkpoint();
    let ghost before_fork = value;
    let mut fork = value.try_clone()?;
    proof { history::lemma_clone_facts(before_fork, fork, marker); }
    let ghost before_foreign = fork;
    let foreign = fork.rollback(marker);
    proof {
        history::lemma_rollback_result(before_foreign, fork, marker, foreign);
        history::lemma_state_frame_facts(before_foreign, fork);
        assert(foreign == Err(HistoryError::WrongCheckpointOwner));
    }
    let ghost before_noop = value;
    proof { history::lemma_checkpoint_matches(value, marker); }
    let no_op = value.rollback(marker);
    proof {
        history::lemma_rollback_result(before_noop, value, marker, no_op);
        history::lemma_state_frame_facts(before_noop, value);
        history::lemma_checkpoint_owner_preserved(before_noop, value, marker);
        assert(no_op == Ok(()));
    }
    let ghost before_push = value;
    let push = value.push(event);
    proof {
        history::lemma_push_result(before_push, value, event, push);
        history::lemma_checkpoint_owner_preserved(before_push, value, marker);
    }
    push?;
    let ghost before_rollback = value;
    let rollback = value.rollback(marker);
    proof {
        history::lemma_rollback_result(before_rollback, value, marker, rollback);
        assert(rollback == Ok(()));
    }
    Ok(value)
}

// The explicit numeric boundary is separate from the typed lifecycle reachability invariant.
fn revision_exhaustion(events: Vec<history_store::store::Event>)
    requires events@.len() > 0,
{
    let mut stored = history::revision_boundary_record(17, events);
    let ghost before = stored;
    let exhausted = history::truncate_boundary_record(&mut stored, 0);
    proof { history::lemma_stored_truncate_result_facts(before, stored, 0, exhausted); }
    assert(exhausted == Err(HistoryError::RevisionExhausted));
    assert(history::stored_events(&stored) == events@);
    assert(stored.spec_revision() == u64::MAX);
    assert(stored@ == before@ && stored.spec_id() == 17);
    let count = stored.len();
    let ghost before_noop = stored;
    let unchanged = history::truncate_boundary_record(&mut stored, count);
    proof { history::lemma_stored_truncate_result_facts(before_noop, stored, count, unchanged); }
    assert(unchanged == Ok(()));
    assert(history::stored_events(&stored) == history::stored_events(&before));
    assert(stored.spec_revision() == u64::MAX);
    assert(stored@ == before@ && stored.spec_id() == 17);
    let ghost before_max_noop = stored;
    let max_noop = history::truncate_boundary_record(&mut stored, usize::MAX);
    proof { history::lemma_stored_truncate_result_facts(before_max_noop, stored, usize::MAX, max_noop); }
    assert(max_noop == Ok(()));
    assert(history::stored_events(&stored) == events@);
    assert(stored.spec_revision() == u64::MAX);
    assert(stored@ == before@ && stored.spec_id() == 17);
}

fn byte_identity<L: Limits>(path: &[u8], different: &[u8], limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<(u64, u64, u64), HistoryError>)
    requires path@ != different@,
    ensures result matches Ok((first, again, other)) ==> first == again && first != other,
{
    let owner = HistoryStore::new(1);
    let store = history_store::store::borrow_numeric_owner(&owner);
    let (first, first_receipt) = store.intern_observed(Component(0), path, limits, world)?;
    let (again, again_receipt) = store.intern_observed(Component(0), path, limits, world)?;
    let (other, other_receipt) = store.intern_observed(Component(0), different, limits, world)?;
    proof {
        records::lemma_byte_binding_pair_facts(store, 0, path@, first, first_receipt@,
            path@, again, again_receipt@);
        records::lemma_byte_binding_pair_facts(store, 0, path@, first, first_receipt@,
            different@, other, other_receipt@);
        history_store::store::lemma_byte_binding_reuse(first_receipt.borrow(), again_receipt.borrow());
        history_store::store::lemma_byte_binding_separation(first_receipt.borrow(), other_receipt.borrow());
    }
    Ok((first, again, other))
}

// Releasing the first guard permits arbitrary intervening writers; only lifecycle facts survive.
fn retained_raw_observations<L: Limits>(arity: usize, events: &[history_store::store::Event],
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<(), HistoryError>)
    requires 1 <= arity <= MAX_ARITY,
{
    let owner = HistoryStore::new(arity);
    let store = history_store::store::borrow_numeric_owner(&owner);
    let handle = owner.new_history(limits, world)?;
    let record = store.history_record(&handle)?;
    let tracked previous;
    {
        let guard = record.read();
        let observed = guard.as_slice();
        let len = guard.len();
        let revision = guard.revision();
        proof {
            guard.lemma_observation();
            assert(records::events_view(observed@) == guard.snapshot_view().value().events);
            assert(len == guard.snapshot_view().value().events.len());
            assert(revision == guard.snapshot_view().value().revision);
            previous = guard.snapshot();
        }
    }
    let append = store.append(&handle, events, limits, world);
    proof {
        records::lemma_append_result_facts(store, handle, events@, append);
        if events@.len() > 0 && append is Ok {
            records::lemma_record_append_observed(handle, events@, append);
            assert(exists|before: history_store::history::StoredHistory, after: history_store::history::StoredHistory|
                records::record_transaction(handle, before, after)
                    && history::stored_events(&after) == history::stored_events(&before) + events@
                    && after.spec_revision() == before.spec_revision());
        }
    }
    let _ = append;
    let truncate = store.truncate(&handle, 1);
    proof {
        records::lemma_truncate_result_facts(store, handle, 1, truncate);
        records::lemma_record_truncate_observed(handle, 1, truncate);
    }
    let later = record.read();
    later.validate_snapshot(Tracked(&previous));
    assert(previous.value().revision <= later.snapshot_view().value().revision);
    assert(previous.value().revision == later.snapshot_view().value().revision ==>
        previous.value().events.is_prefix_of(later.snapshot_view().value().events));
    Ok(())
}

fn numeric_runtime_readiness<L: Limits>(bindings: &junco_core::kernel::Bindings,
    limits: &mut L, world: &mut ObservationWorld) -> Result<(), HistoryError>
    requires history_specs::event_wf(bindings@, bindings@.len()),
        1 <= bindings@.len() <= MAX_ARITY,
{
    let arity = bindings.arity();
    let owner = HistoryStore::new(arity);
    let store = history_store::store::borrow_numeric_owner(&owner);
    let handle = owner.new_history(limits, world)?;
    let record = store.history_record(&handle)?;
    let guard = record.read();
    let stored: &history_store::history::StoredHistory = &guard;
    let target = stored.len();
    let mut regexes = Vec::new();
    regexes.push(FlatRegex::All);
    let mut head = Vec::new();
    while head.len() < arity
        invariant head@.len() <= arity,
            forall|i: int| 0 <= i < head@.len() ==> head@[i] == FlatHead::<u64>::Bind,
        decreases arity - head@.len(),
    {
        head.push(FlatHead::<u64>::Bind);
    }
    let template = FlatPair {
        head,
        tests: Vec::new(), regexes, root: 0,
    };
    let mut state = RuleRuntime::new(&owner, &template, false, limits, world)?;
    let ghost constructed = state;
    proof {
        runtime::lemma_constructor_runtime_wf(state, owner, template);
        runtime::lemma_constructor_snapshot_compatible(state, owner, template, *stored);
        runtime::lemma_resume_requires(state, *bindings, *stored, target);
    }
    let mut cursor = state.resume_cursor(bindings, stored, target);
    proof { runtime::lemma_resume_can_advance(constructed, state, cursor, *bindings, *stored, target); }
    let ghost before = state;
    let ghost start = cursor;
    let answer = state.advance_cursor(&mut cursor, bindings, stored, target, target, limits, world);
    proof {
        runtime::lemma_advance_result_facts(before, state, start, cursor, *bindings, *stored, target, target, answer);
        runtime::lemma_runtime_frame_accepts(constructed, before, bindings@, stored@.events.take(target as int));
        assert(answer matches Ok(Some(accepted)) ==>
            accepted == runtime::runtime_accepts(constructed, bindings@, stored@.events.take(target as int)));
        assert(answer != Err(HistoryError::WrongHistoryOwner));
    }
    Ok(())
}
}
