//! R5: the monitor's semantic state, atomic decisions, and committed-trace safety.
//! Resource ownership, compiled caches, revisions, and stores remain behind Validator::wf.

use crate::policy::PolicyDecision;
use crate::validator::{Decision, Validator};
use history_syntax::{Event, Rule};
use junco_core::error::HistoryError;
use junco_core::event::Request;
use junco_core::spec::hypotheses::monitor_hypotheses;
use junco_core::spec::semantics::{least_violation, policy_denies, rule_violated, rule_wf};
use vstd::prelude::*;

verus! {

/// The ordered source rules and committed real events of a monitor.
pub struct ValidatorView<E: Event> {
    /// Rules in diagnostic priority order.
    pub rules: Seq<Rule<E>>,
    /// Committed events, oldest first.
    pub history: Seq<E>,
}

impl<E: Event> View for Validator<E> {
    type V = ValidatorView<E>;

    closed spec fn view(&self) -> ValidatorView<E> {
        ValidatorView {
            rules: crate::compiled_rule::verify::compiled_sources(self.rules@),
            history: history_store::history::verify::raw_events(self.history),
        }
    }
}

impl<E: Event> Validator<E> {
    /// Opaque compiled/store invariant, including the safety of every committed prefix.
    pub closed spec fn wf(&self) -> bool {
        history_store::history::verify::history_wf(self.history)
            && crate::compiled_rule::verify::compiled_table_wf(self.rules@,
                history_store::history::verify::store_of(self.history))
            && (monitor_hypotheses::<E>() ==> trace_safe(self@)
                && forall|i: int| 0 <= i < self@.rules.len()
                    ==> rule_wf(#[trigger] self@.rules[i]))
    }
}

/// Public consequences of the opaque invariant, requiring no compiled-state accessors.
pub proof fn lemma_validator_wf<E: Event>(validator: Validator<E>)
    requires validator.wf(),
    ensures monitor_hypotheses::<E>() ==> trace_safe(validator@)
        && forall|i: int| 0 <= i < validator@.rules.len()
            ==> rule_wf(#[trigger] validator@.rules[i]),
{
    reveal(Validator::wf);
}

pub(crate) proof fn lemma_validator_representation<E: Event>(validator: Validator<E>)
    ensures validator@ == (ValidatorView {
            rules: crate::compiled_rule::verify::compiled_sources(validator.rules@),
            history: history_store::history::verify::raw_events(validator.history),
        }),
        validator.wf() <==> history_store::history::verify::history_wf(validator.history)
            && crate::compiled_rule::verify::compiled_table_wf(validator.rules@,
                history_store::history::verify::store_of(validator.history))
            && (monitor_hypotheses::<E>() ==> trace_safe(validator@)
                && forall|i: int| 0 <= i < validator@.rules.len()
                    ==> rule_wf(#[trigger] validator@.rules[i])),
{}

pub(crate) proof fn lemma_validator_wf_intro<E: Event>(validator: Validator<E>)
    requires history_store::history::verify::history_wf(validator.history),
        crate::compiled_rule::verify::compiled_table_wf(validator.rules@,
            history_store::history::verify::store_of(validator.history)),
        monitor_hypotheses::<E>() ==> trace_safe(validator@),
        monitor_hypotheses::<E>() ==> forall|i: int| 0 <= i < validator@.rules.len()
            ==> rule_wf(#[trigger] validator@.rules[i]),
    ensures validator.wf(),
{}

/// Ordered selection shared by the monitor and both read-only policy facades.
pub open spec fn selected_rule<E: Event>(rules: Seq<Rule<E>>, history: Seq<E>,
    candidate: E, selected: Option<int>) -> bool {
    match selected {
        Some(index) => least_violation(rules, history, candidate, index),
        None => !policy_denies(rules, candidate, history),
    }
}

/// The executable first-violation query implements canonical ordered selection.
pub open spec fn selection_spec<E: Event>(rules: Seq<Rule<E>>, history: Seq<E>,
    candidate: E, result: Result<Option<usize>, HistoryError>) -> bool {
    match result {
        Ok(Some(index)) => selected_rule(rules, history, candidate, Some(index as int)),
        Ok(None) => selected_rule(rules, history, candidate, None),
        Err(error) => !(error is Invariant),
    }
}

/// Read-only policy decisions use the same least-source selection as `check_step`.
pub open spec fn policy_decision_spec<E: Event>(rules: Seq<Rule<E>>, history: Seq<E>,
    candidate: E, selected: int, result: Result<PolicyDecision, HistoryError>) -> bool {
    match result {
        Ok(PolicyDecision::Grant) => selected_rule(rules, history, candidate, None),
        Ok(PolicyDecision::Deny { .. }) => selected_rule(rules, history, candidate, Some(selected)),
        Err(error) => !(error is Invariant),
    }
}

/// Semantic frames retain source rules; private storage frames are maintained separately.
pub open spec fn validator_frame<E: Event>(before: ValidatorView<E>, after: ValidatorView<E>) -> bool {
    after.rules == before.rules
}

/// Grant appends exactly the permitted candidate; denial/error leave the history unchanged.
/// Denial selects the least violated rule; errors are never invariant failures (monitor theorem).
pub open spec fn check_step<E: Event, M>(before: ValidatorView<E>, after: ValidatorView<E>,
    request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>) -> bool {
    match result {
        Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
            && after.history == before.history.push(request.event)
            && !policy_denies(before.rules, request.event, before.history),
        Ok(Decision::Denied(denial)) => after.history == before.history && denial.event == request.event
            && exists|index: int| least_violation(before.rules, before.history, request.event, index)
                && denial.mode == before.rules[index].mode,
        Err(error) => after.history == before.history && !(error is Invariant),
    }
}

/// The read-only query reports exactly whether no source rule is violated.
pub open spec fn permits_spec<E: Event>(before: ValidatorView<E>, after: ValidatorView<E>,
    candidate: E, result: Result<bool, HistoryError>) -> bool {
    after.history == before.history && match result {
        Ok(permitted) => permitted == !policy_denies(before.rules, candidate, before.history),
        Err(error) => !(error is Invariant),
    }
}

/// A successful owned rollback restores a prefix; any error leaves the history unchanged.
pub open spec fn rollback_spec<E: Event>(before: ValidatorView<E>, after: ValidatorView<E>,
    prefix: Seq<E>, result: Result<(), HistoryError>) -> bool {
    match result {
        Ok(()) => prefix.is_prefix_of(before.history) && after.history == prefix,
        Err(error) => after.history == before.history && !(error is Invariant),
    }
}

/// Total prefix observation: future markers are rejected, so their unused prefix is the full trace.
pub open spec fn rollback_prefix<E: Event>(history: Seq<E>, length: usize) -> Seq<E> {
    if length <= history.len() { history.take(length as int) } else { history }
}

/// A completed builder starts the monitor with its ordered rules and an empty history.
pub open spec fn finish_spec<E: Event>(rules: Seq<Rule<E>>, state: ValidatorView<E>) -> bool {
    state.rules == rules && state.history == Seq::<E>::empty()
}

/// Rule registration appends one well-formed source on success and is atomic on error.
pub open spec fn add_rule_spec<E: Event>(before: Seq<Rule<E>>, after: Seq<Rule<E>>,
    source: Rule<E>, succeeded: bool) -> bool {
    if succeeded { after == before.push(source) && rule_wf(source) } else { after == before }
}

/// Every committed event was permitted by every rule against its own strict prefix.
pub open spec fn trace_safe<E: Event>(state: ValidatorView<E>) -> bool {
    forall|j: int, i: int| 0 <= j < state.history.len() && 0 <= i < state.rules.len()
        ==> !#[trigger] rule_violated(state.rules[i], state.history[j], state.history.subrange(0, j))
}

/// Appending a permitted event preserves the safety of every committed prefix.
pub proof fn lemma_trace_safe_append<E: Event>(before: ValidatorView<E>, candidate: E)
    requires trace_safe(before), !policy_denies(before.rules, candidate, before.history),
    ensures trace_safe(ValidatorView { rules: before.rules, history: before.history.push(candidate) }),
{
    let history = before.history.push(candidate);
    assert forall|j: int, i: int| 0 <= j < history.len() && 0 <= i < before.rules.len()
        implies !#[trigger] rule_violated(before.rules[i], history[j], history.subrange(0, j)) by {
        if j < before.history.len() {
            assert(history.subrange(0, j) =~= before.history.subrange(0, j));
        } else {
            assert(j == before.history.len());
            assert(history.subrange(0, j) =~= before.history);
        }
    }
}

/// Truncating a safe trace preserves safety, including after an owned rollback.
pub proof fn lemma_trace_safe_prefix<E: Event>(before: ValidatorView<E>, prefix: Seq<E>)
    requires trace_safe(before), prefix.is_prefix_of(before.history),
    ensures trace_safe(ValidatorView { rules: before.rules, history: prefix }),
{
    assert forall|j: int, i: int| 0 <= j < prefix.len() && 0 <= i < before.rules.len()
        implies !#[trigger] rule_violated(before.rules[i], prefix[j], prefix.subrange(0, j)) by {
        assert(prefix[j] == before.history[j]);
        assert(prefix.subrange(0, j) =~= before.history.subrange(0, j));
    }
}

/// The monitor step relation preserves committed-trace safety on every outcome.
pub proof fn lemma_check_step_trace_safe<E: Event, M>(before: ValidatorView<E>, after: ValidatorView<E>,
    request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>)
    requires trace_safe(before), validator_frame(before, after), check_step(before, after, request, result),
    ensures trace_safe(after),
{
    if let Ok(Decision::Grant(_)) = result {
        lemma_trace_safe_append(before, request.event);
    }
}

/// An owned-prefix rollback preserves committed-trace safety.
pub proof fn lemma_rollback_trace_safe<E: Event>(before: ValidatorView<E>, after: ValidatorView<E>,
    prefix: Seq<E>, result: Result<(), HistoryError>)
    requires trace_safe(before), validator_frame(before, after), rollback_spec(before, after, prefix, result),
    ensures trace_safe(after),
{
    if result is Ok { lemma_trace_safe_prefix(before, prefix); }
}

}
