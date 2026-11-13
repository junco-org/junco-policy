//! R5: the monitor's semantic state, atomic decisions, and committed-trace safety.
//! Resource ownership, compiled caches, revisions, and stores remain behind Validator::wf.

use crate::validator::{Decision, Validator};
use history_syntax::{Event, Rule};
use junco_core::error::HistoryError;
use junco_core::event::Request;
use junco_core::spec::semantics::{least_violation, policy_denies, rule_violated};
use vstd::prelude::*;

verus! {

/// The ordered source rules and committed real events of a monitor.
pub struct ValidatorView<E: Event> {
    /// Rules in diagnostic priority order.
    pub rules: Seq<Rule<E>>,
    /// Committed events, oldest first.
    pub history: Seq<E>,
}

impl<E: Event> Validator<E> {
    /// Opaque compiled/store invariant; public preservation and revealing lemmas accompany the API.
    pub closed spec fn wf(&self) -> bool {
        crate::validator::verify::validator_wf(*self)
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

/// A completed builder starts the monitor with its ordered rules and an empty history.
pub open spec fn finish_spec<E: Event>(rules: Seq<Rule<E>>, state: ValidatorView<E>) -> bool {
    state.rules == rules && state.history == Seq::<E>::empty()
}

/// Every committed event was permitted by every rule against its own strict prefix.
pub open spec fn trace_safe<E: Event>(state: ValidatorView<E>) -> bool {
    forall|j: int, i: int| 0 <= j < state.history.len() && 0 <= i < state.rules.len()
        ==> !#[trigger] rule_violated(state.rules[i], state.history[j], state.history.subrange(0, j))
}

}
