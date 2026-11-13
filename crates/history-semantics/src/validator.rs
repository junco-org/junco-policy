//! Ordered authorization and append-on-grant request handling.
//!
//! Checked ordered selection composes the rule evaluator with atomic history transactions.
//! Numeric residual caches retain their existing native boundary.

use alloc::{borrow::ToOwned, string::String, sync::Arc, vec::Vec};

use crate::compiled_rule::CompiledRule;
#[cfg(verus_keep_ghost)]
use crate::compiled_rule::verify as compiled;
#[cfg(verus_keep_ghost)]
use crate::spec::monitor::{self, check_step, finish_spec, permits_spec, rollback_spec};
#[cfg(verus_keep_ghost)]
use history_store::history::verify as raw;
use history_store::history::{Checkpoint, History};
use history_store::typed::Store;
use history_syntax::Event;
use history_syntax::syntax::{Rule, RuleMode};
use junco_core::error::{CompileError, HistoryError};
use junco_core::event::{Grant, Request};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::{hypotheses::monitor_hypotheses, semantics};
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{no_internal_compile_error, no_invariant_failure};
use vstd::prelude::*;

/// Diagnostic returned when the first matching rule is violated.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial<E: Event> {
    /// Whether the violated rule required or forbade its tail language.
    pub mode: RuleMode,
    /// Candidate event that was denied and was not appended to history.
    pub event: E,
    /// Human-readable explanation of the failed history relation.
    pub message: String,
}

/// Result of checking one capability request.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<E: Event, M> {
    /// Request was accepted and appended to committed history.
    Grant(Grant<E, M>),
    /// Request was rejected atomically; committed history is unchanged.
    Denied(Denial<E>),
}

#[verus_verify]
impl<E: Event, M> Decision<E, M> {
    /// Returns `true` exactly for [`Decision::Grant`].
    #[verus_spec(result => ensures result == (self is Grant))]
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

/// Compiles an ordered rule set sharing one typed store.
#[verus_verify]
pub struct ValidatorBuilder<E: Event> {
    pub(crate) store: Arc<Store<E>>,
    pub(crate) rules: Vec<CompiledRule<E>>,
}

#[verus_verify]
impl<E: Event> ValidatorBuilder<E> {
    /// Creates an empty builder in `store`.
    #[verus_spec(result => requires history_store::typed::verify::store_wf(*store),
        ensures result.wf(), result.store_spec() == store,
            result@ == Seq::<Rule<E>>::empty())]
    pub fn new(store: Arc<Store<E>>) -> Self {
        Self {
            store,
            rules: Vec::new(),
        }
    }

    /// Compiles and appends one complete source rule.
    /// Native event laws exclude internal invariant failures, not resource errors.
    #[verus_spec(result => requires old(self).wf(),
        ensures monitor_hypotheses::<E>() ==> no_internal_compile_error(result),
            monitor_hypotheses::<E>() && semantics::rule_wf(source)
                ==> !(result matches Err(CompileError::HeadArity { .. }))
                    && !(result matches Err(CompileError::ComponentCoordinate { .. })),
            match result {
            Err(_) => final(self).wf()
                && builder_error_frame(*old(self), *final(self))
                && monitor::add_rule_spec(old(self)@, final(self)@, source, false),
            Ok(borrow) => mut_ref_current(borrow).wf()
                && mut_ref_current(borrow).store_spec() == old(self).store_spec()
                && mut_ref_current(borrow)@ == old(self)@.push(source)
                && (monitor_hypotheses::<E>() ==>
                    monitor::add_rule_spec(old(self)@, mut_ref_current(borrow)@, source, true))
                && mut_ref_future(borrow) == *final(self),
        })]
    pub fn add_rule(&mut self, source: Rule<E>) -> Result<&mut Self, CompileError> {
        proof_decl! { let ghost before = *self; let ghost supplied = source; }
        if ObservationWorld
            .try_reserve_vec(&mut self.rules, 1)
            .is_err()
        {
            source.dispose();
            return Err(HistoryError::AllocationFailed.into());
        }
        let runtime = CompiledRule::new(self.store.clone(), source)?;
        proof! { compiled::lemma_constructed_facts(runtime, supplied, self.store); }
        self.rules.push(runtime);
        proof! {
            assert(self@ =~= before@.push(supplied));
            assert forall|i: int| 0 <= i < self.rules@.len() implies
                crate::compiled_rule::compiled_wf(self.rules@[i])
                    && crate::compiled_rule::compiled_store(self.rules@[i]) == self.store by {
                if i < before.rules@.len() { assert(self.rules@[i] == before.rules@[i]); }
            }
        }
        Ok(self)
    }

    /// Creates the empty committed history in the rules' store.
    #[verus_spec(result => requires self.wf(),
        ensures monitor_hypotheses::<E>() ==> no_invariant_failure(result),
            result matches Ok(validator) ==> validator.wf()
                && finish_spec(self@, validator@)
                && finish_storage(self, validator))]
    pub fn finish(self) -> Result<Validator<E>, HistoryError> {
        proof! { self.lemma_wf(); }
        proof_decl! { let ghost builder = self; }
        let history = History::new(self.store)?;
        proof! { raw::lemma_empty_history(history, self.store); }
        let validator = Validator {
            rules: self.rules,
            history,
        };
        proof! {
            monitor::lemma_validator_representation(validator);
            assert(validator@.rules == builder@);
            monitor::lemma_validator_wf_intro(validator);
        }
        Ok(validator)
    }
}

/// Stateful validator for a fixed ordered rule set.
#[verus_verify]
pub struct Validator<E: Event> {
    pub(crate) rules: Vec<CompiledRule<E>>,
    pub(crate) history: History<E>,
}

#[verus_verify]
impl<E: Event> Validator<E> {
    /// Starts compiling a validator in `store`.
    #[verus_spec(result => requires history_store::typed::verify::store_wf(*store),
        ensures result.wf(), result.store_spec() == store,
            result@ == Seq::<Rule<E>>::empty())]
    pub fn builder(store: Arc<Store<E>>) -> ValidatorBuilder<E> {
        ValidatorBuilder::new(store)
    }

    /// Authorizes a request, appending its exact event only after successful evaluation.
    /// Native event laws exclude internal invariant failures while retaining resource errors.
    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(), storage_frame(*old(self), *final(self)),
            monitor::validator_frame(old(self)@, final(self)@),
            check_storage(*old(self), *final(self), request, result),
            monitor_hypotheses::<E>() ==> check_step(old(self)@, final(self)@, request, result),
            monitor_hypotheses::<E>() ==> no_invariant_failure(result))]
    pub fn check<M>(&mut self, request: Request<E, M>) -> Result<Decision<E, M>, HistoryError> {
        self.check_with(request, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(), storage_frame(*old(self), *final(self)),
            monitor::validator_frame(old(self)@, final(self)@),
            check_storage(*old(self), *final(self), request, result),
            monitor_hypotheses::<E>() ==> check_step(old(self)@, final(self)@, request, result),
            monitor_hypotheses::<E>() ==> no_invariant_failure(result))]
    fn check_with<M, L: Limits>(
        &mut self,
        request: Request<E, M>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Decision<E, M>, HistoryError> {
        proof! { monitor::lemma_validator_representation(*self);     }
        proof_decl! { let ghost entry = *self; }
        proof! { history_store::history::verify::lemma_history_frame_facts(entry.history, entry.history); }
        if let Some(index) = self.first_violation_with(&request.event, limits, world)? {
            let mode = self.rules[index].mode();
            let message = match mode {
                RuleMode::Require => {
                    "committed history does not satisfy required past-regex rule".to_owned()
                }
                RuleMode::Forbid => {
                    "committed history satisfies forbidden past-regex rule".to_owned()
                }
            };
            proof! {
                monitor::lemma_validator_representation(*self);
                crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
                crate::compiled_rule::verify::lemma_compiled_mode_frame(entry.rules@, self.rules@, index as int);
                if monitor_hypotheses::<E>() {
                    crate::compiled_rule::verify::lemma_compiled_source_mode(self.rules@[index as int], mode);
                }
            }
            let denial = Denial {
                mode,
                event: request.event,
                message,
            };
            proof! {
                assert(monitor_hypotheses::<E>() ==>
                    semantics::least_violation(entry@.rules, entry@.history, request.event, index as int));
            }
            return Ok(Decision::Denied(denial));
        }
        proof! { monitor::lemma_validator_representation(*self); }
        let appended = self.history.push_with(request.event, limits, world);
        proof! {
            monitor::lemma_validator_representation(*self);
            history_store::history::verify::lemma_push_result(entry.history, self.history, request.event, appended);
            raw::lemma_history_frame_facts(entry.history, self.history);
            if monitor_hypotheses::<E>() && appended is Ok {
                monitor::lemma_trace_safe_append(entry@, request.event);
            }
            monitor::lemma_validator_wf_intro(*self);
            assert(storage_frame(entry, *self));
        }
        appended?;
        Ok(Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        }))
    }

    /// Evaluates without appending; retained residuals fold only newly committed events.
    /// Operational errors cannot be internal invariant failures.
    /// Structural compiled readiness excludes invariant failures without native event laws;
    /// those laws are needed only to identify this read-only answer with source semantics.
    #[verus_spec(result => requires old(self).wf(),
        ensures no_invariant_failure(result), final(self).wf(),
            storage_frame(*old(self), *final(self)),
            monitor::validator_frame(old(self)@, final(self)@),
            final(self)@.history == old(self)@.history,
            history_state_frame(*old(self), *final(self)),
            monitor_hypotheses::<E>() ==> permits_spec(old(self)@, final(self)@, *candidate, result))]
    pub fn permits(&mut self, candidate: &E) -> Result<bool, HistoryError> {
        proof! { monitor::lemma_validator_representation(*self);     }
        proof! { history_store::history::verify::lemma_history_frame_facts(self.history, self.history); }
        Ok(self.first_violation(candidate)?.is_none())
    }

    #[verus_spec(result => requires old(self).wf(),
        ensures no_invariant_failure(result), final(self).wf(),
            storage_frame(*old(self), *final(self)), final(self).history == old(self).history,
            monitor::validator_frame(old(self)@, final(self)@),
            final(self)@.history == old(self)@.history, history_state_frame(*old(self), *final(self)),
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            monitor_hypotheses::<E>() ==> monitor::selection_spec(old(self)@.rules, old(self)@.history, *candidate, result))]
    fn first_violation(&mut self, candidate: &E) -> Result<Option<usize>, HistoryError> {
        self.first_violation_with(candidate, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires old(self).wf(),
        ensures no_invariant_failure(result), final(self).wf(),
            storage_frame(*old(self), *final(self)), final(self).history == old(self).history,
            monitor::validator_frame(old(self)@, final(self)@),
            final(self)@.history == old(self)@.history, history_state_frame(*old(self), *final(self)),
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            monitor_hypotheses::<E>() ==> monitor::selection_spec(old(self)@.rules, old(self)@.history, *candidate, result))]
    fn first_violation_with<L: Limits>(
        &mut self,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<usize>, HistoryError> {
        proof! { monitor::lemma_validator_representation(*self);     }
        proof_decl! { let ghost entry = *self; }
        proof! {
            raw::lemma_history_frame_facts(entry.history, entry.history);
            compiled::lemma_compiled_table_reflexive(entry.rules@, raw::store_of(entry.history));
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= self.rules@.len(), self.wf(), storage_frame(entry, *self),
            entry.wf(), history_state_frame(entry, *self),
            monitor::validator_frame(entry@, self@), self@.history == entry@.history,
            entry@.rules == compiled::compiled_sources(entry.rules@),
            entry@.history == raw::raw_events(entry.history),
            entry == *old(self), self.history == entry.history,
            monitor_hypotheses::<E>() ==>
                forall|j: int| 0 <= j < index ==> !semantics::rule_violated(
                    entry@.rules[j], *candidate, entry@.history),
            decreases self.rules@.len() - index))]
        while index < self.rules.len() {
            proof! {
                monitor::lemma_validator_representation(entry);
                monitor::lemma_validator_representation(*self);
                compiled::lemma_decision_requires(self.rules@[index as int], self.history);
            }
            proof_decl! { let ghost before = *self; }
            let rule = &mut self.rules[index];
            let answer = rule.accepts_history_with_limits(&self.history, candidate, limits, world);
            let mode = rule.mode();
            proof! {
                compiled::lemma_decision_result_facts(before.rules@[index as int], *rule,
                    self.history, *candidate, answer);
                if monitor_hypotheses::<E>() {
                    crate::compiled_rule::verify::lemma_dsl_violation(*rule, self.history, *candidate, answer, mode);
                }
                assert forall|j: int| 0 <= j < entry.rules@.len() implies
                    crate::compiled_rule::compiled_structure_frame(entry.rules@[j], self.rules@[j]) by {
                    if j != index as int {
                        assert(self.rules@[j] == before.rules@[j]);
                    } else {
                        compiled::lemma_compiled_frame_transitive(entry.rules@[j], before.rules@[j], self.rules@[j]);
                    }
                }
                compiled::lemma_compiled_table_frame_facts(entry.rules@, self.rules@, raw::store_of(entry.history));
                monitor::lemma_validator_representation(*self);
                raw::lemma_history_frame_facts(self.history, self.history);
                monitor::lemma_validator_wf_intro(*self);
                assert(storage_frame(entry, *self));
            }
            let violated = match answer? {
                None => false,
                Some(inside) => match mode {
                    RuleMode::Require => !inside,
                    RuleMode::Forbid => inside,
                },
            };
            if violated {
                return Ok(Some(index));
            }
            index += 1;
        }
        proof! {
            monitor::lemma_validator_representation(entry);
            monitor::lemma_validator_representation(*self);
        }
        Ok(None)
    }

    /// Returns committed grants' events in exact acceptance order.
    #[verus_spec(result => ensures result@ == self@.history)]
    pub fn history(&self) -> &[E] {
        proof! { monitor::lemma_validator_representation(*self);     }
        self.history.as_slice()
    }

    /// Captures the current committed-history position.
    #[verus_spec(result => ensures self.checkpoint_owned(result),
        history_store::history::verify::checkpoint_len(result) == self@.history.len())]
    pub fn checkpoint(&self) -> Checkpoint {
        proof! { monitor::lemma_validator_representation(*self);      }
        let checkpoint = self.history.checkpoint();
        proof! { raw::lemma_checkpoint_matches(self.history, checkpoint); }
        checkpoint
    }

    /// Rolls back a checkpoint belonging to this validator's history.
    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(), storage_frame(*old(self), *final(self)),
            monitor::validator_frame(old(self)@, final(self)@),
            rollback_spec(old(self)@, final(self)@,
                monitor::rollback_prefix(old(self)@.history, raw::checkpoint_len(checkpoint)), result),
            rollback_storage(*old(self), *final(self), checkpoint, result))]
    pub fn rollback(&mut self, checkpoint: Checkpoint) -> Result<(), HistoryError> {
        proof! { monitor::lemma_validator_representation(*self);     }
        proof_decl! { let ghost entry = *self; }
        let result = self.history.rollback(checkpoint);
        proof! {
            history_store::history::verify::lemma_rollback_result(entry.history, self.history, checkpoint, result);
            raw::lemma_history_frame_facts(entry.history, self.history);
            if raw::checkpoint_owned(entry.history, checkpoint)
                && raw::checkpoint_len(checkpoint) <= entry@.history.len() {
                raw::lemma_truncate_result(entry.history, self.history, raw::checkpoint_len(checkpoint), result);
            } else {
                assert(result is Err);
            }
            assert(no_invariant_failure(result));
            compiled::lemma_compiled_table_reflexive(entry.rules@, raw::store_of(entry.history));
            compiled::lemma_compiled_sources_frame(entry.rules@, self.rules@);
            monitor::lemma_validator_representation(*self);
            let prefix = monitor::rollback_prefix(entry@.history, raw::checkpoint_len(checkpoint));
            if result is Ok {
                assert(self@.history =~= prefix);
                assert(prefix.is_prefix_of(entry@.history));
                if monitor_hypotheses::<E>() { monitor::lemma_trace_safe_prefix(entry@, prefix); }
            }
            monitor::lemma_validator_wf_intro(*self);
            assert(storage_frame(entry, *self));
            assert(rollback_spec(entry@, self@, prefix, result));
        }
        result
    }
}

impl<E: Event> Validator<E> {
    /// Resets the existing per-rule numeric event-work counters.
    #[cfg(feature = "test-util")]
    pub fn reset_work_events(&mut self) {
        for rule in &mut self.rules {
            rule.reset_work_events();
        }
    }

    /// Returns the saturating sum of existing per-rule numeric event-work counters.
    #[cfg(feature = "test-util")]
    pub fn work_events(&self) -> usize {
        self.rules.iter().fold(0usize, |total, rule| {
            total.saturating_add(rule.work_events())
        })
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl<E: Event> View for ValidatorBuilder<E> {
    type V = Seq<Rule<E>>;
    closed spec fn view(&self) -> Seq<Rule<E>> {
        compiled::compiled_sources(self.rules@)
    }
}

impl<E: Event> ValidatorBuilder<E> {
    /// Opaque compilation invariant for the ordered source builder.
    pub closed spec fn wf(&self) -> bool {
        compiled::compiled_table_wf(self.rules@, self.store)
    }
    /// The shared native store, not part of the source-rule view.
    pub closed spec fn store_spec(&self) -> Arc<Store<E>> { self.store }

    /// Public invariant facts expose only source well-formedness and store readiness.
    pub proof fn lemma_wf(&self)
        requires self.wf(),
        ensures history_store::typed::verify::store_wf(*self.store_spec()),
            monitor_hypotheses::<E>() ==> forall|i: int| 0 <= i < self@.len()
                ==> semantics::rule_wf(#[trigger] self@[i]),
    {
        assert forall|i: int| 0 <= i < self@.len() implies
            monitor_hypotheses::<E>() ==> semantics::rule_wf(#[trigger] self@[i]) by {
            compiled::lemma_compiled_wf_facts(self.rules@[i]);
        }
    }
}

impl<E: Event> Validator<E> {
    /// Whether a checkpoint belongs to this validator's committed history.
    pub closed spec fn checkpoint_owned(&self, checkpoint: Checkpoint) -> bool {
        raw::checkpoint_owned(self.history, checkpoint)
    }
}

/// A failed registration retains every compiled entry and the builder's store.
pub closed spec fn builder_error_frame<E: Event>(before: ValidatorBuilder<E>, after: ValidatorBuilder<E>) -> bool {
    after.store == before.store && after.rules@ == before.rules@
}

/// Finishing initializes the same native owner and zero-revision empty history.
pub closed spec fn finish_storage<E: Event>(builder: ValidatorBuilder<E>, validator: Validator<E>) -> bool {
    raw::empty_history(validator.history, builder.store)
}

/// Compiled entries retain their source, owner, mode and template; history retains its owner.
pub closed spec fn storage_frame<E: Event>(before: Validator<E>, after: Validator<E>) -> bool {
    compiled::compiled_table_frame(before.rules@, after.rules@)
        && raw::owner_frame(before.history, after.history)
}

/// A read-only operation retains events, encodings, revision and owner receipts.
pub closed spec fn history_state_frame<E: Event>(before: Validator<E>, after: Validator<E>) -> bool {
    raw::state_frame(before.history, after.history)
}

/// Atomic publication and exact denial diagnostics, independently of event-law hypotheses.
pub closed spec fn check_storage<E: Event, M>(before: Validator<E>, after: Validator<E>,
    request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>) -> bool {
    match result {
        Err(_) => raw::state_frame(before.history, after.history),
        Ok(Decision::Denied(denial)) => denial.event == request.event
            && raw::state_frame(before.history, after.history)
            && exists|index: int| 0 <= index < before.rules@.len()
                && denial.mode == before.rules@[index].mode_spec()
            && denial.message@ == match denial.mode {
                RuleMode::Require => "committed history does not satisfy required past-regex rule"@,
                RuleMode::Forbid => "committed history satisfies forbidden past-regex rule"@,
            },
        Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
            && raw::push_result(before.history, after.history, request.event, Ok(())),
    }
}

/// Owned checkpoint rollback retains the encoding map and exact revision/error behavior.
pub closed spec fn rollback_storage<E: Event>(before: Validator<E>, after: Validator<E>,
    checkpoint: Checkpoint, result: Result<(), HistoryError>) -> bool {
    raw::rollback_result(before.history, after.history, checkpoint, result)
}
}

/// Storage-only facts are opaque; source decisions live exclusively in R5.
#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use crate::compiled_rule::verify as compiled;
    use history_store::history::verify as raw;
    verus! {










    /// Native initialization facts for internal constructor clients.
    pub(crate) proof fn lemma_finish_storage<E: Event>(builder: ValidatorBuilder<E>, state: Validator<E>)
        requires state.wf(), finish_storage(builder, state),
        ensures raw::history_wf(state.history),
            raw::empty_history(state.history, builder.store_spec()),
            state@.history == Seq::<E>::empty(),
    {
        monitor::lemma_validator_representation(state);
        raw::lemma_empty_history(state.history, builder.store_spec());
    }

    /// Public elimination of atomicity and diagnostics without exposing history storage.
    pub proof fn lemma_check_storage<E: Event, M>(before: Validator<E>, after: Validator<E>,
        request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>)
        requires check_storage(before, after, request, result),
        ensures match result {
            Err(_) => after@.history == before@.history,
            Ok(Decision::Denied(denial)) => after@.history == before@.history
                && denial.event == request.event
                && denial.message@ == match denial.mode {
                    RuleMode::Require => "committed history does not satisfy required past-regex rule"@,
                    RuleMode::Forbid => "committed history satisfies forbidden past-regex rule"@,
                },
            Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
                && after@.history == before@.history.push(request.event),
        },
    {
        monitor::lemma_validator_representation(before); monitor::lemma_validator_representation(after);
        raw::lemma_history_frame_facts(before.history, after.history);
        if let Ok(Decision::Grant(_)) = result {
            raw::lemma_push_result(before.history, after.history, request.event, Ok(()));
        }
    }

    /// Failure-atomic registration also retains its public source-rule sequence.
    pub proof fn lemma_builder_error_frame<E: Event>(before: ValidatorBuilder<E>, after: ValidatorBuilder<E>)
        requires builder_error_frame(before, after),
        ensures after@ == before@, after.store_spec() == before.store_spec(),
    {

    }

    /// Storage preservation exposes the semantic rule frame, but not compiled representations.
    pub proof fn lemma_storage_frame<E: Event>(before: Validator<E>, after: Validator<E>)
        requires storage_frame(before, after),
        ensures monitor::validator_frame(before@, after@),
    {
        monitor::lemma_validator_representation(before); monitor::lemma_validator_representation(after);
        compiled::lemma_compiled_sources_frame(before.rules@, after.rules@);
    }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use history_syntax::{
        AtomPattern, Comparison, Component, Component3, ComponentPattern as P, Head, N3,
        RegexExpr as R, TestExpr as T,
    };
    use junco_core::limits::LimitError;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Document {
        principal: u8,
        action: u8,
        resource: u8,
        payload: u16,
    }
    impl Event for Document {
        type Component = Component3<u8, u8, u8>;
        type Arity = N3;

        fn component(self, index: usize) -> Self::Component {
            match index {
                0 => Component3::C0(self.principal),
                1 => Component3::C1(self.action),
                _ => Component3::C2(self.resource),
            }
        }

        fn coordinate(component: Self::Component) -> usize {
            match component {
                Component3::C0(_) => 0,
                Component3::C1(_) => 1,
                Component3::C2(_) => 2,
            }
        }
    }
    fn edit() -> Document {
        Document {
            principal: 7,
            action: 1,
            resource: 9,
            payload: 42,
        }
    }
    fn release() -> Document {
        Document {
            action: 2,
            payload: 21,
            ..edit()
        }
    }
    fn store() -> Arc<Store<Document>> {
        Arc::new(Store::new().unwrap())
    }
    fn any_head() -> Head<Document> {
        Head::new([
            P::variable("principal"),
            P::variable("action"),
            P::variable("resource"),
        ])
    }
    fn prior_edit() -> Rule<Document> {
        Rule::new(
            RuleMode::Require,
            Head::new([
                P::variable("actor"),
                P::constant(Component3::C1(2)),
                P::variable("resource"),
            ]),
            R::concat([
                R::all(),
                R::test(T::and([
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(0), P::variable("actor")),
                    ),
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(1), P::constant(Component3::C1(1))),
                    ),
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(2), P::variable("resource")),
                    ),
                ])),
                R::all(),
            ]),
        )
    }

    #[test]
    fn grants_preserve_event_metadata_and_append_exactly_once() {
        let mut builder = Validator::builder(store());
        builder.add_rule(prior_edit()).unwrap();
        let mut validator = builder.finish().unwrap();
        assert!(
            validator
                .check(Request::new(edit(), ()))
                .unwrap()
                .is_grant()
        );
        assert_eq!(validator.history(), &[edit()]);
        let checkpoint = validator.checkpoint();
        let metadata = alloc::vec![3u8, 1, 4];
        let Decision::Grant(grant) = validator
            .check(Request::new(release(), metadata.clone()))
            .unwrap()
        else {
            panic!("matching prior edit must grant")
        };
        assert_eq!(grant.event, release());
        assert_eq!(grant.metadata, metadata);
        assert_eq!(validator.history(), &[edit(), release()]);
        let other = Document {
            principal: 8,
            ..release()
        };
        assert!(
            matches!(validator.check(Request::new(other, ())).unwrap(), Decision::Denied(Denial { mode: RuleMode::Require, event, .. }) if event == other)
        );
        assert_eq!(validator.history(), &[edit(), release()]);
        assert!(validator.permits(&release()).unwrap());
        assert_eq!(validator.history(), &[edit(), release()]);
        validator.rollback(checkpoint).unwrap();
        assert_eq!(validator.history(), &[edit()]);
    }

    #[test]
    fn first_violation_order_and_empty_tables_are_preserved() {
        for first in [RuleMode::Require, RuleMode::Forbid] {
            let mut builder = Validator::builder(store());
            for mode in [
                first,
                if first == RuleMode::Require {
                    RuleMode::Forbid
                } else {
                    RuleMode::Require
                },
            ] {
                builder
                    .add_rule(Rule::new(
                        mode,
                        any_head(),
                        if mode == RuleMode::Require {
                            R::empty()
                        } else {
                            R::all()
                        },
                    ))
                    .unwrap();
            }
            let mut validator = builder.finish().unwrap();
            assert!(
                matches!(validator.check(Request::new(release(), ())).unwrap(), Decision::Denied(Denial { mode, .. }) if mode == first)
            );
            assert!(validator.history().is_empty());
        }
        let mut empty = Validator::<Document>::builder(store()).finish().unwrap();
        assert!(empty.permits(&release()).unwrap());
        assert!(empty.check(Request::new(release(), ())).unwrap().is_grant());
        assert_eq!(empty.history(), &[release()]);
    }

    #[test]
    fn append_allocation_error_is_not_a_denial_or_a_grant() {
        let mut validator = Validator::<Document>::builder(store()).finish().unwrap();
        let _failure = junco_core::observation::fail_reservations_after(0);
        assert!(matches!(
            validator.check(Request::new(edit(), ())),
            Err(HistoryError::AllocationFailed)
        ));
        assert!(validator.history().is_empty());
    }

    struct PublicationFailure;
    impl Limits for PublicationFailure {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Err(LimitError::RegexSizeLimitExceeded { limit: 0 })
        }
    }

    #[test]
    fn evaluation_error_does_not_append_or_become_a_denial() {
        let mut builder = Validator::builder(store());
        builder
            .add_rule(Rule::new(RuleMode::Require, any_head(), R::epsilon()))
            .unwrap();
        let mut validator = builder.finish().unwrap();
        assert!(matches!(
            validator.check_with(
                Request::new(release(), ()),
                &mut PublicationFailure,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert!(validator.history().is_empty());
    }

    #[test]
    fn failed_builder_reservation_drains_a_deep_owned_rule() {
        let mut tail = R::<Document>::epsilon();
        for _ in 0..4096 {
            tail = R::star(tail);
        }
        let source = Rule::new(RuleMode::Require, any_head(), tail);
        let mut builder = Validator::builder(store());
        {
            let _failure = junco_core::observation::fail_reservations_after(0);
            assert!(matches!(
                builder.add_rule(source),
                Err(CompileError::Runtime(HistoryError::AllocationFailed))
            ));
        }
        assert!(builder.finish().unwrap().permits(&release()).unwrap());
    }
}
