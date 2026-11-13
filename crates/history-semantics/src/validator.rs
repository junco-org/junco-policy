//! Ordered authorization and append-on-grant request handling.
//!
//! Checked ordered selection composes the rule evaluator with atomic history transactions.
//! Numeric residual caches retain their existing native boundary.

use alloc::{borrow::ToOwned, string::String, sync::Arc, vec::Vec};

use crate::compiled_rule::CompiledRule;
use history_store::history::{Checkpoint, History};
use history_store::typed::Store;
use history_syntax::Event;
use history_syntax::syntax::{Rule, RuleMode};
use junco_core::error::{CompileError, HistoryError};
use junco_core::event::{Grant, Request};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics as sem;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{no_invariant_compile_failure, no_invariant_failure};
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
        ensures verify::builder_wf(result), verify::builder_store(result) == store,
            verify::builder_sources(result) == Seq::<Rule<E>>::empty())]
    pub fn new(store: Arc<Store<E>>) -> Self {
        Self {
            store,
            rules: Vec::new(),
        }
    }

    /// Compiles and appends one complete source rule.
    /// Native event laws exclude internal invariant failures, not resource errors.
    #[verus_spec(result => requires verify::builder_wf(*old(self)),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            match result {
            Err(_) => verify::builder_wf(*final(self))
                && verify::builder_store(*final(self)) == verify::builder_store(*old(self))
                && verify::builder_rules(*final(self)) == verify::builder_rules(*old(self)),
            Ok(borrow) => verify::builder_wf(mut_ref_current(borrow))
                && verify::builder_store(mut_ref_current(borrow)) == verify::builder_store(*old(self))
                && verify::builder_sources(mut_ref_current(borrow)) == verify::builder_sources(*old(self)).push(source)
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
        self.rules.push(runtime);
        proof! {
            assert(verify::builder_sources(*self) =~= verify::builder_sources(before).push(supplied));
            assert forall|i: int| 0 <= i < self.rules@.len() implies
                crate::compiled_rule::verify::compiled_wf(self.rules@[i]) && self.rules@[i].store == self.store by {
                if i < before.rules@.len() { assert(self.rules@[i] == before.rules@[i]); }
            }
        }
        Ok(self)
    }

    /// Creates the empty committed history in the rules' store.
    #[verus_spec(result => requires verify::builder_wf(self),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_failure(result),
            result matches Ok(validator) ==> verify::validator_wf(validator)
            && verify::validator_sources(validator) == verify::builder_sources(self)
            && history_store::history::verify::empty_history(verify::validator_history(validator), verify::builder_store(self)))]
    pub fn finish(self) -> Result<Validator<E>, HistoryError> {
        let history = History::new(self.store)?;
        proof! { history_store::history::verify::lemma_empty_history(history, self.store); }
        Ok(Validator {
            rules: self.rules,
            history,
        })
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
        ensures verify::builder_wf(result), verify::builder_store(result) == store,
            verify::builder_sources(result) == Seq::<Rule<E>>::empty())]
    pub fn builder(store: Arc<Store<E>>) -> ValidatorBuilder<E> {
        ValidatorBuilder::new(store)
    }

    /// Authorizes a request, appending its exact event only after successful evaluation.
    /// Native event laws exclude internal invariant failures while retaining resource errors.
    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures verify::check_result(*old(self), *final(self), request, result),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_failure(result))]
    pub fn check<M>(&mut self, request: Request<E, M>) -> Result<Decision<E, M>, HistoryError> {
        self.check_with(request, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures verify::check_result(*old(self), *final(self), request, result),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_failure(result))]
    fn check_with<M, L: Limits>(
        &mut self,
        request: Request<E, M>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Decision<E, M>, HistoryError> {
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
                crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
                crate::compiled_rule::verify::lemma_compiled_mode_frame(entry.rules@, self.rules@, index as int);
                if junco_core::spec::hypotheses::event_obligations::<E>() {
                    crate::compiled_rule::verify::lemma_compiled_source_mode(self.rules@[index as int], mode);
                }
            }
            let denial = Denial {
                mode,
                event: request.event,
                message,
            };
            proof! { assert(verify::denial_at(entry, request, denial, index as int)); }
            return Ok(Decision::Denied(denial));
        }
        let appended = self.history.push_with(request.event, limits, world);
        proof! {
            history_store::history::verify::lemma_push_result(entry.history, self.history, request.event, appended);
            assert(verify::validator_wf(*self));
            assert(verify::validator_frame(entry, *self));
        }
        appended?;
        Ok(Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        }))
    }

    /// Evaluates without appending; retained residuals fold only newly committed events.
    /// Operational errors cannot be internal invariant failures.
    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures no_invariant_failure(result),
            verify::validator_frame(*old(self), *final(self)),
            history_store::history::verify::state_frame(verify::validator_history(*old(self)), verify::validator_history(*final(self))),
            result matches Ok(permitted) ==> (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                permitted == (forall|i: int| 0 <= i < verify::validator_sources(*old(self)).len() ==>
                    !sem::rule_violated(verify::validator_sources(*old(self))[i]@, *candidate,
                        history_store::history::verify::raw_events(verify::validator_history(*old(self)))))))]
    pub fn permits(&mut self, candidate: &E) -> Result<bool, HistoryError> {
        proof! { history_store::history::verify::lemma_history_frame_facts(self.history, self.history); }
        Ok(self.first_violation(candidate)?.is_none())
    }

    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures no_invariant_failure(result),
            verify::validator_frame(*old(self), *final(self)), final(self).history == old(self).history,
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            crate::compiled_rule::verify::ordered_result(verify::validator_sources(*old(self)), old(self).history, *candidate, result))]
    fn first_violation(&mut self, candidate: &E) -> Result<Option<usize>, HistoryError> {
        self.first_violation_with(candidate, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures no_invariant_failure(result),
            verify::validator_frame(*old(self), *final(self)), final(self).history == old(self).history,
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            crate::compiled_rule::verify::ordered_result(verify::validator_sources(*old(self)), old(self).history, *candidate, result))]
    fn first_violation_with<L: Limits>(
        &mut self,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<usize>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        proof! { history_store::history::verify::lemma_history_frame_facts(entry.history, entry.history); }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= self.rules@.len(), verify::validator_wf(*self), verify::validator_frame(entry, *self),
            entry == *old(self), self.history == entry.history,
            junco_core::spec::hypotheses::event_obligations::<E>() ==>
                forall|j: int| 0 <= j < index ==> !sem::rule_violated(
                    verify::validator_sources(entry)[j]@, *candidate, history_store::history::verify::raw_events(entry.history)),
            decreases self.rules@.len() - index))]
        while index < self.rules.len() {
            proof_decl! { let ghost before = *self; }
            let rule = &mut self.rules[index];
            let answer = rule.accepts_history_with_limits(&self.history, candidate, limits, world);
            let mode = rule.mode();
            proof! {
                if junco_core::spec::hypotheses::event_obligations::<E>() {
                    crate::compiled_rule::verify::lemma_dsl_violation(*rule, self.history, *candidate, answer, mode);
                }
                assert forall|j: int| 0 <= j < entry.rules@.len() implies
                    crate::compiled_rule::verify::compiled_structure_frame(entry.rules@[j], self.rules@[j]) by {
                    if j != index as int { assert(self.rules@[j] == before.rules@[j]); }
                }
                crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
                assert(verify::validator_wf(*self));
                assert(verify::validator_frame(entry, *self));
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
        Ok(None)
    }

    /// Returns committed grants' events in exact acceptance order.
    #[verus_spec(result => ensures result@ == history_store::history::verify::raw_events(verify::validator_history(*self)))]
    pub fn history(&self) -> &[E] {
        self.history.as_slice()
    }

    /// Captures the current committed-history position.
    #[verus_spec(result => ensures history_store::history::verify::checkpoint_matches(verify::validator_history(*self), result))]
    pub fn checkpoint(&self) -> Checkpoint {
        self.history.checkpoint()
    }

    /// Rolls back a checkpoint belonging to this validator's history.
    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures verify::validator_frame(*old(self), *final(self)),
            history_store::history::verify::rollback_result(verify::validator_history(*old(self)), verify::validator_history(*final(self)), checkpoint, result))]
    pub fn rollback(&mut self, checkpoint: Checkpoint) -> Result<(), HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let result = self.history.rollback(checkpoint);
        proof! {
            history_store::history::verify::lemma_rollback_result(entry.history, self.history, checkpoint, result);
            crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
            assert(verify::validator_wf(*self));
            assert(verify::validator_frame(entry, *self));
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

/// Ordered rule and transaction predicates, derived from the actual compiled entries.
#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use crate::compiled_rule::verify as compiled;
    use history_store::history::verify as raw;
    use history_store::typed::verify as books;
    verus! {
    pub open(crate) spec fn builder_store<E: Event>(builder: ValidatorBuilder<E>) -> Arc<Store<E>> { builder.store }
    pub open(crate) spec fn builder_rules<E: Event>(builder: ValidatorBuilder<E>) -> Seq<CompiledRule<E>> { builder.rules@ }
    pub open(crate) spec fn builder_sources<E: Event>(builder: ValidatorBuilder<E>) -> Seq<Rule<E>> {
        compiled::compiled_sources(builder.rules@)
    }
    pub open(crate) spec fn builder_wf<E: Event>(builder: ValidatorBuilder<E>) -> bool {
        compiled::compiled_table_wf(builder.rules@, builder.store)
    }
    pub open(crate) spec fn validator_history<E: Event>(validator: Validator<E>) -> History<E> { validator.history }
    pub open(crate) spec fn validator_sources<E: Event>(validator: Validator<E>) -> Seq<Rule<E>> {
        compiled::compiled_sources(validator.rules@)
    }
    pub open(crate) spec fn validator_wf<E: Event>(validator: Validator<E>) -> bool {
        raw::history_wf(validator.history)
            && compiled::compiled_table_wf(validator.rules@, raw::store_of(validator.history))
    }

    /// Exposes the committed history's public invariant without exposing the rule table.
    pub proof fn lemma_validator_wf<E: Event>(validator: Validator<E>)
        requires validator_wf(validator),
        ensures raw::history_wf(validator_history(validator)),
            books::store_wf(*raw::store_of(validator_history(validator))),
    {
        raw::lemma_history_frame_facts(validator.history, validator.history);
    }
    pub open(crate) spec fn validator_frame<E: Event>(before: Validator<E>, after: Validator<E>) -> bool {
        validator_wf(after) && compiled::compiled_table_frame(before.rules@, after.rules@)
            && validator_sources(after) == validator_sources(before)
            && raw::owner_frame(before.history, after.history)
    }
    pub open(crate) spec fn denial_at<E: Event, M>(before: Validator<E>, request: Request<E,M>, denial: Denial<E>, index: int) -> bool {
        0 <= index < before.rules@.len() && denial.mode == before.rules@[index].mode_spec()
            && denial.event == request.event
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> denial.mode == validator_sources(before)[index].mode
                && sem::least_violation(sem::rule_views(validator_sources(before)), request.event, raw::raw_events(before.history), index))
            && denial.message@ == match denial.mode {
                RuleMode::Require => "committed history does not satisfy required past-regex rule"@,
                RuleMode::Forbid => "committed history satisfies forbidden past-regex rule"@,
            }
    }
    pub open(crate) spec fn check_result<E: Event, M>(before: Validator<E>, after: Validator<E>,
        request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>) -> bool {
        validator_frame(before, after)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_failure(result))
            && match result {
            Err(_) => raw::state_frame(before.history, after.history),
            Ok(Decision::Denied(denial)) => denial.event == request.event
                && raw::state_frame(before.history, after.history)
                && exists|index: int| #[trigger] denial_at(before, request, denial, index),
            Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
                && raw::push_result(before.history, after.history, request.event, Ok(()))
                && (junco_core::spec::hypotheses::event_obligations::<E>() ==> forall|index: int|
                    0 <= index < validator_sources(before).len() ==>
                        !sem::rule_violated(validator_sources(before)[index]@, request.event, raw::raw_events(before.history))),
        }
    }

    /// Exposes exact request publication, least-source denial, and unchanged error histories.
    pub proof fn lemma_check_result_facts<E: Event, M>(
        before: Validator<E>, after: Validator<E>, request: Request<E, M>,
        result: Result<Decision<E, M>, HistoryError>)
        requires check_result(before, after, request, result),
        ensures validator_wf(after), validator_frame(before, after),
            validator_sources(after) == validator_sources(before),
            raw::history_wf(validator_history(after)),
            raw::owner_frame(validator_history(before), validator_history(after)),
            raw::store_of(validator_history(after)) == raw::store_of(validator_history(before)),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_failure(result),
            match result {
                Err(_) => raw::state_frame(validator_history(before), validator_history(after))
                    && raw::raw_events(validator_history(after)) == raw::raw_events(validator_history(before)),
                Ok(Decision::Denied(denial)) => denial.event == request.event
                    && raw::state_frame(validator_history(before), validator_history(after))
                    && raw::raw_events(validator_history(after)) == raw::raw_events(validator_history(before))
                    && exists|index: int| denial_at(before, request, denial, index)
                        && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                            denial.mode == validator_sources(before)[index].mode
                                && sem::least_violation(sem::rule_views(validator_sources(before)),
                                    request.event, raw::raw_events(validator_history(before)), index)),
                Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
                    && raw::push_result(validator_history(before), validator_history(after), request.event, Ok(()))
                    && raw::raw_events(validator_history(after)) == raw::raw_events(validator_history(before)).push(request.event)
                    && (junco_core::spec::hypotheses::event_obligations::<E>() ==> forall|index: int|
                        0 <= index < validator_sources(before).len() ==>
                            !sem::rule_violated(validator_sources(before)[index]@,
                                request.event, raw::raw_events(validator_history(before)))),
            },
    {
        raw::lemma_history_frame_facts(before.history, after.history);
        match result {
            Ok(Decision::Grant(_)) => raw::lemma_push_result(before.history, after.history, request.event, Ok(())),
            Ok(Decision::Denied(denial)) => {
                let index = choose|index: int| #[trigger] denial_at(before, request, denial, index);
                assert(denial_at(before, request, denial, index));
            },
            Err(_) => {},
        }
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
