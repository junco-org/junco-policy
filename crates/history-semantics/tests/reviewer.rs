#![cfg(feature = "runtime")]

//! T: executable public clients of R1–R5. No representation or private proof APIs.
#[cfg(verus_keep_ghost)]
mod proofs {
    use history_semantics::spec::monitor::lemma_validator_wf;
    use history_semantics::validator::{Decision, Validator};
    use history_syntax::{Component3, Event};
    use junco_core::HistoryError;
    use junco_core::event::Request;
    use junco_core::spec::hypotheses::{
        analyzer_hypotheses, hash_coherent, lemma_u8_event_hypotheses, lemma_u32_event_hypotheses,
        monitor_hypotheses,
    };
    use junco_core::spec::semantics::rule_violated;
    use vstd::prelude::*;

    verus! {

    /// H4: the only premise is native hashing faithfulness, not an event/equality axiom.
    proof fn theorem_u8_hash_only_hypotheses()
        requires hash_coherent::<Component3<u8, u8, u8>>(),
        ensures monitor_hypotheses::<(u8, u8, u8)>(), analyzer_hypotheses::<(u8, u8, u8)>(),
    {
        lemma_u8_event_hypotheses();
    }

    /// H4 also has a concrete witness with a u32 coordinate.
    proof fn theorem_u32_hash_only_hypotheses()
        requires hash_coherent::<Component3<u32, u8, u8>>(),
        ensures monitor_hypotheses::<(u32, u8, u8)>(), analyzer_hypotheses::<(u32, u8, u8)>(),
    {
        lemma_u32_event_hypotheses();
    }

    /// Actual check call: exact append-on-grant, least-source denial, atomic errors,
    /// and the safety of EVERY committed prefix (including after any prior check).
    fn theorem_monitor_check_trace_safety<E: Event, M>(validator: &mut Validator<E>, request: Request<E, M>)
        -> (result: Result<Decision<E, M>, HistoryError>)
        requires old(validator).wf(), monitor_hypotheses::<E>(),
        ensures
            final(validator).wf(), final(validator)@.rules == old(validator)@.rules,
            match result {
                Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
                    && final(validator)@.history == old(validator)@.history.push(request.event)
                    && forall|i: int| 0 <= i < old(validator)@.rules.len()
                        ==> !rule_violated(old(validator)@.rules[i], request.event, old(validator)@.history),
                Ok(Decision::Denied(denial)) => final(validator)@.history == old(validator)@.history
                    && denial.event == request.event
                    && exists|j: int| 0 <= j < old(validator)@.rules.len()
                        && rule_violated(old(validator)@.rules[j], request.event, old(validator)@.history)
                        && denial.mode == old(validator)@.rules[j].mode
                        && forall|i: int| 0 <= i < j
                            ==> !rule_violated(old(validator)@.rules[i], request.event, old(validator)@.history),
                Err(error) => final(validator)@.history == old(validator)@.history && !(error is Invariant),
            },
            forall|j: int, i: int| 0 <= j < final(validator)@.history.len()
                && 0 <= i < final(validator)@.rules.len()
                ==> !rule_violated(final(validator)@.rules[i], final(validator)@.history[j],
                    final(validator)@.history.subrange(0, j)),
    {
        let result = validator.check(request);
        proof { lemma_validator_wf(*validator); }
        result
    }

    /// Actual permits call: read-only, exact Boolean equivalence, non-invariant errors.
    fn theorem_monitor_permits<E: Event>(validator: &mut Validator<E>, candidate: &E)
        -> (result: Result<bool, HistoryError>)
        requires old(validator).wf(), monitor_hypotheses::<E>(),
        ensures final(validator).wf(), final(validator)@.rules == old(validator)@.rules,
            final(validator)@.history == old(validator)@.history,
            match result {
                Ok(permitted) => permitted == (forall|i: int| 0 <= i < old(validator)@.rules.len()
                    ==> !rule_violated(old(validator)@.rules[i], *candidate, old(validator)@.history)),
                Err(error) => !(error is Invariant),
            },
    {
        validator.permits(candidate)
    }

    }
}

#[cfg(not(verus_keep_ghost))]
#[test]
fn public_monitor_grant_and_denial() {
    use history_semantics::validator::{Decision, Validator};
    use history_store::typed::Store;
    use history_syntax::{Component3, ComponentPattern, Head, RegexExpr, Rule, RuleMode};
    use junco_core::event::Request;
    use std::sync::Arc;

    let store = Arc::new(Store::<(u8, u8, u8)>::new().expect("store"));
    let mut builder = Validator::builder(store);
    builder
        .add_rule(Rule::new(
            RuleMode::Forbid,
            Head(vec![
                ComponentPattern::Constant(Component3::C0(1)),
                ComponentPattern::Constant(Component3::C1(2)),
                ComponentPattern::Constant(Component3::C2(3)),
            ]),
            RegexExpr::All,
        ))
        .expect("rule");
    let mut monitor = builder.finish().expect("monitor");
    assert!(!monitor.permits(&(1, 2, 3)).expect("permits"));
    assert!(matches!(
        monitor
            .check(Request {
                event: (1, 2, 3),
                metadata: ()
            })
            .expect("denial"),
        Decision::Denied(_)
    ));
    assert!(monitor.history().is_empty());
    assert!(monitor.permits(&(9, 2, 3)).expect("permits"));
    assert!(matches!(
        monitor
            .check(Request {
                event: (9, 2, 3),
                metadata: ()
            })
            .expect("grant"),
        Decision::Grant(_)
    ));
    assert_eq!(monitor.history(), &[(9, 2, 3)]);
}
