//! R6: the analyzer's semantic view and decision contracts over real events.
//! Holds is unconditional; only counterexample existence/refutation needs its own fresh capacity.

use crate::PolicyAnalyzer;
use history_syntax::spec::events::{HeadView, RegexView};
use history_syntax::{Event, Rule};
use junco_core::HistoryError;
use junco_core::spec::{questions as q, semantics as s};
use vstd::prelude::*;

/// A query's semantic result; Exhausted deliberately carries no correctness claim.
#[verus_verify]
pub enum QueryResult<C> {
    /// The requested property holds.
    Holds,
    /// A symbolic pair interpreted by R3's real-event instance relation.
    Counterexample(q::Counterexample<C>),
    /// No verdict is claimed when the implementation exhausts its graph budget.
    Exhausted,
    /// A non-invariant input or resource error.
    Error(HistoryError),
}

verus! {

/// Maximum graph payload charged to one analyzer search: 16 MiB.
pub const GRAPH_BYTES: usize = 16 * 1024 * 1024;

/// Only declared domains and registered source rules are semantic analyzer state.
pub struct AnalyzerView<E: Event> {
    /// Domain assumptions required of the candidate and every history event.
    pub domains: q::Domains<E::Component>,
    /// Source rules in stable registration order.
    pub rules: Seq<Rule<E>>,
}

impl<E: Event> PolicyAnalyzer<E> {
    /// Opaque implementation invariant; codebooks, owners, and search plumbing remain private.
    pub closed spec fn wf(&self) -> bool {
        crate::verify::frontend::analyzer_state_wf(*self)
    }

    /// Native proofs may reveal the implementation invariant without exposing its private fields.
    pub(crate) proof fn lemma_native_wf(&self)
        ensures self.wf() == crate::verify::frontend::analyzer_state_wf(*self),
    {
    }
}


/// Rule ids select this view's registered source rules; duplicates retain their id/multiset meaning.
pub open spec fn rules_of<E: Event>(a: AnalyzerView<E>, ids: Seq<nat>) -> Seq<Rule<E>> {
    ids.map(|i: int, id: nat| a.rules[id as int])
}

/// Every selected index names a registered rule; runtime owner checks are additional.
pub open spec fn valid_ids<E: Event>(a: AnalyzerView<E>, ids: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> #[trigger] ids[i] < a.rules.len()
}

/// No semantic state changes during a query; private allocation/cache frames are separate.
pub open spec fn analyzer_frame<E: Event>(before: AnalyzerView<E>, after: AnalyzerView<E>) -> bool {
    after.domains == before.domains && after.rules == before.rules
}

/// Exhausted makes no claim; errors exclude only invariant failures.
pub open spec fn escapes<C>(result: QueryResult<C>) -> bool {
    match result {
        QueryResult::Exhausted => true,
        QueryResult::Error(error) => !(error is Invariant),
        _ => true,
    }
}

/// A1/A2/A5: Holds proves coverage without capacity; every instance refutes it, and capacity makes it nonvacuous.
pub open spec fn covered_spec<E: Event>(a: AnalyzerView<E>, rule: nat, by: Seq<nat>, result: QueryResult<E::Component>) -> bool {
    escapes(result) && match result {
        QueryResult::Holds => q::covers(a.domains, rules_of(a, by), a.rules[rule as int]),
        QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(a.domains, cex)
            && q::known_within(cex, q::knowable_constants(a.domains, a.rules))
            && q::every_instance::<E>(a.domains, cex, |candidate: E, history: Seq<E>|
                s::rule_violated(a.rules[rule as int], candidate, history)
                    && !s::policy_denies(rules_of(a, by), candidate, history))
            && (q::counterexample_capacity::<E>(a.domains, cex) ==> q::has_instance::<E>(a.domains, cex)
                && !q::covers(a.domains, rules_of(a, by), a.rules[rule as int])),
        _ => true,
    }
}

/// A3/A5: coverage by all non-target ids, plus exact removal semantics for arbitrary order and duplicates.
/// Absent targets retain the coverage meaning; only a present target's refutation changes a decision.
pub open spec fn redundant_spec<E: Event>(a: AnalyzerView<E>, rule: nat, policy: Seq<nat>, result: QueryResult<E::Component>) -> bool {
    let remaining = q::without_rule(policy, rule);
    let full = rules_of(a, policy);
    let others = rules_of(a, remaining);
    covered_spec(a, rule, remaining, result) && match result {
        QueryResult::Holds => q::redundant_in(a.domains, full, others),
        QueryResult::Counterexample(cex) => policy.contains(rule) ==> (
            q::every_instance::<E>(a.domains, cex, |candidate: E, history: Seq<E>|
                s::policy_denies(full, candidate, history) && !s::policy_denies(others, candidate, history))
            && (q::counterexample_capacity::<E>(a.domains, cex) ==> !q::redundant_in(a.domains, full, others))),
        _ => true,
    }
}

/// A3/A5: refinement is real-event permission implication, with every counterexample denied by the same selected Q rule.
pub open spec fn at_least_as_strict_spec<E: Event>(a: AnalyzerView<E>, p: Seq<nat>, other: Seq<nat>, result: QueryResult<E::Component>) -> bool {
    escapes(result) && match result {
        QueryResult::Holds => q::refines(a.domains, rules_of(a, p), rules_of(a, other)),
        QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(a.domains, cex)
            && q::known_within(cex, q::knowable_constants(a.domains, a.rules))
            && (exists|j: int| 0 <= j < other.len()
                && (#[trigger] other[j]) < a.rules.len()
                && q::every_instance::<E>(a.domains, cex, |candidate: E, history: Seq<E>|
                    s::rule_violated(a.rules[other[j] as int], candidate, history)
                        && !s::policy_denies(rules_of(a, p), candidate, history)))
            && (q::counterexample_capacity::<E>(a.domains, cex) ==> q::has_instance::<E>(a.domains, cex)
                && !q::refines(a.domains, rules_of(a, p), rules_of(a, other))),
        _ => true,
    }
}

/// A4/A5: real-event tail inclusion, nonvacuous capacity-qualified refutations, and the existing global length bound.
pub open spec fn tail_included_spec<E: Event>(before: AnalyzerView<E>, after: AnalyzerView<E>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>, result: QueryResult<E::Component>) -> bool {
    analyzer_frame(before, after) && escapes(result) && match result {
        QueryResult::Holds => q::tails_included::<E>(after.domains, head, left, right),
        QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(after.domains, cex)
            && q::known_within(cex, q::tail_knowable_constants::<E>(after.domains, head, left, right))
            && q::every_instance::<E>(after.domains, cex, |candidate: E, history: Seq<E>|
                s::head_matches(head, candidate) && s::lang(left, head, candidate, history)
                    && !s::lang(right, head, candidate, history))
            && (forall|candidate: E, history: Seq<E>| q::in_domains(after.domains, candidate, history)
                && history.len() < cex.history.len() && s::head_matches(head, candidate)
                && s::lang(left, head, candidate, history) ==> s::lang(right, head, candidate, history))
            && (q::counterexample_capacity::<E>(after.domains, cex) ==> q::has_instance::<E>(after.domains, cex)
                && !q::tails_included::<E>(after.domains, head, left, right)),
        _ => true,
    }
}

}
