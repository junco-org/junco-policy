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

/// Maximum graph payload charged to one analyzer search, shared with the native implementation.
pub const GRAPH_BYTES: usize = crate::analyzer::GRAPH_BYTES;

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
    pub(crate) broadcast proof fn lemma_native_wf(&self)
        ensures #[trigger] self.wf() == crate::verify::frontend::analyzer_state_wf(*self),
    {
    }

    /// Reveals the public semantic guarantees of the opaque native invariant.
    pub proof fn lemma_wf(&self)
        requires self.wf(),
        ensures
            q::domains_wf::<E>(self@.domains),
            forall|i: int| 0 <= i < self@.rules.len() ==> s::rule_wf::<E>(self@.rules[i]),
    {
        self.lemma_native_wf();
        crate::verify::frontend::lemma_analyzer_semantic_wf(*self);
    }
}

/// Number of declared-domain values and registered source literals at one coordinate.
/// This semantic observation says nothing about private codebook or allocator availability.
pub open spec fn vocabulary_size<E: Event>(a: AnalyzerView<E>, coordinate: int) -> nat
    recommends 0 <= coordinate < history_syntax::spec::events::arity::<E>(),
{
    q::knowable_constants::<E>(a.domains, a.rules)[coordinate].len()
}

/// Registration adds exactly the new rule's source literals to the semantic vocabulary.
/// The cardinality bounds are semantic facts, not a promise of private allocation capacity.
pub proof fn lemma_vocabulary_growth<E: Event>(
    before: AnalyzerView<E>, after: AnalyzerView<E>, rule: Rule<E>, coordinate: int,
)
    requires
        after.domains == before.domains,
        after.rules == before.rules.push(rule),
        s::rule_wf::<E>(rule),
        0 <= coordinate < history_syntax::spec::events::arity::<E>(),
    ensures
        q::knowable_constants::<E>(after.domains, after.rules)[coordinate]
            == q::knowable_constants::<E>(before.domains, before.rules)[coordinate]
                .union(q::rule_constants(rule@)[coordinate]),
        q::knowable_constants::<E>(before.domains, before.rules)[coordinate]
            .subset_of(q::knowable_constants::<E>(after.domains, after.rules)[coordinate]),
        vocabulary_size(before, coordinate) <= vocabulary_size(after, coordinate),
        vocabulary_size(after, coordinate)
            <= vocabulary_size(before, coordinate) + q::rule_constants(rule@)[coordinate].len(),
{
    broadcast use vstd::seq::group_seq_lemmas;
    let literals = q::rule_constants(rule@);
    let registered_before = before.rules.map_values(|source: Rule<E>| {
        let values = q::rule_constants(source@);
        if 0 <= coordinate < values.len() { values[coordinate] } else { Set::empty() }
    });
    let registered_after = after.rules.map_values(|source: Rule<E>| {
        let values = q::rule_constants(source@);
        if 0 <= coordinate < values.len() { values[coordinate] } else { Set::empty() }
    });
    assert(literals.len() == history_syntax::spec::events::arity::<E>());
    assert(registered_after.drop_last() =~= registered_before);
    assert(registered_after.last() == literals[coordinate]);
    assert(q::constants_union(registered_after)
        == q::constants_union(registered_before).union(literals[coordinate]));
    let old_known = q::knowable_constants::<E>(before.domains, before.rules)[coordinate];
    let new_known = q::knowable_constants::<E>(after.domains, after.rules)[coordinate];
    assert(new_known =~= old_known.union(literals[coordinate]));
    assert(old_known.subset_of(new_known));
    vstd::set_lib::lemma_len_subset(old_known, new_known);
    vstd::set_lib::lemma_len_union(old_known, literals[coordinate]);
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

/// A1/A2/A5/A6: coverage, every real refutation, and PR10's exact minimum within its returned constant profile.
pub open spec fn covered_spec<E: Event>(a: AnalyzerView<E>, rule: nat, by: Seq<nat>, result: QueryResult<E::Component>) -> bool {
    escapes(result) && match result {
        QueryResult::Holds => q::covers(a.domains, rules_of(a, by), a.rules[rule as int]),
        QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(a.domains, cex)
            && q::known_within(cex, q::knowable_constants(a.domains, a.rules))
            && q::every_instance::<E>(a.domains, cex, |candidate: E, history: Seq<E>|
                s::rule_violated(a.rules[rule as int], candidate, history)
                    && !s::policy_denies(rules_of(a, by), candidate, history))
            && q::every_instance::<E>(a.domains, cex, |candidate: E, _history: Seq<E>|
                q::shortest_in_case::<E>(a.domains, cex.known, candidate, cex.history.len(),
                    |other: E, history: Seq<E>| s::rule_violated(a.rules[rule as int], other, history)
                        && !s::policy_denies(rules_of(a, by), other, history)))
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

/// A3/A5/A6: refinement, with the same selected Q rule governing refutation and per-profile minimum.
pub open spec fn at_least_as_strict_spec<E: Event>(a: AnalyzerView<E>, p: Seq<nat>, other: Seq<nat>, result: QueryResult<E::Component>) -> bool {
    escapes(result) && match result {
        QueryResult::Holds => q::refines(a.domains, rules_of(a, p), rules_of(a, other)),
        QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(a.domains, cex)
            && q::known_within(cex, q::knowable_constants(a.domains, a.rules))
            && (exists|j: int| 0 <= j < other.len()
                && (#[trigger] other[j]) < a.rules.len()
                && q::every_instance::<E>(a.domains, cex, |candidate: E, history: Seq<E>|
                    s::rule_violated(a.rules[other[j] as int], candidate, history)
                        && !s::policy_denies(rules_of(a, p), candidate, history))
                && q::every_instance::<E>(a.domains, cex, |candidate: E, _history: Seq<E>|
                    q::shortest_in_case::<E>(a.domains, cex.known, candidate, cex.history.len(),
                        |other_candidate: E, history: Seq<E>|
                            s::rule_violated(a.rules[other[j] as int], other_candidate, history)
                                && !s::policy_denies(rules_of(a, p), other_candidate, history))))
            && (q::counterexample_capacity::<E>(a.domains, cex) ==> q::has_instance::<E>(a.domains, cex)
                && !q::refines(a.domains, rules_of(a, p), rules_of(a, other))),
        _ => true,
    }
}

/// A4/A5: scoped real-event tail inclusion, capacity-qualified refutations, and the existing global length bound.
pub open spec fn tail_included_spec<E: Event>(before: AnalyzerView<E>, after: AnalyzerView<E>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>, result: QueryResult<E::Component>) -> bool {
    analyzer_frame(before, after) && s::head_tails_wf::<E>(head, left, right) && escapes(result) && match result {
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
