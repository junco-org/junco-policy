//! What the analyzer's verdicts mean, over real events through the semantics
//! (`junco_core::spec::semantics`) and the analysis questions (`junco_core::spec::questions`).
//!
//! A `PolicyAnalyzer` is read through `AnalyzerView`: declared domains, the added rules by index,
//! and the constants it distinguishes per coordinate. The `*_spec` predicates are the postconditions
//! of `covered`, `redundant`, `at_least_as_strict` and `tail_included` on an `Ok` answer.
//!
//! `known` is determined by the contracts, never chosen by the implementation: `new` establishes
//! `known == declared_sets(domains)`; `add_rule` ensures `after.known == known_with(before.known,
//! rule_constants(rule))` and `tail_included` ensures `after.known == known_with(before.known,
//! tail_constants(head, left, right))`, both on every return (`Ok` or `Err`: interning may have
//! happened before a failure); `covered`, `redundant` and `at_least_as_strict` leave the view
//! unchanged. So capacity (`capacity_for`) is relative to exactly the constants of the inputs.
//!
//! Escapes (`Exhausted` and errors), in prose: `Exhausted` is returned only when a search's `charge` returned
//! `HistoryError::GraphBudget` (whose contract is `charged + bytes > budget`, with the budget
//! `GRAPH_BYTES`); `Err` is never an invariant failure (`no_invariant_failure`); every call
//! terminates (no `exec_allows_no_decreases_clause` in this crate, see TRUST.md); the policy
//! queries stop at the first non-`Holds` split case; verdicts transfer to the monitor only for
//! pairs inside the declared domains.

use crate::analyzer::RuleId;
use history_syntax::Event;
use history_syntax::spec::events::{HeadView, RegexView, RuleView, arity, event_view};
use junco_core::spec::questions::*;
use junco_core::spec::semantics::{head_matches, history_view, lang, policy_denies, rule_violated};
use junco_core::verify::flatten::regex_cost;
use vstd::prelude::*;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/// What a reviewer needs of a `PolicyAnalyzer`: declared domains, the added rules by index, and
/// the constants it distinguishes per coordinate (rule constants, declared values, constants of
/// tails it has been asked about). `known` is what counterexample freshness and per-case minimality
/// are relative to.
pub struct AnalyzerView<C> {
    /// Declared domain per coordinate (`None` = every value of the type).
    pub domains: DomainsView<C>,
    /// The added rules, by `RuleId` index.
    pub rules: Seq<RuleView<C>>,
    /// The constants the analyzer distinguishes, per coordinate.
    pub known: Seq<Set<C>>,
}

/// The number of known constants, summed over the coordinates.
pub open spec fn known_count<C>(known: Seq<Set<C>>) -> nat
    decreases known.len(),
{
    if known.len() == 0 { 0 } else { known_count(known.drop_last()) + known.last().len() }
}

/// `known` after interning exactly `added`, per coordinate.
pub open spec fn known_with<C>(known: Seq<Set<C>>, added: Seq<Set<C>>) -> Seq<Set<C>> {
    Seq::new(known.len(), |i: int| known[i].union(added[i]))
}

/// The constants of a `tail_included` query per coordinate: head constants and both tails'.
pub open spec fn tail_constants<C>(head: HeadView<C>, left: RegexView<C>, right: RegexView<C>) -> Seq<Set<C>> {
    Seq::new(head.len(), |i: int| head_constants(head)[i]
        .union(regex_constants(left, head.len())[i])
        .union(regex_constants(right, head.len())[i]))
}

// ----- capacities, over the view -----

/// The declared sets, with the empty set at undeclared coordinates.
pub open spec fn declared_sets<C>(domains: DomainsView<C>) -> Seq<Set<C>> {
    domains.map(|i: int, d: Option<Set<C>>| match d { None => Set::empty(), Some(values) => values })
}

/// The constructor can intern every declared value.
pub open spec fn constructor_capacity<E: Event>(domains: DomainsView<E::Component>) -> bool {
    known_count(declared_sets(domains)) <= u32::MAX
}

/// `add_rule` can intern the rule's constants.
pub open spec fn add_rule_capacity<E: Event>(a: AnalyzerView<E::Component>, rule: RuleView<E::Component>) -> bool {
    known_count(a.known) + arity::<E>() + regex_cost::<E>(rule.tail) <= u32::MAX
}

/// `tail_included` can intern both tails' constants.
pub open spec fn query_capacity<E: Event>(
    a: AnalyzerView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>,
) -> bool {
    known_count(a.known) + 2 * arity::<E>() + regex_cost::<E>(left) + regex_cost::<E>(right) <= u32::MAX
}

// ----- rule selection -----

/// The index of each rule id (`RuleId`'s view is its index).
pub open spec fn ids_of(ids: Seq<RuleId>) -> Seq<nat> {
    ids.map_values(|id: RuleId| id@)
}

/// The rules selected by index, in order.
pub open spec fn rules_of<C>(a: AnalyzerView<C>, ids: Seq<nat>) -> Seq<RuleView<C>> {
    ids.map(|i: int, id: nat| a.rules[id as int])
}

/// The policy without every occurrence of `rule`.
pub open spec fn without_rule(policy: Seq<nat>, rule: nat) -> Seq<nat> {
    policy.filter(|id: nat| id != rule)
}

/// The pairs `rule` violates and `p` does not deny.
pub open spec fn uncovered<E: Event>(
    p: Seq<RuleView<E::Component>>, rule: RuleView<E::Component>,
) -> spec_fn(E, Seq<E>) -> bool {
    |c: E, h: Seq<E>| rule_violated(rule, c, h) && !policy_denies(p, c, h)
}

/// The pairs matching `head` whose history is in `left` but not in `right`.
pub open spec fn tail_fails<E: Event>(
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>,
) -> spec_fn(E, Seq<E>) -> bool {
    |c: E, h: Seq<E>| head_matches(head, event_view(c))
        && lang(left, head, event_view(c), history_view(h))
        && !lang(right, head, event_view(c), history_view(h))
}

// ----- verdicts -----

/// Only undeclared coordinates need values outside the known constants. Declared coordinates
/// use constants exclusively, as required separately by `counterexample_spec`.
pub open spec fn undeclared_capacity<E: Event>(
    a: AnalyzerView<E::Component>, cex: CexView<E::Component>,
) -> bool {
    forall|i: int| 0 <= i < arity::<E>() && a.domains[i] is None
        ==> #[trigger] fresh_capacity::<E>(a.domains, a.known, i, fresh_used(cex, i).len())
}

/// What a returned symbolic counterexample promises about `fails`: every real instance is a
/// real pair in the domains that fails; under capacity for its own fresh values an instance exists.
pub open spec fn counterexample_spec<E: Event>(
    a: AnalyzerView<E::Component>, cex: CexView<E::Component>, fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    &&& cex_arity(cex, arity::<E>())
    &&& forall|i: int| 0 <= i < arity::<E>() && a.domains[i] is Some
        ==> fresh_used(cex, i) =~= ISet::empty()
    &&& every_instance::<E>(a.domains, a.known, cex, fails)
    &&& undeclared_capacity::<E>(a, cex) ==> cex_has_instance::<E>(a.domains, a.known, cex)
}

/// For `covered`: Holds is coverage; a counterexample is an uncovered pair, refutes
/// coverage when it has an instance, and is shortest within its constant profile.
pub open spec fn covered_spec<E: Event>(
    a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>, v: InclusionView<E::Component>,
) -> bool {
    let p = rules_of(a, by);
    let r = a.rules[rule as int];
    match v {
        InclusionView::Holds => covers::<E>(a.domains, p, r),
        InclusionView::Counterexample(cex) => counterexample_spec::<E>(a, cex, uncovered::<E>(p, r))
            && (cex_has_instance::<E>(a.domains, a.known, cex) ==> !covers::<E>(a.domains, p, r))
            && minimal_in_case::<E>(a.domains, a.known, cex, uncovered::<E>(p, r)),
        InclusionView::Exhausted => true,
    }
}

/// Removal semantics: removing every occurrence of the id changes no
/// decision; multiset/id reading.
pub open spec fn removal_preserves_decisions<E: Event>(
    a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h)
        ==> (#[trigger] policy_denies(rules_of(a, policy), c, h)
            == policy_denies(rules_of(a, without_rule(policy, rule)), c, h))
}

/// The pairs whose decision removal changes: denied with the rule, permitted without it.
pub open spec fn removal_fails<E: Event>(
    a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>,
) -> spec_fn(E, Seq<E>) -> bool {
    |c: E, h: Seq<E>| policy_denies(rules_of(a, policy), c, h)
        && !policy_denies(rules_of(a, without_rule(policy, rule)), c, h)
}

/// Redundancy: coverage by the others, plus preservation of every decision under removal.
pub open spec fn redundant_spec<E: Event>(
    a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>, v: InclusionView<E::Component>,
) -> bool {
    covered_spec::<E>(a, rule, without_rule(policy, rule), v) && match v {
        InclusionView::Holds => removal_preserves_decisions::<E>(a, rule, policy),
        InclusionView::Counterexample(cex) => policy.contains(rule)
            ==> every_instance::<E>(a.domains, a.known, cex, removal_fails::<E>(a, rule, policy))
                && (cex_has_instance::<E>(a.domains, a.known, cex)
                    ==> !removal_preserves_decisions::<E>(a, rule, policy)),
        InclusionView::Exhausted => true,
    }
}

/// Refinement: Holds is `P ⊑ Q`; a counterexample is uncovered for some rule of `Q`, refutes
/// refinement when it has an instance, and is shortest within its constant profile for that rule.
pub open spec fn at_least_as_strict_spec<E: Event>(
    a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>, v: InclusionView<E::Component>,
) -> bool {
    let pp = rules_of(a, p);
    let qq = rules_of(a, q);
    match v {
        InclusionView::Holds => refines::<E>(a.domains, pp, qq),
        InclusionView::Counterexample(cex) => (exists|j: int| 0 <= j < qq.len()
                && counterexample_spec::<E>(a, cex, #[trigger] uncovered::<E>(pp, qq[j]))
                && minimal_in_case::<E>(a.domains, a.known, cex, uncovered::<E>(pp, qq[j])))
            && (cex_has_instance::<E>(a.domains, a.known, cex) ==> !refines::<E>(a.domains, pp, qq)),
        InclusionView::Exhausted => true,
    }
}

/// Tail inclusion for every matching real candidate; a counterexample is real (under
/// capacity) and of minimum history length.
pub open spec fn tail_included_spec<E: Event>(
    a: AnalyzerView<E::Component>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>, v: InclusionView<E::Component>,
) -> bool {
    match v {
        InclusionView::Holds => tails_included::<E>(a.domains, head, left, right),
        InclusionView::Counterexample(cex) => counterexample_spec::<E>(a, cex, tail_fails::<E>(head, left, right))
            && (cex_has_instance::<E>(a.domains, a.known, cex) ==> !tails_included::<E>(a.domains, head, left, right))
            && shortest::<E>(a.domains, cex.history.len(), tail_fails::<E>(head, left, right)),
        InclusionView::Exhausted => true,
    }
}

} // verus!
