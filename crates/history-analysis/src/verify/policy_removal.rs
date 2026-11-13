//! Decision preservation for removing every occurrence of a rule id, independently of policy
//! order and duplicate ids (R6 `removal_preserves_decisions`, decision 5). An absent id retains
//! the coverage-query interpretation.

use crate::spec::analyzer::{
    AnalyzerView, covered_spec, redundant_spec, removal_fails, removal_preserves_decisions,
    rules_of, uncovered, without_rule,
};
use history_semantics::verify::refinement::semantics;
use history_syntax::Event;
use junco_core::spec::questions::{
    CexView, FreshChoice, InclusionView, admissible, cex_has_instance, covers, every_instance,
    in_domains, instantiates,
};
use junco_core::spec::semantics::{policy_denies, rule_violated};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq::group_seq_lemmas;

/// Membership in the existing filter abstraction, without relying on closure identity.
pub proof fn lemma_without_rule_contains(policy: Seq<nat>, rule: nat, id: nat)
    ensures without_rule(policy, rule).contains(id) == (policy.contains(id) && id != rule),
    decreases policy.len(),
{
    reveal(Seq::filter);
    if policy.len() > 0 {
        lemma_without_rule_contains(policy.drop_last(), rule, id);
        assert(without_rule(policy, rule) == if policy.last() != rule {
            without_rule(policy.drop_last(), rule).push(policy.last())
        } else {
            without_rule(policy.drop_last(), rule)
        });
        assert(policy == policy.drop_last().push(policy.last()));
    }
}

/// Filtering removes exactly the violations contributed by the selected id, not by its position.
pub proof fn lemma_policy_denies_without_rule<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    policy: Seq<nat>, c: E, h: Seq<E>)
    requires rule < a.rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures policy_denies(rules_of(a, policy), c, h)
        == (policy_denies(rules_of(a, without_rule(policy, rule)), c, h)
            || (policy.contains(rule) && rule_violated(a.rules[rule as int], c, h))),
{
    let others = without_rule(policy, rule);
    let full = rules_of(a, policy);
    let filtered = rules_of(a, others);
    if policy_denies(full, c, h) {
        let j = choose|j: int| 0 <= j < full.len() && #[trigger] rule_violated(full[j], c, h);
        if policy[j] == rule {
            assert(policy.contains(rule));
        } else {
            lemma_without_rule_contains(policy, rule, policy[j]);
            assert(others.contains(policy[j]));
            let k = choose|k: int| 0 <= k < others.len() && others[k] == policy[j];
            assert(filtered[k] == full[j]);
            assert(rule_violated(filtered[k], c, h));
        }
    }
    if policy_denies(filtered, c, h) {
        let k = choose|k: int| 0 <= k < filtered.len() && #[trigger] rule_violated(filtered[k], c, h);
        assert(others.contains(others[k]));
        lemma_without_rule_contains(policy, rule, others[k]);
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == others[k];
        assert(full[j] == filtered[k]);
        assert(rule_violated(full[j], c, h));
    }
    if policy.contains(rule) && rule_violated(a.rules[rule as int], c, h) {
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == rule;
        assert(full[j] == a.rules[rule as int]);
        assert(rule_violated(full[j], c, h));
    }
}

/// If present, the selected rule can be moved to the end after deleting all its occurrences,
/// without changing the policy's existential denial semantics.
pub proof fn lemma_policy_denies_removal_push<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    policy: Seq<nat>, c: E, h: Seq<E>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures policy_denies(rules_of(a, policy), c, h)
        == policy_denies(rules_of(a, without_rule(policy, rule)).push(a.rules[rule as int]), c, h),
{
    lemma_policy_denies_without_rule::<E>(a, rule, policy, c, h);
    semantics::lemma_policy_denies_push(rules_of(a, without_rule(policy, rule)),
        a.rules[rule as int], c, h);
}

/// Instantiate the append-shaped redundancy theorem for arbitrary order/duplicates.
pub proof fn lemma_removal_iff_covered<E: Event>(a: AnalyzerView<E::Component>, rule: nat, policy: Seq<nat>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures covers::<E>(a.domains, rules_of(a, without_rule(policy, rule)), a.rules[rule as int])
        == removal_preserves_decisions::<E>(a, rule, policy),
{
    let others = rules_of(a, without_rule(policy, rule));
    let r = a.rules[rule as int];
    semantics::theorem_redundant_iff_covered::<E>();
    assert(covers::<E>(a.domains, others, r) <==> forall|c: E, h: Seq<E>|
        in_domains::<E>(a.domains, c, h)
            ==> (#[trigger] policy_denies(others.push(r), c, h) == policy_denies(others, c, h)));
    if covers::<E>(a.domains, others, r) {
        assert forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h)
            implies (#[trigger] policy_denies(rules_of(a, policy), c, h)
                == policy_denies(others, c, h)) by {
            lemma_policy_denies_removal_push::<E>(a, rule, policy, c, h);
        }
    }
    if removal_preserves_decisions::<E>(a, rule, policy) {
        assert forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h)
            implies (#[trigger] policy_denies(others.push(r), c, h)
                == policy_denies(others, c, h)) by {
            lemma_policy_denies_removal_push::<E>(a, rule, policy, c, h);
        }
    }
}

/// The coverage verdict for the other rules also describes the effect of removing the id (A3).
pub proof fn lemma_redundant_decisions<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    policy: Seq<nat>, v: InclusionView<E::Component>)
    requires rule < a.rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
        covered_spec::<E>(a, rule, without_rule(policy, rule), v),
    ensures redundant_spec::<E>(a, rule, policy, v),
{
    let p = rules_of(a, without_rule(policy, rule));
    let r = a.rules[rule as int];
    match v {
        InclusionView::Holds => {
            if policy.contains(rule) {
                lemma_removal_iff_covered::<E>(a, rule, policy);
            } else {
                assert forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h)
                    implies (#[trigger] policy_denies(rules_of(a, policy), c, h)
                        == policy_denies(p, c, h)) by {
                    lemma_policy_denies_without_rule::<E>(a, rule, policy, c, h);
                }
            }
        },
        InclusionView::Counterexample(cex) => {
            if policy.contains(rule) {
                assert forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                    admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
                    implies in_domains::<E>(a.domains, c, h) && removal_fails::<E>(a, rule, policy)(c, h) by {
                    assert(uncovered::<E>(p, r)(c, h));
                    lemma_policy_denies_without_rule::<E>(a, rule, policy, c, h);
                }
                if cex_has_instance::<E>(a.domains, a.known, cex) {
                    let (f, c, h) = choose|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
                        admissible::<E>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h);
                    assert(in_domains::<E>(a.domains, c, h) && removal_fails::<E>(a, rule, policy)(c, h));
                    assert(!removal_preserves_decisions::<E>(a, rule, policy));
                }
            }
        },
        InclusionView::Exhausted => {},
    }
}

/// A realizable coverage counterexample explicitly witnesses that removal changes a decision.
pub proof fn lemma_redundant_counterexample_refutes<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    policy: Seq<nat>, cex: CexView<E::Component>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
        covered_spec::<E>(a, rule, without_rule(policy, rule), InclusionView::Counterexample(cex)),
        cex_has_instance::<E>(a.domains, a.known, cex),
    ensures !removal_preserves_decisions::<E>(a, rule, policy),
{
    lemma_redundant_decisions::<E>(a, rule, policy, InclusionView::Counterexample(cex));
}
}
