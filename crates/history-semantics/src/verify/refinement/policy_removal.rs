//! Exact decision preservation for removing every occurrence of a registered rule id.
//! Order, duplicate ids, absent targets, and distinct ids with equal source rules retain
//! PR10's meaning. All decisions and counterexample instances use the canonical R2/R3 model.

use super::semantics;
use history_syntax::{Event, Rule};
use junco_core::spec::{questions as q, semantics as s};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq::group_seq_lemmas;

/// Filtering removes every target id and no other id, independently of order and duplicates.
pub proof fn lemma_without_rule_contains(policy: Seq<nat>, rule: nat, id: nat)
    ensures q::without_rule(policy, rule).contains(id) == (policy.contains(id) && id != rule),
    decreases policy.len(),
{
    reveal(Seq::filter);
    if policy.len() > 0 {
        lemma_without_rule_contains(policy.drop_last(), rule, id);
        assert(q::without_rule(policy, rule) == if policy.last() != rule {
            q::without_rule(policy.drop_last(), rule).push(policy.last())
        } else { q::without_rule(policy.drop_last(), rule) });
        assert(policy == policy.drop_last().push(policy.last()));
    }
}

/// Id filtering removes exactly the selected rule's denials, not rules with equal source text.
pub proof fn lemma_policy_denies_without_rule<E: Event>(rules: Seq<Rule<E>>, rule: nat,
    policy: Seq<nat>, candidate: E, history: Seq<E>)
    requires rule < rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < rules.len(),
    ensures s::policy_denies(policy.map(|_i: int, id: nat| rules[id as int]), candidate, history)
        == (s::policy_denies(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), candidate, history)
            || (policy.contains(rule) && s::rule_violated(rules[rule as int], candidate, history))),
{
    let others = q::without_rule(policy, rule);
    let full = policy.map(|_i: int, id: nat| rules[id as int]);
    let filtered = others.map(|_i: int, id: nat| rules[id as int]);
    if s::policy_denies(full, candidate, history) {
        let j = choose|j: int| 0 <= j < full.len() && #[trigger] s::rule_violated(full[j], candidate, history);
        if policy[j] == rule {
            assert(policy.contains(rule));
        } else {
            lemma_without_rule_contains(policy, rule, policy[j]);
            let k = choose|k: int| 0 <= k < others.len() && others[k] == policy[j];
            assert(filtered[k] == full[j]);
            assert(s::rule_violated(filtered[k], candidate, history));
        }
    }
    if s::policy_denies(filtered, candidate, history) {
        let k = choose|k: int| 0 <= k < filtered.len() && #[trigger] s::rule_violated(filtered[k], candidate, history);
        assert(others.contains(others[k]));
        lemma_without_rule_contains(policy, rule, others[k]);
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == others[k];
        assert(full[j] == filtered[k]);
        assert(s::rule_violated(full[j], candidate, history));
    }
    if policy.contains(rule) && s::rule_violated(rules[rule as int], candidate, history) {
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == rule;
        assert(full[j] == rules[rule as int]);
        assert(s::rule_violated(full[j], candidate, history));
    }
}

/// A present target can be moved to the end after filtering, without changing any decision.
pub proof fn lemma_policy_denies_removal_push<E: Event>(rules: Seq<Rule<E>>, rule: nat,
    policy: Seq<nat>, candidate: E, history: Seq<E>)
    requires rule < rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < rules.len(),
    ensures s::policy_denies(policy.map(|_i: int, id: nat| rules[id as int]), candidate, history)
        == s::policy_denies(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]).push(rules[rule as int]), candidate, history),
{
    lemma_policy_denies_without_rule(rules, rule, policy, candidate, history);
    semantics::lemma_policy_denies_push(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]),
        rules[rule as int], candidate, history);
}

/// For a present target, coverage by the remaining ids is exactly decision preservation.
pub proof fn lemma_removal_iff_covered<E: Event>(domains: q::Domains<E::Component>,
    rules: Seq<Rule<E>>, rule: nat, policy: Seq<nat>)
    requires rule < rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < rules.len(),
    ensures q::covers(domains, q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), rules[rule as int])
        == q::redundant_in(domains, policy.map(|_i: int, id: nat| rules[id as int]),
            q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int])),
{
    let full = policy.map(|_i: int, id: nat| rules[id as int]);
    let others = q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]);
    let target = rules[rule as int];
    semantics::theorem_redundant_iff_covered::<E>();
    if q::covers(domains, others, target) {
        assert forall|candidate: E, history: Seq<E>| q::in_domains(domains, candidate, history)
            implies (#[trigger] s::policy_denies(full, candidate, history)
                == s::policy_denies(others, candidate, history)) by {
            lemma_policy_denies_removal_push(rules, rule, policy, candidate, history);
        }
    }
    if q::redundant_in(domains, full, others) {
        assert forall|candidate: E, history: Seq<E>| q::in_domains(domains, candidate, history)
            implies (#[trigger] s::policy_denies(others.push(target), candidate, history)
                == s::policy_denies(others, candidate, history)) by {
            lemma_policy_denies_removal_push(rules, rule, policy, candidate, history);
        }
    }
}

/// Holds preserves all decisions even if the target is absent; no membership premise is added.
pub proof fn lemma_redundant_decisions<E: Event>(domains: q::Domains<E::Component>,
    rules: Seq<Rule<E>>, rule: nat, policy: Seq<nat>)
    requires rule < rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < rules.len(),
        q::covers(domains, q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), rules[rule as int]),
    ensures q::redundant_in(domains, policy.map(|_i: int, id: nat| rules[id as int]),
        q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int])),
{
    let full = policy.map(|_i: int, id: nat| rules[id as int]);
    let others = q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]);
    if policy.contains(rule) {
        lemma_removal_iff_covered(domains, rules, rule, policy);
    } else {
        assert forall|candidate: E, history: Seq<E>| q::in_domains(domains, candidate, history)
            implies (#[trigger] s::policy_denies(full, candidate, history)
                == s::policy_denies(others, candidate, history)) by {
            lemma_policy_denies_without_rule(rules, rule, policy, candidate, history);
        }
    }
}

/// Every real instance changes a present target's decision; an instance refutes preservation.
pub proof fn lemma_redundant_counterexample_refutes<E: Event>(domains: q::Domains<E::Component>,
    rules: Seq<Rule<E>>, rule: nat, policy: Seq<nat>, cex: q::Counterexample<E::Component>)
    requires rule < rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < rules.len(),
        q::every_instance::<E>(domains, cex, |candidate: E, history: Seq<E>|
            s::rule_violated(rules[rule as int], candidate, history)
                && !s::policy_denies(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), candidate, history)),
    ensures q::every_instance::<E>(domains, cex, |candidate: E, history: Seq<E>|
            s::policy_denies(policy.map(|_i: int, id: nat| rules[id as int]), candidate, history)
                && !s::policy_denies(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), candidate, history)),
        q::has_instance::<E>(domains, cex) ==> !q::redundant_in(domains,
            policy.map(|_i: int, id: nat| rules[id as int]),
            q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int])),
{
    assert forall|candidate: E, history: Seq<E>| #[trigger] q::instance::<E>(domains, cex, candidate, history)
        implies (s::policy_denies(policy.map(|_i: int, id: nat| rules[id as int]), candidate, history)
            && !s::policy_denies(q::without_rule(policy, rule).map(|_i: int, id: nat| rules[id as int]), candidate, history)) by {
        lemma_policy_denies_without_rule(rules, rule, policy, candidate, history);
    }
    if q::has_instance::<E>(domains, cex) {
        let (candidate, history) = choose|candidate: E, history: Seq<E>|
            #[trigger] q::instance::<E>(domains, cex, candidate, history);
        assert(q::in_domains(domains, candidate, history));
    }
}

} // verus!
