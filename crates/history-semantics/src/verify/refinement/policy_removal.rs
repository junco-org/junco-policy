//! Decision preservation for removing every occurrence of a rule id, independently of policy
//! order and duplicate ids. An absent id retains the existing coverage-query interpretation.

use super::analyzer::{
    self, AnalyzerView, CexView, FreshChoice, InclusionView, rules_of, without_rule,
};
use super::semantics::{self, covers, event_in, history_in, policy_denies, rule_denies};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq::group_seq_lemmas;

/// Removing all occurrences of `rule` leaves every admissible deny/permit decision unchanged.
pub open spec fn removal_preserves_decisions<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>| event_in(a.domains, candidate)
        && history_in(a.domains, history)
        ==> (#[trigger] policy_denies(rules_of(a, policy), candidate, history)
            == policy_denies(rules_of(a, without_rule(policy, rule)), candidate, history))
}

/// A concrete decision changed by removal: the original denies, the filtered policy permits.
pub open spec fn removal_fails<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>) -> spec_fn(Seq<C>, Seq<Seq<C>>) -> bool {
    |candidate: Seq<C>, history: Seq<Seq<C>>|
        policy_denies(rules_of(a, policy), candidate, history)
            && !policy_denies(rules_of(a, without_rule(policy, rule)), candidate, history)
}

/// The operational removal guarantee supplements, rather than changes, `redundant_correct`.
/// A counterexample to coverage changes the policy only when the target id was present.
pub open spec fn redundant_decisions_ok<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>, v: InclusionView<C>) -> bool {
    match v {
        InclusionView::Holds => removal_preserves_decisions(a, rule, policy),
        InclusionView::Counterexample(cex) => policy.contains(rule) ==> (
            analyzer::every_instance(a, cex, removal_fails(a, rule, policy))
                && (analyzer::cex_has_instance(a, cex) ==> !removal_preserves_decisions(a, rule, policy))),
        InclusionView::Exhausted => true,
    }
}

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

/// Filtering removes exactly the denials contributed by the selected id, not by its position.
pub proof fn lemma_policy_denies_without_rule<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>, candidate: Seq<C>, history: Seq<Seq<C>>)
    requires rule < a.rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures policy_denies(rules_of(a, policy), candidate, history)
        == (policy_denies(rules_of(a, without_rule(policy, rule)), candidate, history)
            || (policy.contains(rule) && rule_denies(a.rules[rule as int], candidate, history))),
{
    let others = without_rule(policy, rule);
    let full = rules_of(a, policy);
    let filtered = rules_of(a, others);
    if policy_denies(full, candidate, history) {
        let j = choose|j: int| 0 <= j < full.len() && #[trigger] rule_denies(full[j], candidate, history);
        if policy[j] == rule {
            assert(policy.contains(rule));
        } else {
            lemma_without_rule_contains(policy, rule, policy[j]);
            assert(others.contains(policy[j]));
            let k = choose|k: int| 0 <= k < others.len() && others[k] == policy[j];
            assert(filtered[k] == full[j]);
            assert(rule_denies(filtered[k], candidate, history));
        }
    }
    if policy_denies(filtered, candidate, history) {
        let k = choose|k: int| 0 <= k < filtered.len() && #[trigger] rule_denies(filtered[k], candidate, history);
        assert(others.contains(others[k]));
        lemma_without_rule_contains(policy, rule, others[k]);
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == others[k];
        assert(full[j] == filtered[k]);
        assert(rule_denies(full[j], candidate, history));
    }
    if policy.contains(rule) && rule_denies(a.rules[rule as int], candidate, history) {
        let j = choose|j: int| 0 <= j < policy.len() && policy[j] == rule;
        assert(full[j] == a.rules[rule as int]);
        assert(rule_denies(full[j], candidate, history));
    }
}

/// If present, the selected rule can be moved to the end after deleting all its occurrences,
/// without changing the policy's existential denial semantics.
pub proof fn lemma_policy_denies_removal_push<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>, candidate: Seq<C>, history: Seq<Seq<C>>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures policy_denies(rules_of(a, policy), candidate, history)
        == policy_denies(rules_of(a, without_rule(policy, rule)).push(a.rules[rule as int]), candidate, history),
{
    lemma_policy_denies_without_rule(a, rule, policy, candidate, history);
    semantics::lemma_policy_denies_push(rules_of(a, without_rule(policy, rule)),
        a.rules[rule as int], candidate, history);
}

/// Instantiate the existing append-shaped redundancy theorem for arbitrary order/duplicates.
pub proof fn lemma_removal_iff_covered<C: PartialEq>(a: AnalyzerView<C>, rule: nat, policy: Seq<nat>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
    ensures covers(a.domains, rules_of(a, without_rule(policy, rule)), a.rules[rule as int])
        == removal_preserves_decisions(a, rule, policy),
{
    let others = rules_of(a, without_rule(policy, rule));
    let r = a.rules[rule as int];
    semantics::theorem_redundant_iff_covered::<C>();
    assert(covers(a.domains, others, r) <==> forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(a.domains, candidate) && history_in(a.domains, history)
            ==> (#[trigger] policy_denies(others.push(r), candidate, history) == policy_denies(others, candidate, history)));
    if covers(a.domains, others, r) {
        assert forall|candidate: Seq<C>, history: Seq<Seq<C>>| event_in(a.domains, candidate)
            && history_in(a.domains, history)
            implies (#[trigger] policy_denies(rules_of(a, policy), candidate, history)
                == policy_denies(others, candidate, history)) by {
            lemma_policy_denies_removal_push(a, rule, policy, candidate, history);
        }
    }
    if removal_preserves_decisions(a, rule, policy) {
        assert forall|candidate: Seq<C>, history: Seq<Seq<C>>| event_in(a.domains, candidate)
            && history_in(a.domains, history)
            implies (#[trigger] policy_denies(others.push(r), candidate, history)
                == policy_denies(others, candidate, history)) by {
            lemma_policy_denies_removal_push(a, rule, policy, candidate, history);
        }
    }
}

/// The verified coverage verdict also describes the actual effect of removing the id.
pub proof fn lemma_redundant_decisions<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>, v: InclusionView<C>)
    requires rule < a.rules.len(),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
        analyzer::redundant_correct(a, rule, policy, v),
    ensures redundant_decisions_ok(a, rule, policy, v),
{
    match v {
        InclusionView::Holds => {
            if policy.contains(rule) {
                lemma_removal_iff_covered(a, rule, policy);
            } else {
                assert forall|candidate: Seq<C>, history: Seq<Seq<C>>| event_in(a.domains, candidate)
                    && history_in(a.domains, history)
                    implies (#[trigger] policy_denies(rules_of(a, policy), candidate, history)
                        == policy_denies(rules_of(a, without_rule(policy, rule)), candidate, history)) by {
                    lemma_policy_denies_without_rule(a, rule, policy, candidate, history);
                }
            }
        },
        InclusionView::Counterexample(cex) => {
            if policy.contains(rule) {
                assert forall|f: FreshChoice<C>| #[trigger] analyzer::admissible(a, cex, f)
                    implies removal_fails(a, rule, policy)(analyzer::event_of(cex.candidate, f), analyzer::history_of(cex, f)) by {
                    lemma_policy_denies_without_rule(a, rule, policy,
                        analyzer::event_of(cex.candidate, f), analyzer::history_of(cex, f));
                }
                if analyzer::cex_has_instance(a, cex) {
                    let f = choose|f: FreshChoice<C>| #[trigger] analyzer::admissible(a, cex, f);
                    let candidate = analyzer::event_of(cex.candidate, f);
                    let history = analyzer::history_of(cex, f);
                    assert(event_in(a.domains, candidate) && history_in(a.domains, history));
                    assert(removal_fails(a, rule, policy)(candidate, history));
                    assert(!removal_preserves_decisions(a, rule, policy));
                }
            }
        },
        InclusionView::Exhausted => {},
    }
}

/// A realizable coverage counterexample explicitly witnesses that removal changes a decision.
pub proof fn lemma_redundant_counterexample_refutes<C: PartialEq>(a: AnalyzerView<C>, rule: nat,
    policy: Seq<nat>, cex: CexView<C>)
    requires rule < a.rules.len(), policy.contains(rule),
        forall|i: int| 0 <= i < policy.len() ==> #[trigger] policy[i] < a.rules.len(),
        analyzer::redundant_correct(a, rule, policy, InclusionView::Counterexample(cex)),
        analyzer::cex_has_instance(a, cex),
    ensures !removal_preserves_decisions(a, rule, policy),
{
    lemma_redundant_decisions(a, rule, policy, InclusionView::Counterexample(cex));
}
}
