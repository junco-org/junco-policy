//! The policy reduction composed with the inclusion search: per-case search outcomes decide
//! whether a policy covers a rule (`stmt_policy_reduction` with `search::outcome_ok`).
//!
//! The analyzer answers `covered(R, P)` by one constrained inclusion per case `Γ'` of a split of
//! the head constraint `Γ_R` on the head constants `Π` of `P`, searching `ρ_R ⊑_{Γ'} Σ firing(Γ')`
//! (`inclusion::firing_denials`). `stmt_policy_outcomes` reads the per-case outcomes back as
//! answers about `R` and `P`: every case holding means `P` covers `R`; a case's refutation is
//! realized only by pairs that `R` denies and `P` permits, and no such pair in the case is
//! shorter.
use super::encoding::*;
use super::inclusion::*;
use super::search::*;
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

verus! {

/// Within the case `g1`, the inclusion counterexamples of `ρ_R ⊑_{g1} Σ firing(g1)` are exactly the
/// pairs that `rule` denies and no rule of `p` denies.
pub open spec fn case_cex_uncovered(d: NDomains, p: Seq<NRule>, rule: NRule, g1: Constraint) -> bool {
    forall|theta: Subst, w: Seq<EventView>|
        #[trigger] inclusion_cex(d, g1, denial(rule), firing_denials(d, p, g1), theta, w)
            <==> (n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g1)
                && n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w))
}

/// Every admissible realization `(θ, u)` of the refutation `(g, letters)` is denied by `rule` and by
/// no rule of `p`.
pub open spec fn realizations_uncovered(d: NDomains, p: Seq<NRule>, rule: NRule, g: Constraint,
    letters: Seq<Assignment>) -> bool {
    forall|theta: Subst, u: Seq<EventView>| n_theta_ok(d, theta) && sat_by(theta, g)
        && #[trigger] follows(d, letters, theta, u)
        ==> n_rule_denies(rule, theta, u) && !n_policy_denies(p, theta, u)
}

/// No pair satisfying the case `g1` with a history shorter than `n` is denied by `rule` and by no
/// rule of `p`.
pub open spec fn no_uncovered_shorter(d: NDomains, p: Seq<NRule>, rule: NRule, g1: Constraint, n: nat) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g1)
        && w.len() < n ==> !(#[trigger] n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w))
}

/// The policy reduction (`stmt_policy_reduction`) composed with the search's outcomes
/// (`outcome_ok`, Theorem Inclusion search correctness `thm:search`). For any family of cases
/// with `split_ok` on the head constants of `p`:
/// - in each case, the inclusion counterexamples are the pairs of the case that `rule` denies
///   and `p` permits;
/// - if the inclusion holds in every case, `p` covers `rule`;
/// - a refutation of one case's inclusion is realized only by pairs that `rule` denies and `p`
///   permits, and no such pair satisfying the case has a shorter history.
pub open spec fn stmt_policy_outcomes() -> bool {
    forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>|
        #[trigger] split_ok(d, head_constraint(rule.head), head_pairs(p), cases) ==> {
            &&& forall|g1: Constraint| #[trigger] cases.contains(g1) ==> case_cex_uncovered(d, p, rule, g1)
            &&& (forall|g1: Constraint| #[trigger] cases.contains(g1)
                    ==> outcome_ok(d, g1, denial(rule), firing_denials(d, p, g1), Outcome::Holds))
                ==> n_covers(d, p, rule)
            &&& forall|g1: Constraint, g: Constraint, letters: Seq<Assignment>| cases.contains(g1)
                && #[trigger] outcome_ok(d, g1, denial(rule), firing_denials(d, p, g1), Outcome::Refuted(g, letters))
                ==> realizations_uncovered(d, p, rule, g, letters)
                    && no_uncovered_shorter(d, p, rule, g1, letters.len())
        }
}

} // verus!
