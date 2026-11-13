//! Checked index of the thirteen rows of the paper's `tab:mechanization`, in table order.
//!
//! Each `stmt_*` packages exactly the result described in its comment; the adjacent
//! `theorem_*` proves it using the development named there. This is an index, not a
//! second semantics. Definition `def:regex-lang` is indexed by its defining equations.
//! The `prop:policy` row indexes the implemented alternative reduction, **not** the
//! paper's unmechanized `Den`/appended-candidate proposition. The simulation row claims
//! soundness, not a decision procedure for the paper's larger lifted-test relation.
//!
//! Numeric matcher results use encoded events and unnormalized symbolic derivatives.
//! The genuine front-end and execution links are `encoding::stmt_front_end_denies`,
//! `compile::lemma_flat_regex`, the verified derivative/normalizer contracts, and
//! `CompiledRule::accepts_history`/`Validator::permits`; the public real-event monitor
//! contract is `spec::monitor`. Search termination is conditional on finite reachable
//! items here, discharged for the implemented normalizer by
//! `finite_impl::theorem_impl_contract` and
//! `refinement::finiteness::theorem_impl_finitely_many_items`. These statements do not
//! claim a verdict on `Exhausted` or on resource/input errors. Executable analyzer
//! guarantees and their hypotheses belong to `history_analysis::spec::analyzer`.

use super::history_algebra as algebra;
use super::refinement::{finiteness, inclusion, pruning, search, semantics};
use history_syntax::Event;
use junco_core::verify::numeric_regex as language;
use junco_core::verify::numeric_regex::{EventView, Head, Regex, SrcTest, Subst};
use vstd::prelude::*;

verus! {

/// Definition `def:regex-lang`: the numeric whole-word language has the paper's
/// constructor equations. Proved by [`theorem_regex_language`] by unfolding the definition.
/// The public typed language is `junco_core::spec::semantics::lang`; its encoding is
/// related to this algebra by `refinement::encoding::stmt_front_end_denies`.
pub open spec fn stmt_regex_language<L>(sem: spec_fn(L, EventView) -> bool,
    r: Regex<L>, w: Seq<EventView>) -> bool {
    language::numeric_lang(sem, r, w) == match r {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => w.len() == 0,
        Regex::Test(l) => w.len() == 1 && sem(l, w[0]),
        Regex::Union(cs) => exists|i: int| 0 <= i < cs.len() && language::numeric_lang(sem, cs[i], w),
        Regex::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> language::numeric_lang(sem, cs[i], w),
        Regex::Not(c) => !language::numeric_lang(sem, *c, w),
        Regex::Concat(cs) => exists|parts: Seq<Seq<EventView>>| parts.len() == cs.len()
            && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> language::numeric_lang(sem, cs[i], parts[i]),
        Regex::Star(c) => exists|parts: Seq<Seq<EventView>>| w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> language::numeric_lang(sem, *c, parts[i]),
    }
}

pub proof fn theorem_regex_language<L>(sem: spec_fn(L, EventView) -> bool,
    r: Regex<L>, w: Seq<EventView>)
    ensures stmt_regex_language(sem, r, w),
{
    reveal(language::numeric_lang);
}

/// Lemma One-step correctness (`lem:sderiv`), up to language before normalization.
/// Proved by [`theorem_symbolic_derivative_correct`] using the theorem in `history_algebra`.
pub open spec fn stmt_symbolic_derivative_correct<L>(sem: spec_fn(L, EventView) -> bool,
    e: EventView, r: Regex<L>, w: Seq<EventView>) -> bool {
    algebra::stmt_symbolic_derivative_correct(sem, e, r, w)
}

pub proof fn theorem_symbolic_derivative_correct<L>(sem: spec_fn(L, EventView) -> bool,
    e: EventView, r: Regex<L>, w: Seq<EventView>)
    ensures stmt_symbolic_derivative_correct(sem, e, r, w),
{
    algebra::theorem_symbolic_derivative_correct(sem, e, r, w);
}

/// Theorem Symbolic derivative correctness (`thm:sderiv`), iterated over the history.
/// Proved by [`theorem_symbolic_run_correct`] using `history_algebra::theorem_symbolic_run_correct`.
pub open spec fn stmt_symbolic_run_correct<L>(sem: spec_fn(L, EventView) -> bool,
    u: Seq<EventView>, r: Regex<L>) -> bool {
    algebra::stmt_symbolic_run_correct(sem, u, r)
}

pub proof fn theorem_symbolic_run_correct<L>(sem: spec_fn(L, EventView) -> bool,
    u: Seq<EventView>, r: Regex<L>)
    ensures stmt_symbolic_run_correct(sem, u, r),
{
    algebra::theorem_symbolic_run_correct(sem, u, r);
}

/// Theorem Matcher correctness (`thm:matcher`): a pair matches iff a complete head
/// substitution matches and its symbolic run accepts. Proved by [`theorem_matcher_correct`]
/// using `history_algebra::theorem_rule_decision`; `theorem_not_fired` is its unmatched case.
/// For require rules the mode reverses tail membership; the verified monitor contracts
/// state the resulting real-event denial/permission decision, including least violation.
pub open spec fn stmt_matcher_correct(head: Head, tail: Regex<SrcTest>, request: EventView,
    history: Seq<EventView>) -> bool {
    language::pair_lang(head, tail, request, history)
        == exists|theta: Subst| language::head_match(head, request, theta)
            && language::nullable(algebra::symbolic_run(algebra::src_sem(theta), history, tail))
}

pub proof fn theorem_matcher_correct(head: Head, tail: Regex<SrcTest>, request: EventView,
    history: Seq<EventView>)
    ensures stmt_matcher_correct(head, tail, request, history),
{
    if language::pair_lang(head, tail, request, history) {
        let theta = choose|theta: Subst| language::head_match(head, request, theta)
            && language::numeric_lang(algebra::src_sem(theta), tail, history);
        algebra::theorem_rule_decision(head, tail, request, history, theta);
    }
    if exists|theta: Subst| language::head_match(head, request, theta)
        && language::nullable(algebra::symbolic_run(algebra::src_sem(theta), history, tail)) {
        let theta = choose|theta: Subst| language::head_match(head, request, theta)
            && language::nullable(algebra::symbolic_run(algebra::src_sem(theta), history, tail));
        algebra::theorem_rule_decision(head, tail, request, history, theta);
    }
}

/// Proposition Similarity preserves language (`lem:similarity-language`).
/// Proved by [`theorem_similarity_preserves_language`] using the theorem in `history_algebra`.
pub open spec fn stmt_similarity_preserves_language(r: Regex<SrcTest>, s: Regex<SrcTest>,
    theta: Subst, w: Seq<EventView>) -> bool {
    algebra::similar(r, s) ==> algebra::stmt_similarity_preserves_language(r, s, theta, w)
}

pub proof fn theorem_similarity_preserves_language(r: Regex<SrcTest>, s: Regex<SrcTest>,
    theta: Subst, w: Seq<EventView>)
    ensures stmt_similarity_preserves_language(r, s, theta, w),
{
    if algebra::similar(r, s) { algebra::theorem_similarity_preserves_language(r, s, theta, w); }
}

/// Lemma Finitely many residuals (`lem:finite-states`, `app:finiteness`), conditional
/// on `finite_states::Model::contract`, not similarity alone. Proved by
/// [`theorem_finite_residuals`] using `finiteness::theorem_reachable_states_finite`.
/// The descriptive normalization, successor and bound conditions are documented once
/// in `finite_states`; only the implemented normalizer is instantiated here.
pub open spec fn stmt_finite_residuals() -> bool {
    finiteness::stmt_reachable_states_finite()
}

pub proof fn theorem_finite_residuals()
    ensures stmt_finite_residuals(),
{
    finiteness::theorem_reachable_states_finite();
}

/// Alternative to Proposition Refinement as inclusion (`prop:policy`), **not** that
/// proposition as stated: no `Den(P)` or appended candidate is mechanized. Refinement
/// reduces rule-by-rule to coverage, then numerically to one constrained inclusion per
/// split case. Proved by [`theorem_policy_reduction`] using
/// `semantics::theorem_refines_iff_covers` and `inclusion::theorem_policy_reduction`.
pub open spec fn stmt_policy_reduction<E: Event>() -> bool {
    semantics::stmt_refines_iff_covers::<E>() && inclusion::stmt_policy_reduction()
}

pub proof fn theorem_policy_reduction<E: Event>()
    ensures stmt_policy_reduction::<E>(),
{
    semantics::theorem_refines_iff_covers::<E>();
    inclusion::theorem_policy_reduction();
}

/// Redundancy and vacuity reductions (`app:policy-reduction`), in the constrained,
/// non-appended-candidate form, for forbid and require rules. Proved by
/// [`theorem_redundancy_vacuity`] using `semantics::theorem_redundant_iff_covered`
/// and `inclusion::theorem_vacuity_reductions`. Executable redundancy filters every
/// occurrence of an id; shortest policy counterexamples are only split-case-local.
pub open spec fn stmt_redundancy_vacuity<E: Event>() -> bool {
    semantics::stmt_redundant_iff_covered::<E>() && inclusion::stmt_vacuity_reductions()
}

pub proof fn theorem_redundancy_vacuity<E: Event>()
    ensures stmt_redundancy_vacuity::<E>(),
{
    semantics::theorem_redundant_iff_covered::<E>();
    inclusion::theorem_vacuity_reductions();
}

/// Equation Decomposition (`eq:decomposition`). Proved by [`theorem_decomposition`]
/// using `pruning::theorem_decomposition` for the required/excluded expression decomposition.
pub open spec fn stmt_decomposition() -> bool { pruning::stmt_decomposition() }

pub proof fn theorem_decomposition()
    ensures stmt_decomposition(),
{
    pruning::theorem_decomposition();
}

/// Lemmas Computing successors and Uniform reachability (`lem:succ`, `lem:uniform`),
/// one successor-case statement including partition and uniform-realization properties.
/// Proved by [`theorem_successor_cases`] using `search::theorem_successor_cases`.
/// This specifies semantic case families, not Algorithm `alg:succ`; finite-domain
/// cases split additionally on declared values. The executable link is
/// `history_analysis::verify::search_exec::lemma_emitted_steps`, not an unused wrapper.
pub open spec fn stmt_successor_cases() -> bool { search::stmt_successor_cases() }

pub proof fn theorem_successor_cases()
    ensures stmt_successor_cases(),
{
    search::theorem_successor_cases();
}

/// Lemma Pruning soundness (`lem:prune`). Proved by [`theorem_pruning_sound`]
/// using `pruning::theorem_prune_sound` and `pruning::theorem_checks_discard`.
/// Executable domination is a sound subset of the abstract check (indexed required
/// subsets are enumerated only up to four operands); failure to prune retains the item.
pub open spec fn stmt_pruning_sound() -> bool {
    pruning::stmt_prune_sound() && pruning::stmt_checks_discard()
}

pub proof fn theorem_pruning_sound()
    ensures stmt_pruning_sound(),
{
    pruning::theorem_prune_sound();
    pruning::theorem_checks_discard();
}

/// Lemma Simulation soundness (`lem:simulation`), **soundness only**, for the
/// implemented `sim_step`/`test_step` rules. Proved by [`theorem_simulation_sound`]
/// using `pruning::theorem_sim_rules_sound` and `pruning::theorem_test_rules_sound`.
/// The paper additionally claims decidability for its figure; that larger relation's
/// lifted-test rules are not all implemented, so that claim is not indexed as proved.
pub open spec fn stmt_simulation_sound() -> bool {
    pruning::stmt_sim_rules_sound() && pruning::stmt_test_rules_sound()
}

pub proof fn theorem_simulation_sound()
    ensures stmt_simulation_sound(),
{
    pruning::theorem_sim_rules_sound();
    pruning::theorem_test_rules_sound();
}

/// Theorem Inclusion search correctness (`thm:search`): correctness/minimum length
/// for a returning trace, plus termination conditional on finitely many reachable items.
/// Proved by [`theorem_inclusion_search`] using `search::theorem_search_correct`
/// and `search::theorem_search_terminates`. No unrestricted-domain premise is needed
/// for correctness; no inclusion claim is made for `Outcome::Exhausted`.
pub open spec fn stmt_inclusion_search() -> bool {
    search::stmt_search_correct() && search::stmt_search_terminates()
}

pub proof fn theorem_inclusion_search()
    ensures stmt_inclusion_search(),
{
    search::theorem_search_correct();
    search::theorem_search_terminates();
}

} // verus!
