//! Top layer: what the analyzer's verdicts mean (`history-analysis/src/analyzer.rs`), against
//! the typed semantics of `semantics`.
//!
//! `history-analysis` is Verus-checked. This module fixes the *view* of its state and results
//! and the predicate each query's result must satisfy. `PolicyAnalyzer::tail_included` is the
//! executable query and is verified to ensure `tail_included_ok`; the other predicates specify
//! policy-level questions that `semantics` and `inclusion` reduce to tail inclusions, but have no
//! executable entry point. The postconditions are
//!
//! ```text
//! covered(&self, rule, by)            ensures r matches Ok(v) ==> covered_ok(self@, rule@, by@, v.inclusion@)
//! redundant(&self, rule, policy)      ensures r matches Ok(v) ==> redundant_ok(self@, rule@, policy@, v.inclusion@)
//! at_least_as_strict(&self, p, q)     ensures r matches Ok(v) ==> at_least_as_strict_ok(self@, p@, q@, v.inclusion@)
//! never_fires(&self, rule)            ensures r matches Ok(v) ==> never_fires_ok(self@, rule@, v.inclusion@)
//! always_fires(&self, rule)           ensures r matches Ok(v) ==> always_fires_ok(self@, rule@, v.inclusion@)
//! tail_included(&mut self, h, l, r)   ensures r matches Ok(v) ==> tail_included_ok(final(self)@, h@, l@, r@, v.inclusion@)
//! add_rule(&mut self, rule)           ensures r matches Ok(id) ==> final(self)@.rules == old(self)@.rules.push(rule@)
//!                                         && id@ == old(self)@.rules.len() && semantics::rule_wf(rule@)
//! ```
//!
//! `Exhausted` (the graph budget) and `Err` carry no claim; they are explicit, never a silent
//! `Holds`. Termination of every query is part of verifying the exec code (loops with
//! `decreases`). Finitely many reachable items, the hypothesis of
//! `search::stmt_search_terminates`, is established for the executed search
//! (`theorem_retained_search_bounded` and `lemma_running_outcome` in
//! `history-analysis/src/verify/search_exec.rs`), so every search trace is bounded independently
//! of the budget.
use super::semantics::*;
use history_store::typed::verify::eq_equivalence;
use history_syntax::verify::dsl::{HeadView, RegexView, RuleView};
use junco_core::verify::dsl as tdsl;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// `Value<T>`: a constant, or a numbered value of an unrestricted component that equals no
/// constant known to the analyzer.
pub enum ValueView<T> { Constant(T), Fresh(nat) }

pub type ComponentsView<C> = Seq<ValueView<C>>;

/// `Counterexample<E>`: a candidate and a history (oldest first).
pub struct CexView<C> { pub candidate: ComponentsView<C>, pub history: Seq<ComponentsView<C>> }

/// `Inclusion<E>`.
pub enum InclusionView<C> { Holds, Counterexample(CexView<C>), Exhausted }

/// `PolicyAnalyzer<E>`: declared domains, the added rules (indexed by `RuleId`), and the
/// constants it knows per component (rule constants and declared domain values).
pub struct AnalyzerView<C> {
    pub domains: DomainsView<C>,
    pub rules: Seq<RuleView<C>>,
    pub known: Seq<Set<C>>,
}

/// Every added rule is well formed and its constants are known.
pub open spec fn analyzer_wf<C: PartialEq>(a: AnalyzerView<C>) -> bool {
    &&& 1 <= a.domains.len() <= history_syntax::MAX_ARITY
    &&& a.known.len() == a.domains.len()
    &&& forall|i: int| 0 <= i < a.rules.len() ==> rule_wf(#[trigger] a.rules[i])
        && a.rules[i].head.len() == a.domains.len()
        && forall|j: int| 0 <= j < a.domains.len() ==> rule_constants(a.rules[i])[j].subset_of(a.known[j])
}

// ----- instantiating fresh values -----

/// Per-component choice of a value for each fresh number.
pub type FreshChoice<C> = Seq<spec_fn(nat) -> C>;

pub open spec fn value_of<T>(v: ValueView<T>, f: spec_fn(nat) -> T) -> T {
    match v { ValueView::Constant(c) => c, ValueView::Fresh(n) => f(n) }
}

pub open spec fn event_of<C>(c: ComponentsView<C>, f: FreshChoice<C>) -> Seq<C> {
    Seq::new(c.len(), |i: int| value_of(c[i], f[i]))
}

pub open spec fn history_of<C>(cex: CexView<C>, f: FreshChoice<C>) -> Seq<Seq<C>> {
    cex.history.map(|i: int, c: ComponentsView<C>| event_of(c, f))
}

/// Fresh numbers used at one component.
pub open spec fn fresh_used<C>(cex: CexView<C>, coordinate: int) -> ISet<nat> {
    ISet::new(|n: nat| (0 <= coordinate < cex.candidate.len()
        && cex.candidate[coordinate] == ValueView::<C>::Fresh(n))
        || exists|i: int| 0 <= i < cex.history.len() && 0 <= coordinate < cex.history[i].len()
            && #[trigger] cex.history[i][coordinate] == ValueView::<C>::Fresh(n))
}

/// The shape previously guaranteed by the tuple types.
pub open spec fn cex_arity<C>(cex: CexView<C>, arity: nat) -> bool {
    cex.candidate.len() == arity
        && forall|i: int| 0 <= i < cex.history.len() ==> #[trigger] cex.history[i].len() == arity
}

/// The choice is injective on the used fresh numbers, avoids the known constants, and stays in
/// the component's domain.
pub open spec fn choice_ok<T: PartialEq>(f: spec_fn(nat) -> T, used: ISet<nat>, known: Set<T>, domain: Option<Set<T>>) -> bool {
    &&& forall|m: nat, n: nat| #![trigger used.contains(m), used.contains(n)]
        used.contains(m) && used.contains(n) && m != n ==> !f(m).eq_spec(&f(n))
    &&& forall|n: nat, k: T| #![trigger used.contains(n), known.contains(k)]
        used.contains(n) && known.contains(k) ==> !f(n).eq_spec(&k)
    &&& forall|n: nat| #[trigger] used.contains(n) ==> in_domain(domain, f(n))
}

pub open spec fn admissible<C: PartialEq>(a: AnalyzerView<C>, cex: CexView<C>, f: FreshChoice<C>) -> bool {
    &&& 1 <= a.domains.len() <= history_syntax::MAX_ARITY
    &&& a.known.len() == a.domains.len()
    &&& f.len() == a.domains.len()
    &&& cex_arity(cex, a.domains.len())
    &&& forall|i: int| 0 <= i < a.domains.len() ==> choice_ok(#[trigger] f[i],
        fresh_used(cex, i), a.known[i], a.domains[i])
}

/// Constants of a counterexample lie in their domains; fresh values occur only at unrestricted
/// components. Under `infinite_type` for those components an admissible choice exists.
pub open spec fn cex_values_ok<C: PartialEq>(a: AnalyzerView<C>, cex: CexView<C>) -> bool {
    forall|f: FreshChoice<C>| #[trigger] admissible(a, cex, f)
        ==> event_in(a.domains, event_of(cex.candidate, f)) && history_in(a.domains, history_of(cex, f))
}

/// Every admissible instantiation of the counterexample satisfies `fails`.
pub open spec fn every_instance<C: PartialEq>(
    a: AnalyzerView<C>, cex: CexView<C>,
    fails: spec_fn(Seq<C>, Seq<Seq<C>>) -> bool,
) -> bool {
    cex_values_ok(a, cex)
        && forall|f: FreshChoice<C>| #[trigger] admissible(a, cex, f) ==> fails(event_of(cex.candidate, f), history_of(cex, f))
}

// ----- minimality -----

/// `c2` agrees with `c` on equality with every known constant (so it lies in the same candidate
/// case of every split the analyzer makes).
pub open spec fn same_profile<C: PartialEq>(a: AnalyzerView<C>, c: Seq<C>, c2: Seq<C>) -> bool {
    &&& c.len() == a.domains.len() && c2.len() == a.domains.len()
    &&& a.known.len() == a.domains.len()
    &&& forall|i: int, k: C| 0 <= i < a.known.len() && #[trigger] a.known[i].contains(k)
        ==> (c[i].eq_spec(&k) == c2[i].eq_spec(&k))
}

/// No failing pair has a shorter history, among all candidates.
pub open spec fn shortest<C: PartialEq>(
    a: AnalyzerView<C>, n: nat, fails: spec_fn(Seq<C>, Seq<Seq<C>>) -> bool,
) -> bool {
    forall|c: Seq<C>, h: Seq<Seq<C>>| event_in(a.domains, c) && history_in(a.domains, h) && h.len() < n
        ==> !#[trigger] fails(c, h)
}

/// No failing pair has a shorter history among candidates with the profile of `c`
/// (minimum length per inclusion query, Theorem Inclusion search correctness `thm:search`).
pub open spec fn shortest_in_case<C: PartialEq>(
    a: AnalyzerView<C>, c: Seq<C>, n: nat, fails: spec_fn(Seq<C>, Seq<Seq<C>>) -> bool,
) -> bool {
    forall|c2: Seq<C>, h: Seq<Seq<C>>| event_in(a.domains, c2) && history_in(a.domains, h) && h.len() < n
        && same_profile(a, c, c2) ==> !#[trigger] fails(c2, h)
}

// ----- query contracts -----

pub open spec fn rules_of<C>(a: AnalyzerView<C>, ids: Seq<nat>) -> Seq<RuleView<C>> {
    ids.map(|i: int, id: nat| a.rules[id as int])
}

/// `rule` denies and no rule of `p` does.
pub open spec fn uncovered<C: PartialEq>(
    p: Seq<RuleView<C>>, rule: RuleView<C>,
) -> spec_fn(Seq<C>, Seq<Seq<C>>) -> bool {
    |c: Seq<C>, h: Seq<Seq<C>>| rule_denies(rule, c, h) && !policy_denies(p, c, h)
}

/// `covered(rule, by)`: Holds iff covered; a counterexample is denied by `rule` and by no rule of
/// `by`, shortest within its candidate case.
pub open spec fn covered_ok<C: PartialEq>(
    a: AnalyzerView<C>, rule: nat, by: Seq<nat>, v: InclusionView<C>,
) -> bool {
    let p = rules_of(a, by);
    let r = a.rules[rule as int];
    match v {
        InclusionView::Holds => covers(a.domains, p, r),
        InclusionView::Counterexample(cex) => every_instance(a, cex, uncovered(p, r))
            && forall|f: FreshChoice<C>| #[trigger] admissible(a, cex, f)
                ==> shortest_in_case(a, event_of(cex.candidate, f), cex.history.len(), uncovered(p, r)),
        InclusionView::Exhausted => true,
    }
}

/// `redundant(rule, policy)`: `covered(rule, policy without every occurrence of rule)`.
pub open spec fn redundant_ok<C: PartialEq>(
    a: AnalyzerView<C>, rule: nat, policy: Seq<nat>, v: InclusionView<C>,
) -> bool {
    covered_ok(a, rule, policy.filter(|id: nat| id != rule), v)
}

/// `at_least_as_strict(p, q)`: Holds iff `p ⊑ q`; a counterexample is permitted by `p` and
/// denied by some rule of `q`, shortest for that rule within its candidate case.
pub open spec fn at_least_as_strict_ok<C: PartialEq>(
    a: AnalyzerView<C>, p: Seq<nat>, q: Seq<nat>, v: InclusionView<C>,
) -> bool {
    let pp = rules_of(a, p);
    let qq = rules_of(a, q);
    match v {
        InclusionView::Holds => refines(a.domains, pp, qq),
        InclusionView::Counterexample(cex) => exists|j: int| 0 <= j < qq.len()
            && every_instance(a, cex, #[trigger] uncovered(pp, qq[j]))
            && forall|f: FreshChoice<C>| #[trigger] admissible(a, cex, f)
                ==> shortest_in_case(a, event_of(cex.candidate, f), cex.history.len(), uncovered(pp, qq[j])),
        InclusionView::Exhausted => true,
    }
}

pub open spec fn denies_fn<C: PartialEq>(
    rule: RuleView<C>,
) -> spec_fn(Seq<C>, Seq<Seq<C>>) -> bool {
    |c: Seq<C>, h: Seq<Seq<C>>| rule_denies(rule, c, h)
}

pub open spec fn grants_matching<C: PartialEq>(
    rule: RuleView<C>,
) -> spec_fn(Seq<C>, Seq<Seq<C>>) -> bool {
    |c: Seq<C>, h: Seq<Seq<C>>| tdsl::head_matches(rule.head, c) && !rule_denies(rule, c, h)
}

/// `never_fires(rule)`: Holds iff the rule never denies; a counterexample is a pair it denies,
/// of minimum length.
pub open spec fn never_fires_ok<C: PartialEq>(
    a: AnalyzerView<C>, rule: nat, v: InclusionView<C>,
) -> bool {
    let r = a.rules[rule as int];
    match v {
        InclusionView::Holds => never_denies(a.domains, r),
        InclusionView::Counterexample(cex) => every_instance(a, cex, denies_fn(r))
            && shortest(a, cex.history.len(), denies_fn(r)),
        InclusionView::Exhausted => true,
    }
}

/// `always_fires(rule)`: Holds iff the rule denies every matching candidate after every
/// history; a counterexample is a matching candidate and a history it grants, of minimum length.
pub open spec fn always_fires_ok<C: PartialEq>(
    a: AnalyzerView<C>, rule: nat, v: InclusionView<C>,
) -> bool {
    let r = a.rules[rule as int];
    match v {
        InclusionView::Holds => always_denies(a.domains, r),
        InclusionView::Counterexample(cex) => every_instance(a, cex, grants_matching(r))
            && shortest(a, cex.history.len(), grants_matching(r)),
        InclusionView::Exhausted => true,
    }
}

pub open spec fn tail_fails<C: PartialEq>(
    head: HeadView<C>, left: RegexView<C>, right: RegexView<C>,
) -> spec_fn(Seq<C>, Seq<Seq<C>>) -> bool {
    |c: Seq<C>, h: Seq<Seq<C>>| tdsl::head_matches(head, c)
        && tdsl::lang(left, head, c, h) && !tdsl::lang(right, head, c, h)
}

/// `tail_included(head, left, right)`, read against the analyzer after the call (it interns the
/// tails' constants): Holds iff the inclusion holds for every matching candidate; a
/// counterexample is a matching candidate with a history in `left` but not `right`, of minimum
/// length.
pub open spec fn tail_included_ok<C: PartialEq>(
    a: AnalyzerView<C>, head: HeadView<C>, left: RegexView<C>, right: RegexView<C>,
    v: InclusionView<C>,
) -> bool {
    match v {
        InclusionView::Holds => tails_included(a.domains, head, left, right),
        InclusionView::Counterexample(cex) => every_instance(a, cex, tail_fails(head, left, right))
            && shortest(a, cex.history.len(), tail_fails(head, left, right)),
        InclusionView::Exhausted => true,
    }
}

/// Existence of admissible choices: with infinite types at the unrestricted components whose
/// `eq_spec` is an equivalence (implied by `books::native_obligations`, see
/// `history_store::typed::verify::lemma_native_obligations_eq_equivalence`), every counterexample
/// has an admissible instantiation, so `every_instance` is not vacuous.
pub open spec fn stmt_choice_exists<C: PartialEq>() -> bool {
    forall|a: AnalyzerView<C>, cex: CexView<C>| #![trigger infinite_domains(a.domains), fresh_finite(cex)]
        eq_equivalence::<C>() && infinite_domains(a.domains) && fresh_finite(cex)
            && a.known.len() == a.domains.len() && cex_arity(cex, a.domains.len())
            ==> exists|f: FreshChoice<C>| #[trigger] admissible(a, cex, f)
}

pub open spec fn fresh_finite<C>(cex: CexView<C>) -> bool {
    forall|i: int| 0 <= i < cex.candidate.len() ==> #[trigger] fresh_used(cex, i).finite()
}


// ----- proofs -----

/// An injective choice avoiding `known` exists for every finite set of fresh numbers, given an
/// infinite type whose `eq_spec` is an equivalence.
pub proof fn lemma_choice_for_used<T: PartialEq>(used: ISet<nat>, known: Set<T>) -> (f: spec_fn(nat) -> T)
    requires
        used.finite(),
        infinite_type::<T>(),
        eq_equivalence::<T>(),
    ensures choice_ok(f, used, known, None),
    decreases used.len(),
{
    vstd::iset_lib::lemma_iset_empty_equivalency_len(used);
    if used.len() == 0 {
        assert(used == ISet::<nat>::empty());
        |n: nat| known.choose()
    } else {
        let a = used.choose();
        assert(used.contains(a));
        let rest = used.remove(a);
        assert(rest.len() < used.len());
        let f0 = lemma_choice_for_used(rest, known);
        rest.lemma_map_finite(f0);
        let img = Set::new_from_iset(rest.map(f0)).unwrap();
        let avoid = known.union(img);
        assert(has_missing(avoid));
        let v = choose|v: T| #[trigger] misses(avoid, v);
        let f = |n: nat| if n == a { v } else { f0(n) };
        assert forall|m: nat, n: nat| #![trigger used.contains(m), used.contains(n)]
            used.contains(m) && used.contains(n) && m != n implies !f(m).eq_spec(&f(n)) by {
            if m == a {
                assert(rest.contains(n));
                assert(rest.map(f0).contains(f0(n)));
                assert(avoid.contains(f0(n)));
            } else if n == a {
                assert(rest.contains(m));
                assert(rest.map(f0).contains(f0(m)));
                assert(avoid.contains(f0(m)));
                assert(!v.eq_spec(&f0(m)));
                assert(f0(m).eq_spec(&v) == v.eq_spec(&f0(m)));
            } else {
                assert(rest.contains(m) && rest.contains(n));
            }
        }
        assert forall|n: nat, k: T| #![trigger used.contains(n), known.contains(k)]
            used.contains(n) && known.contains(k) implies !f(n).eq_spec(&k) by {
            if n == a {
                assert(avoid.contains(k));
            } else {
                assert(rest.contains(n));
            }
        }
        f
    }
}

pub proof fn theorem_choice_exists<C: PartialEq>()
    ensures stmt_choice_exists::<C>(),
{
    assert forall|a: AnalyzerView<C>, cex: CexView<C>| #![trigger infinite_domains(a.domains), fresh_finite(cex)]
        eq_equivalence::<C>() && infinite_domains(a.domains) && fresh_finite(cex)
            && a.known.len() == a.domains.len() && cex_arity(cex, a.domains.len())
        implies exists|f: FreshChoice<C>| #[trigger] admissible(a, cex, f) by {
        assert forall|i: int| #![trigger fresh_used(cex, i)] 0 <= i < a.domains.len() implies
            exists|f: spec_fn(nat) -> C| choice_ok(f, fresh_used(cex, i), a.known[i], None) by {
            let f = lemma_choice_for_used(fresh_used(cex, i), a.known[i]);
        }
        let f = Seq::new(a.domains.len(), |i: int| choose|f: spec_fn(nat) -> C|
            choice_ok(f, fresh_used(cex, i), a.known[i], None));
        assert forall|i: int| 0 <= i < a.domains.len() implies choice_ok(#[trigger] f[i],
            fresh_used(cex, i), a.known[i], a.domains[i]) by {
            assert(a.domains[i] is None);
        }
        assert(admissible(a, cex, f));
    }
}

} // verus!
