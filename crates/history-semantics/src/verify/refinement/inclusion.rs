//! Layer 2: constraints, `Split`, constrained inclusion, and the policy reduction
//! (`inclusion.tex:39-100`, Proposition B.1 `appendix.tex:434-481`), over numeric rules.
use super::encoding::*;
use super::semantics::violated_by;
use crate::verify::finite_states::lemma_powerset_finite;
use alloc::boxed::Box;
use history_syntax::syntax::{Component, RuleMode};
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::iset_lib::lemma_iset_subset_finite;
use vstd::prelude::*;

verus! {

/// `x_c = value` (`equal`) or `x_c ≠ value`.
pub struct Literal { pub component: Component, pub value: nat, pub equal: bool }

/// A finite conjunction of literals (`inclusion.tex:44-45`).
pub type Constraint = Set<Literal>;

pub open spec fn literal_holds(theta: Subst, l: Literal) -> bool {
    (language::field_value(theta, l.component) == l.value) == l.equal
}

/// `θ ⊨ Γ`.
pub open spec fn sat_by(theta: Subst, g: Constraint) -> bool {
    forall|l: Literal| #[trigger] g.contains(l) ==> literal_holds(theta, l)
}

/// Satisfiable by an admissible valuation of the domain.
pub open spec fn satisfiable(d: NDomains, g: Constraint) -> bool {
    exists|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
}

/// `Γ' ⊨ Γ`, relative to the admissible valuations of the domain.
pub open spec fn entails(d: NDomains, g1: Constraint, g2: Constraint) -> bool {
    forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) ==> sat_by(theta, g2)
}

pub open spec fn eq_literal(c: Component, v: nat) -> Literal { Literal { component: c, value: v, equal: true } }

pub open spec fn ne_literal(c: Component, v: nat) -> Literal { Literal { component: c, value: v, equal: false } }

/// `Γ` decides `(x_c, v)` (`inclusion.tex:52`).
pub open spec fn decides(d: NDomains, g: Constraint, c: Component, v: nat) -> bool {
    entails(d, g, set![eq_literal(c, v)]) || entails(d, g, set![ne_literal(c, v)])
}

/// A set of pairs `(x_c, v)`.
pub type Pairs = Set<(Component, nat)>;

/// What every use of `Split(Γ; Π)` relies on (`inclusion.tex:53-58`): finitely many satisfiable
/// cases, each entailing `Γ` and deciding `Π`, that partition the admissible valuations of `Γ`.
/// The paper's `Split` (`paper_split`) is one such family; the implementation's `split` emits an
/// equivalent one with at most `n + 1` cases per register (`constraint.rs:236-281`).
pub open spec fn split_ok(d: NDomains, g: Constraint, pi: Pairs, cases: Set<Constraint>) -> bool {
    &&& forall|g1: Constraint| #[trigger] cases.contains(g1) ==> satisfiable(d, g1) && entails(d, g1, g)
        && forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] decides(d, g1, p.0, p.1)
    &&& forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
        ==> exists|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1)
    &&& forall|theta: Subst, g1: Constraint, g2: Constraint| n_theta_ok(d, theta) && cases.contains(g1) && cases.contains(g2)
        && #[trigger] sat_by(theta, g1) && #[trigger] sat_by(theta, g2) ==> g1 == g2
}

/// `Δ` has exactly one of `x_c = v`, `x_c ≠ v` for each pair of `Π` that `Γ` does not decide.
pub open spec fn split_delta(d: NDomains, g: Constraint, pi: Pairs, delta: Constraint) -> bool {
    &&& forall|l: Literal| #[trigger] delta.contains(l) ==> pi.contains((l.component, l.value)) && !decides(d, g, l.component, l.value)
    &&& forall|p: (Component, nat)| #[trigger] pi.contains(p) && !decides(d, g, p.0, p.1)
        ==> delta.contains(eq_literal(p.0, p.1)) != delta.contains(ne_literal(p.0, p.1))
}

/// The paper's `Split(Γ; Π)`: the satisfiable `Γ ∪ Δ`.
pub open spec fn paper_split(d: NDomains, g: Constraint, pi: Pairs) -> Set<Constraint> {
    Set::new(|g1: Constraint| exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
        && satisfiable(d, g1)).unwrap_or(Set::empty())
}

pub open spec fn stmt_paper_split_ok() -> bool {
    forall|d: NDomains, g: Constraint, pi: Pairs| #[trigger] split_ok(d, g, pi, paper_split(d, g, pi))
}

// ----- constrained inclusion (Definition 5.1, `inclusion.tex:60-65`) -----

/// `r ⊑_Γ s`.
pub open spec fn included_under(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g)
        && #[trigger] n_lang(theta, r, w) ==> n_lang(theta, s, w)
}

/// A counterexample: `θ ⊨ Γ` and `w ∈ L_θ(r & ¬s)`.
pub open spec fn inclusion_cex(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>,
    theta: Subst, w: Seq<EventView>) -> bool {
    n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g) && n_lang(theta, r, w) && !n_lang(theta, s, w)
}

/// Shortest counterexample length bound: no counterexample is shorter than `n`.
pub open spec fn no_cex_shorter(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, n: nat) -> bool {
    forall|theta: Subst, w: Seq<EventView>| w.len() < n ==> !#[trigger] inclusion_cex(d, g, r, s, theta, w)
}

// ----- policy reduction (`inclusion.tex:74-100`, `appendix.tex:437-481`) -----

/// Head constraint `Γ_R`.
pub open spec fn head_constraint(h: NHead) -> Constraint {
    Set::new(|l: Literal| l.equal && n_head_field(h, l.component) == Some(l.value)).unwrap_or(Set::empty())
}

/// Denial expression `ρ_R`: the tail for `forbid`, its complement for `require`.
pub open spec fn denial(rule: NRule) -> Regex<model::Test> {
    match rule.mode { RuleMode::Forbid => rule.tail, RuleMode::Require => Regex::Not(Box::new(rule.tail)) }
}

/// `Π` of Proposition B.1: `(x_c, v)` for each head constant `v` at component `c` in `P`.
pub open spec fn head_pairs(p: Seq<NRule>) -> Pairs {
    Set::new(|pair: (Component, nat)| exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
        .unwrap_or(Set::empty())
}

/// `Σ_{R' ∈ P, Γ' ⊨ Γ_R'} ρ_R'` (the empty sum is `∅`).
pub open spec fn firing_denials(d: NDomains, p: Seq<NRule>, g1: Constraint) -> Regex<model::Test> {
    let firing = p.filter(|r: NRule| entails(d, g1, head_constraint(r.head)));
    Regex::Union(firing.map(|i: int, r: NRule| denial(r)))
}

pub open spec fn n_covers(d: NDomains, p: Seq<NRule>, rule: NRule) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
        && #[trigger] n_rule_denies(rule, theta, w) ==> n_policy_denies(p, theta, w)
}

/// Proposition B.1, for any family of cases with `split_ok` (so it covers the implementation's
/// `split` as well as `paper_split`).
pub open spec fn stmt_policy_reduction() -> bool {
    forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>|
        #[trigger] split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
            ==> (n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
                ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)))
}

/// `R` never denies iff `ρ_R ⊑_{Γ_R} ∅`; `R` denies every matching candidate and history iff
/// `Univ ⊑_{Γ_R} ρ_R` (`appendix.tex:454`, `analyzer.rs:366-383`).
pub open spec fn stmt_vacuity_reductions() -> bool {
    forall|d: NDomains, rule: NRule| {
        &&& (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty)
        &&& (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                ==> #[trigger] n_rule_denies(rule, theta, w))
            <==> #[trigger] included_under(d, head_constraint(rule.head), Regex::All, denial(rule))
    }
}

// ----- proofs: finiteness of the constructed sets -----

/// A predicate bounded by a finite set defines a `Set` with exactly its members.
pub proof fn lemma_set_new_bounded<A>(f: spec_fn(A) -> bool, bound: ISet<A>)
    requires
        bound.finite(),
        forall|a: A| f(a) ==> bound.contains(a),
    ensures
        Set::new(f) is Some,
        forall|a: A| #[trigger] Set::new(f).unwrap().contains(a) == f(a),
{
    assert(ISet::new(f).subset_of(bound));
    lemma_iset_subset_finite(bound, ISet::new(f));
    assert(Set::new(f) is Some);
}

pub open spec fn head_value(h: NHead, c: Component) -> nat {
    match n_head_field(h, c) { Some(v) => v, None => 0 }
}

/// `Γ_R` has exactly the equalities `x_c = v` of the head's constants (at most three).
pub proof fn lemma_head_constraint(h: NHead)
    ensures
        forall|l: Literal| #[trigger] head_constraint(h).contains(l)
            <==> (l.equal && n_head_field(h, l.component) == Some(l.value)),
{
    let bound = ISet::<Literal>::empty().insert(eq_literal(Component::Principal, head_value(h, Component::Principal)))
        .insert(eq_literal(Component::Action, head_value(h, Component::Action)))
        .insert(eq_literal(Component::Resource, head_value(h, Component::Resource)));
    let f = |l: Literal| l.equal && n_head_field(h, l.component) == Some(l.value);
    assert forall|l: Literal| f(l) implies bound.contains(l) by {
        assert(l == eq_literal(l.component, head_value(h, l.component)));
        match l.component {
            Component::Principal => {},
            Component::Action => {},
            Component::Resource => {},
        }
    }
    lemma_set_new_bounded(f, bound);
    assert(head_constraint(h) == Set::new(f).unwrap());
}

/// A finite superset of `head_pairs(p)`.
pub open spec fn head_pairs_bound(p: Seq<NRule>) -> ISet<(Component, nat)>
    decreases p.len(),
{
    if p.len() == 0 {
        ISet::empty()
    } else {
        let h = p.last().head;
        head_pairs_bound(p.drop_last()).insert((Component::Principal, head_value(h, Component::Principal)))
            .insert((Component::Action, head_value(h, Component::Action)))
            .insert((Component::Resource, head_value(h, Component::Resource)))
    }
}

pub proof fn lemma_head_pairs_bound(p: Seq<NRule>)
    ensures
        head_pairs_bound(p).finite(),
        forall|pair: (Component, nat)| (exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
            ==> #[trigger] head_pairs_bound(p).contains(pair),
    decreases p.len(),
{
    if p.len() > 0 {
        let q = p.drop_last();
        lemma_head_pairs_bound(q);
        let h = p.last().head;
        assert forall|pair: (Component, nat)| (exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
            implies #[trigger] head_pairs_bound(p).contains(pair) by {
            let i = choose|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1);
            if i < p.len() - 1 {
                assert(q[i] == p[i]);
                assert(n_head_field(q[i].head, pair.0) == Some(pair.1));
                assert(head_pairs_bound(q).contains(pair));
            } else {
                assert(pair == (pair.0, head_value(h, pair.0)));
                match pair.0 {
                    Component::Principal => {},
                    Component::Action => {},
                    Component::Resource => {},
                }
            }
        }
    }
}

/// `Π` has exactly the head constants of `P` (finitely many).
pub proof fn lemma_head_pairs(p: Seq<NRule>)
    ensures
        forall|pair: (Component, nat)| #[trigger] head_pairs(p).contains(pair)
            <==> exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1),
{
    lemma_head_pairs_bound(p);
    let f = |pair: (Component, nat)| exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1);
    lemma_set_new_bounded(f, head_pairs_bound(p));
    assert(head_pairs(p) == Set::new(f).unwrap());
}

/// Both literals of every pair of `Π`.
pub open spec fn pair_literals(pi: Pairs) -> Set<Literal> {
    pi.map(|p: (Component, nat)| eq_literal(p.0, p.1)).union(pi.map(|p: (Component, nat)| ne_literal(p.0, p.1)))
}

/// Membership in the paper's `Split` (the defining set is finite).
pub proof fn lemma_paper_split_members(d: NDomains, g: Constraint, pi: Pairs)
    ensures
        forall|g1: Constraint| #[trigger] paper_split(d, g, pi).contains(g1)
            <==> exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
                && satisfiable(d, g1),
{
    let lits = pair_literals(pi);
    lemma_powerset_finite(lits);
    let pw = ISet::new(|s: Set<Literal>| s.subset_of(lits));
    let un = |delta: Set<Literal>| g.union(delta);
    pw.lemma_map_finite(un);
    let f = |g1: Constraint| exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
        && satisfiable(d, g1);
    assert forall|g1: Constraint| f(g1) implies pw.map(un).contains(g1) by {
        let delta = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        assert forall|l: Literal| delta.contains(l) implies lits.contains(l) by {
            let pr = (l.component, l.value);
            assert(pi.contains(pr));
            if l.equal {
                assert(l == eq_literal(pr.0, pr.1));
                assert(pi.map(|p: (Component, nat)| eq_literal(p.0, p.1)).contains(l));
            } else {
                assert(l == ne_literal(pr.0, pr.1));
                assert(pi.map(|p: (Component, nat)| ne_literal(p.0, p.1)).contains(l));
            }
        }
        assert(pw.contains(delta));
        assert(un(delta) == g1);
    }
    lemma_set_new_bounded(f, pw.map(un));
    assert(paper_split(d, g, pi) == Set::new(f).unwrap());
}

// ----- proofs: constraints -----

pub proof fn lemma_entails_subset(d: NDomains, g1: Constraint, g2: Constraint)
    requires g2.subset_of(g1),
    ensures entails(d, g1, g2),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) implies sat_by(theta, g2) by {
        assert forall|l: Literal| #[trigger] g2.contains(l) implies literal_holds(theta, l) by {
            assert(g1.contains(l));
        }
    }
}

pub proof fn lemma_entails_trans(d: NDomains, a: Constraint, b: Constraint, c: Constraint)
    requires entails(d, a, b), entails(d, b, c),
    ensures entails(d, a, c),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, a) implies sat_by(theta, c) by {
        assert(sat_by(theta, b));
    }
}

/// A constraint satisfied by `θ0` that decides every literal of `gh` (all equalities, also
/// satisfied by `θ0`) entails `gh`.
pub proof fn lemma_decided_entails(d: NDomains, g1: Constraint, gh: Constraint, theta0: Subst)
    requires
        n_theta_ok(d, theta0),
        sat_by(theta0, g1),
        sat_by(theta0, gh),
        forall|l: Literal| #[trigger] gh.contains(l) ==> l.equal && decides(d, g1, l.component, l.value),
    ensures entails(d, g1, gh),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) implies sat_by(theta, gh) by {
        assert forall|l: Literal| #[trigger] gh.contains(l) implies literal_holds(theta, l) by {
            let eq = eq_literal(l.component, l.value);
            let ne = ne_literal(l.component, l.value);
            assert(literal_holds(theta0, l));
            if entails(d, g1, set![ne]) {
                assert(sat_by(theta0, set![ne]));
                assert(set![ne].contains(ne));
                assert(false);
            }
            assert(entails(d, g1, set![eq]));
            assert(sat_by(theta, set![eq]));
            assert(set![eq].contains(eq));
            assert(l == eq);
        }
    }
}

/// Under a valuation, `Δ` is determined by `Π` and the undecided pairs.
pub proof fn lemma_delta_unique(d: NDomains, g: Constraint, pi: Pairs, d1: Constraint, d2: Constraint, theta: Subst)
    requires
        split_delta(d, g, pi, d1),
        split_delta(d, g, pi, d2),
        sat_by(theta, d1),
        sat_by(theta, d2),
    ensures d1 == d2,
{
    assert forall|l: Literal| d1.contains(l) implies d2.contains(l) by {
        lemma_delta_unique_one(d, g, pi, d1, d2, theta, l);
    }
    assert forall|l: Literal| d2.contains(l) implies d1.contains(l) by {
        lemma_delta_unique_one(d, g, pi, d2, d1, theta, l);
    }
    assert(d1 =~= d2);
}

proof fn lemma_delta_unique_one(d: NDomains, g: Constraint, pi: Pairs, d1: Constraint, d2: Constraint, theta: Subst, l: Literal)
    requires
        split_delta(d, g, pi, d1),
        split_delta(d, g, pi, d2),
        sat_by(theta, d1),
        sat_by(theta, d2),
        d1.contains(l),
    ensures d2.contains(l),
{
    let pr = (l.component, l.value);
    assert(pi.contains(pr) && !decides(d, g, pr.0, pr.1));
    let eq = eq_literal(pr.0, pr.1);
    let ne = ne_literal(pr.0, pr.1);
    assert(d2.contains(eq) != d2.contains(ne));
    assert(literal_holds(theta, l));
    if d2.contains(eq) {
        assert(literal_holds(theta, eq));
        assert(l == eq);
    } else {
        assert(literal_holds(theta, ne));
        assert(l == ne);
    }
}

pub proof fn lemma_paper_split_ok(d: NDomains, g: Constraint, pi: Pairs)
    ensures split_ok(d, g, pi, paper_split(d, g, pi)),
{
    let cases = paper_split(d, g, pi);
    lemma_paper_split_members(d, g, pi);
    assert forall|g1: Constraint| #[trigger] cases.contains(g1) implies satisfiable(d, g1) && entails(d, g1, g)
        && forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] decides(d, g1, p.0, p.1) by {
        let delta = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        lemma_entails_subset(d, g1, g);
        assert forall|p: (Component, nat)| pi.contains(p) implies #[trigger] decides(d, g1, p.0, p.1) by {
            let eq = eq_literal(p.0, p.1);
            let ne = ne_literal(p.0, p.1);
            if decides(d, g, p.0, p.1) {
                if entails(d, g, set![eq]) {
                    lemma_entails_trans(d, g1, g, set![eq]);
                } else {
                    lemma_entails_trans(d, g1, g, set![ne]);
                }
            } else if delta.contains(eq) {
                lemma_entails_subset(d, g1, set![eq]);
            } else {
                assert(delta.contains(ne));
                lemma_entails_subset(d, g1, set![ne]);
            }
        }
    }
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
        implies exists|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1) by {
        let undecided = pi.filter(|p: (Component, nat)| !decides(d, g, p.0, p.1));
        let mk = |p: (Component, nat)| Literal { component: p.0, value: p.1, equal: language::field_value(theta, p.0) == p.1 };
        let delta = undecided.map(mk);
        assert forall|l: Literal| #[trigger] delta.contains(l) implies pi.contains((l.component, l.value))
            && !decides(d, g, l.component, l.value) && literal_holds(theta, l) by {
            let p = choose|p: (Component, nat)| undecided.contains(p) && l == mk(p);
            assert((l.component, l.value) == p);
        }
        assert forall|p: (Component, nat)| #[trigger] pi.contains(p) && !decides(d, g, p.0, p.1)
            implies delta.contains(eq_literal(p.0, p.1)) != delta.contains(ne_literal(p.0, p.1)) by {
            assert(undecided.contains(p));
            assert(delta.contains(mk(p)));
            if language::field_value(theta, p.0) == p.1 {
                assert(mk(p) == eq_literal(p.0, p.1));
                assert(!literal_holds(theta, ne_literal(p.0, p.1)));
            } else {
                assert(mk(p) == ne_literal(p.0, p.1));
                assert(!literal_holds(theta, eq_literal(p.0, p.1)));
            }
        }
        assert(split_delta(d, g, pi, delta));
        let g1 = g.union(delta);
        assert(sat_by(theta, g1));
        assert(satisfiable(d, g1));
        assert(cases.contains(g1));
    }
    assert forall|theta: Subst, g1: Constraint, g2: Constraint| n_theta_ok(d, theta) && cases.contains(g1) && cases.contains(g2)
        && #[trigger] sat_by(theta, g1) && #[trigger] sat_by(theta, g2) implies g1 == g2 by {
        let d1 = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        let d2 = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g2 == g.union(delta)
            && satisfiable(d, g2);
        lemma_entails_subset(d, g1, d1);
        lemma_entails_subset(d, g2, d2);
        assert forall|l: Literal| #[trigger] d1.contains(l) implies literal_holds(theta, l) by { assert(g1.contains(l)); }
        assert forall|l: Literal| #[trigger] d2.contains(l) implies literal_holds(theta, l) by { assert(g2.contains(l)); }
        lemma_delta_unique(d, g, pi, d1, d2, theta);
    }
}

pub proof fn theorem_paper_split_ok()
    ensures stmt_paper_split_ok(),
{
    assert forall|d: NDomains, g: Constraint, pi: Pairs| #[trigger] split_ok(d, g, pi, paper_split(d, g, pi)) by {
        lemma_paper_split_ok(d, g, pi);
    }
}

// ----- proofs: policy reduction -----

/// `θ ⊨ Γ_R` iff the head matches `θ`.
pub proof fn lemma_head_sat(h: NHead, theta: Subst)
    ensures sat_by(theta, head_constraint(h)) == n_head_matches(h, theta),
{
    lemma_head_constraint(h);
    if n_head_matches(h, theta) {
        assert forall|l: Literal| #[trigger] head_constraint(h).contains(l) implies literal_holds(theta, l) by {
            assert(n_head_field(h, l.component) == Some(l.value));
        }
    }
    if sat_by(theta, head_constraint(h)) {
        assert forall|c: Component| #[trigger] n_head_field(h, c) matches Some(v) ==> language::field_value(theta, c) == v by {
            if let Some(v) = n_head_field(h, c) {
                assert(head_constraint(h).contains(eq_literal(c, v)));
            }
        }
    }
}

/// `L(ρ_R)` is the set of histories violating the rule's mode.
pub proof fn lemma_denial_lang(rule: NRule, theta: Subst, w: Seq<EventView>)
    ensures n_lang(theta, denial(rule), w) == violated_by(rule.mode, n_lang(theta, rule.tail, w)),
{
}

/// `R` denies iff `θ ⊨ Γ_R` and `w ∈ L_θ(ρ_R)`.
pub proof fn lemma_rule_denies_iff(rule: NRule, theta: Subst, w: Seq<EventView>)
    ensures n_rule_denies(rule, theta, w) == (sat_by(theta, head_constraint(rule.head)) && n_lang(theta, denial(rule), w)),
{
    lemma_head_sat(rule.head, theta);
    lemma_denial_lang(rule, theta, w);
}

/// The language of the firing denials under a case.
pub proof fn lemma_firing_lang(d: NDomains, p: Seq<NRule>, g1: Constraint, theta: Subst, w: Seq<EventView>)
    ensures
        n_lang(theta, firing_denials(d, p, g1), w) <==> exists|j: int| 0 <= j < p.len()
            && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w),
{
    let firing = p.filter(|r: NRule| entails(d, g1, head_constraint(r.head)));
    let ms = firing.map(|i: int, r: NRule| denial(r));
    assert(firing_denials(d, p, g1) == Regex::Union(ms));
    if n_lang(theta, firing_denials(d, p, g1), w) {
        let i = choose|i: int| 0 <= i < ms.len() && language::lang(model::gsem(theta), ms[i], w);
        let r = firing[i];
        assert(entails(d, g1, head_constraint(r.head)));
        assert(firing.contains(r));
        p.lemma_filter_contains_rev(|r: NRule| entails(d, g1, head_constraint(r.head)), r);
        let j = choose|j: int| 0 <= j < p.len() && p[j] == r;
        assert(n_lang(theta, denial(p[j]), w));
    }
    if exists|j: int| 0 <= j < p.len() && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w) {
        let j = choose|j: int| 0 <= j < p.len() && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w);
        assert(firing.contains(p[j]));
        let i = choose|i: int| 0 <= i < firing.len() && firing[i] == p[j];
        assert(ms[i] == denial(p[j]));
        assert(language::lang(model::gsem(theta), ms[i], w));
        language::lemma_lang_union(model::gsem(theta), ms, w);
    }
}

pub proof fn lemma_policy_reduction(d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>)
    requires split_ok(d, head_constraint(rule.head), head_pairs(p), cases),
    ensures
        n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
            ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)),
{
    let gr = head_constraint(rule.head);
    let pi = head_pairs(p);
    lemma_head_pairs(p);
    if n_covers(d, p, rule) {
        assert forall|g1: Constraint| #[trigger] cases.contains(g1)
            implies included_under(d, g1, denial(rule), firing_denials(d, p, g1)) by {
            assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g1)
                && #[trigger] n_lang(theta, denial(rule), w) implies n_lang(theta, firing_denials(d, p, g1), w) by {
                assert(entails(d, g1, gr));
                assert(sat_by(theta, gr));
                lemma_rule_denies_iff(rule, theta, w);
                assert(n_rule_denies(rule, theta, w));
                let j = choose|j: int| 0 <= j < p.len() && #[trigger] n_rule_denies(p[j], theta, w);
                let gj = head_constraint(p[j].head);
                lemma_rule_denies_iff(p[j], theta, w);
                lemma_head_constraint(p[j].head);
                assert forall|l: Literal| #[trigger] gj.contains(l) implies l.equal && decides(d, g1, l.component, l.value) by {
                    assert(n_head_field(p[j].head, l.component) == Some(l.value));
                    assert(pi.contains((l.component, l.value)));
                }
                lemma_decided_entails(d, g1, gj, theta);
                lemma_firing_lang(d, p, g1, theta, w);
            }
        }
    }
    if forall|g1: Constraint| #[trigger] cases.contains(g1) ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
            && #[trigger] n_rule_denies(rule, theta, w) implies n_policy_denies(p, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            assert(sat_by(theta, gr));
            let g1 = choose|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1);
            assert(included_under(d, g1, denial(rule), firing_denials(d, p, g1)));
            assert(n_lang(theta, firing_denials(d, p, g1), w));
            lemma_firing_lang(d, p, g1, theta, w);
            let j = choose|j: int| 0 <= j < p.len()
                && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w);
            assert(sat_by(theta, head_constraint(p[j].head)));
            lemma_rule_denies_iff(p[j], theta, w);
            assert(n_rule_denies(p[j], theta, w));
        }
    }
}

pub proof fn theorem_policy_reduction()
    ensures stmt_policy_reduction(),
{
    assert forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>|
        #[trigger] split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
        implies (n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
            ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1))) by {
        lemma_policy_reduction(d, p, rule, cases);
    }
}

pub proof fn lemma_vacuity(d: NDomains, rule: NRule)
    ensures
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty),
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                ==> #[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), Regex::All, denial(rule)),
{
    let gr = head_constraint(rule.head);
    if forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, gr)
            && #[trigger] n_lang(theta, denial(rule), w) implies n_lang(theta, Regex::Empty, w) by {
            lemma_rule_denies_iff(rule, theta, w);
        }
    }
    if included_under(d, gr, denial(rule), Regex::Empty) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
            implies !#[trigger] n_rule_denies(rule, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            if n_rule_denies(rule, theta, w) {
                assert(n_lang(theta, denial(rule), w));
            }
        }
    }
    if forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
        ==> #[trigger] n_rule_denies(rule, theta, w) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, gr)
            && #[trigger] n_lang(theta, Regex::All, w) implies n_lang(theta, denial(rule), w) by {
            lemma_rule_denies_iff(rule, theta, w);
            lemma_head_sat(rule.head, theta);
            assert(n_rule_denies(rule, theta, w));
        }
    }
    if included_under(d, gr, Regex::All, denial(rule)) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
            implies #[trigger] n_rule_denies(rule, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            lemma_head_sat(rule.head, theta);
            assert(n_lang(theta, Regex::All, w));
        }
    }
}

pub proof fn theorem_vacuity_reductions()
    ensures stmt_vacuity_reductions(),
{
    assert forall|d: NDomains, rule: NRule|
        #![trigger included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty)]
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty) by {
        lemma_vacuity(d, rule);
    }
    assert forall|d: NDomains, rule: NRule|
        #![trigger included_under(d, head_constraint(rule.head), Regex::All, denial(rule))]
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                ==> #[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), Regex::All, denial(rule)) by {
        lemma_vacuity(d, rule);
    }
}

} // verus!
