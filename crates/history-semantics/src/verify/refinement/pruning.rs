//! Layer 4: pruning (`inclusion.tex:281-330`, `appendix.tex:525-665`).
//!
//! The search may discard an item at insertion when `search::may_discard` holds. This layer
//! states that the implemented checks (dead items, domination up to a sound simulation) imply it.
//! The simulation rules are those of the current code (`history-analysis/src/simulation.rs`,
//! uncommitted version), which extend the paper's Figure `fig:simulation`.
use super::encoding::*;
use super::inclusion::*;
use super::search::*;
use alloc::boxed::Box;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

/// `L_θ(x) ⊆ L_θ(y)` for every admissible `θ`.
pub open spec fn lang_le(x: Regex<model::Test>, y: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta) && #[trigger] n_lang(theta, x, w) ==> n_lang(theta, y, w)
}

pub open spec fn test_le_sem(x: model::Test, y: model::Test) -> bool {
    forall|theta: Subst, e: EventView| language::event_wf(theta) && #[trigger] model::test_holds(theta, x, e) ==> model::test_holds(theta, y, e)
}

/// `≤` is sound (`appendix.tex:544-546`).
pub open spec fn sim_sound(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool) -> bool {
    forall|x: Regex<model::Test>, y: Regex<model::Test>| #[trigger] le(x, y) ==> lang_le(x, y)
}

pub open spec fn test_sim_sound(tle: spec_fn(model::Test, model::Test) -> bool) -> bool {
    forall|x: model::Test, y: model::Test| #[trigger] tle(x, y) ==> test_le_sem(x, y)
}

/// Operands of `q` for `&` (`+`): its operands if it is an intersection (union), else `{q}`.
pub open spec fn inter_ops(q: Regex<model::Test>) -> Seq<Regex<model::Test>> {
    match q { Regex::Intersect(cs) => cs, _ => seq![q] }
}

pub open spec fn union_ops(q: Regex<model::Test>) -> Seq<Regex<model::Test>> {
    match q { Regex::Union(cs) => cs, _ => seq![q] }
}

/// `dec(q) = (P, N)` (Definition B.2, `appendix.tex:528-541`).
pub open spec fn required(q: Regex<model::Test>, p: Regex<model::Test>) -> bool {
    inter_ops(q).contains(p) && !(p is Not)
}

pub open spec fn excluded(q: Regex<model::Test>, n: Regex<model::Test>) -> bool {
    exists|v: Regex<model::Test>| #[trigger] inter_ops(q).contains(Regex::Not(Box::new(v))) && union_ops(v).contains(n)
}

/// Equation `eq:decomposition`: `L_θ(q) = ⋂_{p∈P} L_θ(p) \ ⋃_{n∈N} L_θ(n)`.
pub open spec fn stmt_decomposition() -> bool {
    forall|q: Regex<model::Test>, theta: Subst, w: Seq<EventView>| #[trigger] n_lang(theta, q, w) == (
        (forall|p: Regex<model::Test>| #[trigger] required(q, p) ==> n_lang(theta, p, w))
        && (forall|n: Regex<model::Test>| #[trigger] excluded(q, n) ==> !n_lang(theta, n, w)))
}

/// Dead test (Definition B.3, `appendix.tex:547-551`).
pub open spec fn dead(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, q: Regex<model::Test>) -> bool {
    exists|p: Regex<model::Test>| #[trigger] required(q, p) && forall|v: Regex<model::Test>| #[trigger] union_ops(p).contains(v)
        ==> exists|n: Regex<model::Test>| #[trigger] excluded(q, n) && le(v, n)
}

/// Domination `J ⊑ I` (Definition B.3, `appendix.tex:552-557`).
pub open spec fn dominated(d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, j: Item, i: Item) -> bool {
    &&& entails(d, j.constraint, i.constraint)
    &&& forall|p: Regex<model::Test>| #[trigger] required(i.state, p) ==> required(j.state, p)
    &&& forall|n: Regex<model::Test>| #[trigger] excluded(i.state, n) ==> exists|n2: Regex<model::Test>| #[trigger] excluded(j.state, n2) && le(n, n2)
}

/// Lemma B.4 (pruning soundness): a dead item has no witnesses, and `J ⊑ I` gives `W(J) ⊆ W(I)`.
pub open spec fn stmt_prune_sound() -> bool {
    forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, j: Item, i: Item|
        #[trigger] sim_sound(le) ==> {
            &&& (dead(le, j.state) ==> no_witness(d, j))
            &&& (#[trigger] dominated(d, le, j, i) ==> witnesses_within(d, j, i))
        }
}

/// One rule of the code's term simulation, with premises read from `le` and `tle`.
pub open spec fn sim_step(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    tle: spec_fn(model::Test, model::Test) -> bool, x: Regex<model::Test>, y: Regex<model::Test>) -> bool {
    ||| x == y                                                     // Refl
    ||| x is Empty                                                 // Zero
    ||| y is All                                                   // One
    ||| x is Epsilon && language::nullable(y)                      // Eps
    ||| (x matches Regex::Union(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(cs[i], y))        // SumL
    ||| (y matches Regex::Union(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(x, cs[i]))         // SumR
    ||| (x matches Regex::Intersect(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(cs[i], y))     // AndL
    ||| (y matches Regex::Intersect(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(x, cs[i]))    // AndR
    ||| (x matches Regex::Not(a) && y matches Regex::Not(b) && le(*b, *a))                                   // Not
    ||| (x matches Regex::Test(f) && y matches Regex::Test(g) && tle(f, g))                                  // tests
    ||| (x matches Regex::Star(a) && y matches Regex::Star(b) && le(*a, *b))                                 // Star
    ||| (y matches Regex::Star(b) && le(x, *b))                                                              // StarI
    ||| (y matches Regex::Concat(ys) && cat_padded(le, x, ys))                                               // Cat, PadL, PadR
}

/// `x`'s factors (its list, or `x` itself) match `ys` pointwise after dropping `a` leading and
/// `b` trailing `Univ` factors of `ys`.
pub open spec fn cat_padded(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    x: Regex<model::Test>, ys: Seq<Regex<model::Test>>) -> bool {
    let xs = match x { Regex::Concat(cs) => cs, _ => seq![x] };
    exists|a: nat, b: nat| #[trigger] padding_ok(ys, a, b, xs.len())
        && forall|i: int| 0 <= i < xs.len() ==> #[trigger] le(xs[i], ys[a + i])
}

pub open spec fn padding_ok(ys: Seq<Regex<model::Test>>, a: nat, b: nat, len: nat) -> bool {
    a + b + len == ys.len()
        && forall|i: int| (0 <= i < a || ys.len() - b <= i < ys.len()) ==> #[trigger] ys[i] is All
}

/// One rule of the code's test simulation (`simulation.rs:278-332`).
pub open spec fn test_step(tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test) -> bool {
    ||| x == y
    ||| y is True
    ||| x is False
    ||| (x matches model::Test::Or(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(cs[i], y))
    ||| (y matches model::Test::And(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(x, cs[i]))
    ||| (x matches model::Test::And(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(cs[i], y))
    ||| (y matches model::Test::Or(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(x, cs[i]))
}

/// Lemma B.6 (simulation soundness), rule by rule: each rule applied to sound premises gives a
/// sound conclusion; by induction on derivations the least relation closed under the rules,
/// and any relation the memoized recursion computes inside it, is sound.
pub open spec fn stmt_sim_rules_sound() -> bool {
    forall|le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, tle: spec_fn(model::Test, model::Test) -> bool,
        x: Regex<model::Test>, y: Regex<model::Test>|
        sim_sound(le) && test_sim_sound(tle) && #[trigger] sim_step(le, tle, x, y) ==> lang_le(x, y)
}

pub open spec fn stmt_test_rules_sound() -> bool {
    forall|tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test|
        test_sim_sound(tle) && #[trigger] test_step(tle, x, y) ==> test_le_sem(x, y)
}

/// The implemented insertion checks discharge `search::may_discard`: the dead check gives no
/// witnesses, and domination by an earlier node gives `W(J) ⊆ W(K)`.
pub open spec fn stmt_checks_discard() -> bool {
    forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, nodes: Seq<Node>, j: Item, depth: nat|
        #[trigger] sim_sound(le) && (dead(le, j.state) || exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth
            && #[trigger] dominated(d, le, j, nodes[k].item))
            ==> #[trigger] may_discard(d, nodes, j, depth)
}

} // verus!
