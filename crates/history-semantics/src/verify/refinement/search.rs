//! Layer 3: the symbolic search (`inclusion.tex:150-279`, `appendix.tex:483-523, 667-741`).
//!
//! States are abstract expressions `Regex<model::Test>`; the implementation's states are graph
//! ids, abstracted by `model::lift_regex` (see `implementation`). The search is specified by its
//! *traces*: the sequence of inserted items in insertion order, with parents and depths, as kept
//! by `history-analysis/src/search.rs` (`items`, `next`). Insertion-time discarding is specified
//! semantically (no witnesses, or witnesses contained in those of an earlier item); the `pruning`
//! layer shows the implemented checks imply it.
use super::encoding::*;
use super::inclusion::*;
use history_syntax::syntax::Component;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

/// A search item `(Γ, q)`.
pub struct Item { pub constraint: Constraint, pub state: Regex<model::Test> }

/// `(θ, w) ∈ W(I)` (`inclusion.tex:156-159`).
pub open spec fn witness(d: NDomains, item: Item, theta: Subst, w: Seq<EventView>) -> bool {
    n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, item.constraint) && n_lang(theta, item.state, w)
}

pub open spec fn no_witness(d: NDomains, item: Item) -> bool {
    forall|theta: Subst, w: Seq<EventView>| !#[trigger] witness(d, item, theta, w)
}

/// `W(J) ⊆ W(I)`.
pub open spec fn witnesses_within(d: NDomains, j: Item, i: Item) -> bool {
    forall|theta: Subst, w: Seq<EventView>| #[trigger] witness(d, j, theta, w) ==> witness(d, i, theta, w)
}

/// `W(I)` has a member of length `n` (used for the minimality argument).
pub open spec fn has_witness_of_length(d: NDomains, item: Item, n: nat) -> bool {
    exists|theta: Subst, w: Seq<EventView>| w.len() == n && #[trigger] witness(d, item, theta, w)
}

// ----- atoms, assignments, successor cases (`inclusion.tex:164-216`) -----

/// An atom assignment; its domain is the atom set.
pub type Assignment = Map<model::Primitive, bool>;

/// `(θ, e)` realizes `α`.
pub open spec fn realizes(theta: Subst, e: EventView, alpha: Assignment) -> bool {
    forall|p: model::Primitive| #[trigger] alpha.dom().contains(p) ==> alpha[p] == model::primitive_holds(theta, p, e)
}

/// `Π_q`: `(x_c, v)` such that `π_c = x_c` and `π_c = v` are both atoms.
pub open spec fn atom_pairs(atoms: Set<model::Primitive>) -> Pairs {
    Set::new(|p: (Component, nat)| atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
        && atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Constant(p.1)))).unwrap_or(Set::empty())
}

/// `next` is the successor of `q` for `α`: `L_θ(next) = e⁻¹ L_θ(q)` whenever `(θ, e)` realizes `α`
/// (the implementation's `successor_entries_wf`, `progress.rs:1790`).
pub open spec fn successor_ok(q: Regex<model::Test>, alpha: Assignment, next: Regex<model::Test>) -> bool {
    forall|theta: Subst, e: EventView, w: Seq<EventView>| language::event_wf(theta) && #[trigger] realizes(theta, e, alpha)
        ==> (#[trigger] n_lang(theta, next, w) == n_lang(theta, q, seq![e] + w))
}

/// One successor case `(Γ', α, q')`.
pub struct Case { pub constraint: Constraint, pub alpha: Assignment, pub next: Regex<model::Test> }

pub open spec fn case_item(c: Case) -> Item { Item { constraint: c.constraint, state: c.next } }

/// Lemma 5.3's conclusion for a set of cases of `item` (`inclusion.tex:197-209`).
pub open spec fn steps_ok(d: NDomains, item: Item, cases: Set<Case>) -> bool {
    &&& forall|c: Case| #[trigger] cases.contains(c) ==> {
        &&& satisfiable(d, c.constraint) && entails(d, c.constraint, item.constraint)
        &&& successor_ok(item.state, c.alpha, c.next)
        // uniform realizability
        &&& forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, c.constraint)
            ==> exists|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha)
    }
    // every (θ, e) belongs to exactly one case
    &&& forall|theta: Subst, e: EventView| n_theta_ok(d, theta) && #[trigger] n_event_in(d, e) && #[trigger] sat_by(theta, item.constraint)
        ==> exists|c: Case| #[trigger] cases.contains(c) && sat_by(theta, c.constraint) && realizes(theta, e, c.alpha)
    &&& forall|theta: Subst, e: EventView, c1: Case, c2: Case| n_theta_ok(d, theta)
        && cases.contains(c1) && cases.contains(c2) && #[trigger] sat_by(theta, c1.constraint) && #[trigger] sat_by(theta, c2.constraint)
        && #[trigger] realizes(theta, e, c1.alpha) && realizes(theta, e, c2.alpha) ==> c1 == c2
}

/// The paper's `Steps(Γ, q)` for an atom set and the successors `next(α)`.
pub open spec fn paper_steps(d: NDomains, item: Item, atoms: Set<model::Primitive>,
    cases_split: Set<Constraint>, next: spec_fn(Assignment) -> Regex<model::Test>) -> ISet<Case> {
    ISet::new(|c: Case| cases_split.contains(c.constraint) && c.alpha.dom() == atoms && c.next == next(c.alpha)
        && exists|theta: Subst, e: EventView| n_theta_ok(d, theta) && n_event_in(d, e)
            && #[trigger] sat_by(theta, c.constraint) && #[trigger] realizes(theta, e, c.alpha))
}

pub open spec fn n_unrestricted(d: NDomains) -> bool {
    d.principal is None && d.action is None && d.resource is None
}

/// The atoms determine `q`'s derivative: realizing the same assignment gives the same residual
/// language (true for the atoms of `δ(q)`'s conditions by Theorem 4.1).
pub open spec fn atoms_complete(q: Regex<model::Test>, atoms: Set<model::Primitive>) -> bool {
    forall|theta: Subst, e1: EventView, e2: EventView, w: Seq<EventView>|
        (forall|p: model::Primitive| atoms.contains(p) ==> #[trigger] model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2))
            ==> (#[trigger] n_lang(theta, q, seq![e1] + w) == #[trigger] n_lang(theta, q, seq![e2] + w))
}

/// Component-locality of atoms (`bg.tex` §3): a variable atom compares a component only with the
/// candidate's value of the same component. The analyzer enforces it (`search.rs` `atom`).
pub open spec fn atoms_local(atoms: Set<model::Primitive>) -> bool {
    forall|c: Component, c2: Component| #[trigger] atoms.contains(model::Primitive::Eq(c, model::GTerm::Variable(c2))) ==> c2 == c
}

/// Lemma 5.3 (exact successor cases), infinite domains: with `Γ` satisfiable, complete atoms,
/// correct successors for every realizable assignment, and any `Split(Γ; Π_q)` family, the paper's
/// `Steps` is finite and satisfies `steps_ok`.
pub open spec fn stmt_successor_cases() -> bool {
    forall|d: NDomains, item: Item, atoms: Set<model::Primitive>, cases_split: Set<Constraint>,
        next: spec_fn(Assignment) -> Regex<model::Test>|
        n_unrestricted(d) && satisfiable(d, item.constraint) && atoms_local(atoms) && atoms_complete(item.state, atoms)
            && split_ok(d, item.constraint, atom_pairs(atoms), cases_split)
            && (forall|alpha: Assignment| alpha.dom() == atoms ==> #[trigger] successor_ok(item.state, alpha, next(alpha)))
            ==> #[trigger] paper_steps(d, item, atoms, cases_split, next).finite()
                && steps_ok(d, item, Set::new_from_iset(paper_steps(d, item, atoms, cases_split, next)).unwrap_or(Set::empty()))
}

/// Extension beyond the paper (declared finite domains): `Π` additionally pairs each register
/// compared at a finite component with every declared value, as `constraint.rs:236-281` does.
pub open spec fn domain_pairs(d: NDomains, atoms: Set<model::Primitive>) -> Pairs {
    Set::new(|p: (Component, nat)| atom_pairs(atoms).contains(p)
        || (atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
            && match n_domain(d, p.0) { Some(values) => values.contains(p.1), None => false })).unwrap_or(Set::empty())
}

pub open spec fn stmt_successor_cases_finite_domains() -> bool {
    forall|d: NDomains, item: Item, atoms: Set<model::Primitive>, cases_split: Set<Constraint>,
        next: spec_fn(Assignment) -> Regex<model::Test>|
        satisfiable(d, item.constraint) && atoms_local(atoms) && atoms_complete(item.state, atoms)
            && split_ok(d, item.constraint, domain_pairs(d, atoms), cases_split)
            && (forall|alpha: Assignment| alpha.dom() == atoms ==> #[trigger] successor_ok(item.state, alpha, next(alpha)))
            ==> #[trigger] paper_steps(d, item, atoms, cases_split, next).finite()
                && steps_ok(d, item, Set::new_from_iset(paper_steps(d, item, atoms, cases_split, next)).unwrap_or(Set::empty()))
}

// ----- the breadth-first search (Algorithm 5.4, `inclusion.tex:221-255`) -----

pub struct Node { pub item: Item, pub parent: Option<(nat, Assignment)>, pub depth: nat }

/// The search state the implementation keeps: inserted nodes in insertion order (never removed)
/// and the number of expanded nodes.
pub struct Trace { pub nodes: Seq<Node>, pub expanded: nat }

pub enum Outcome { Holds, Refuted(Constraint, Seq<Assignment>), Exhausted }

pub open spec fn nullable_state(q: Regex<model::Test>) -> bool { language::nullable(q) }

/// A successor item may be dropped at insertion: its state is `∅`, or it has no witnesses
/// (dead), or an already inserted node of depth at most `depth` has all its witnesses
/// (an identical item or a dominating one).
pub open spec fn may_discard(d: NDomains, nodes: Seq<Node>, j: Item, depth: nat) -> bool {
    ||| j.state == Regex::<model::Test>::Empty
    ||| no_witness(d, j)
    ||| exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth && #[trigger] witnesses_within(d, j, nodes[k].item)
}

/// Assignments along the parent chain of node `n`, oldest first (`inclusion.tex:224-229`).
pub open spec fn chain(nodes: Seq<Node>, n: int, fuel: nat) -> Seq<Assignment>
    decreases fuel,
{
    if fuel == 0 || n < 0 || n >= nodes.len() { Seq::empty() } else {
        match nodes[n].parent {
            None => Seq::empty(),
            Some((p, alpha)) => chain(nodes, p as int, (fuel - 1) as nat).push(alpha),
        }
    }
}

/// Node `j` is a successor case of an expanded earlier node, one level deeper.
pub open spec fn parent_ok(cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int) -> bool {
    match t.nodes[j].parent {
        None => false,
        Some((p, alpha)) => p < t.expanded && p < j && t.nodes[j].depth == t.nodes[p as int].depth + 1
            && exists|c: Case| #[trigger] cases_of(t.nodes[p as int].item).contains(c) && c.alpha == alpha
                && t.nodes[j].item == case_item(c),
    }
}

/// `t` is a trace of the search from `(Γ₀, q₀)` that enumerates successor cases with `cases_of`.
pub open spec fn trace_wf(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace) -> bool {
    let nodes = t.nodes;
    &&& t.expanded <= nodes.len()
    // the root is inserted unless it may be discarded
    &&& if nodes.len() == 0 { may_discard(d, nodes, Item { constraint: g0, state: q0 }, 0) }
        else { nodes[0] == (Node { item: Item { constraint: g0, state: q0 }, parent: None, depth: 0 }) }
    // every other node is a successor case of an expanded node, one level deeper
    &&& forall|j: int| 0 < j < nodes.len() ==> #[trigger] parent_ok(cases_of, t, j)
    &&& forall|i: int, j: int| 0 <= i < j < nodes.len() ==> #[trigger] nodes[i].depth <= #[trigger] nodes[j].depth
        && nodes[i].item != nodes[j].item
    // expanded nodes are not nullable, and every one of their cases was inserted or discarded
    &&& forall|p: int| 0 <= p < t.expanded ==> !nullable_state(#[trigger] nodes[p].item.state)
        && forall|c: Case| #[trigger] cases_of(nodes[p].item).contains(c) ==>
            (exists|j: int| 0 < j < nodes.len() && nodes[j].parent == Some((p as nat, c.alpha)) && nodes[j].item == case_item(c))
            || may_discard(d, nodes, case_item(c), nodes[p].depth + 1)
}

/// The outcome a trace returns: a counterexample from the first unexpanded node if nullable,
/// `Holds` if every node was expanded, and `Exhausted` from a limit at any point.
pub open spec fn trace_outcome(t: Trace, outcome: Outcome) -> bool {
    match outcome {
        Outcome::Holds => t.expanded == t.nodes.len(),
        Outcome::Refuted(g, letters) => t.expanded < t.nodes.len() && nullable_state(t.nodes[t.expanded as int].item.state)
            && g == t.nodes[t.expanded as int].item.constraint
            && letters == chain(t.nodes, t.expanded as int, t.nodes[t.expanded as int].depth),
        Outcome::Exhausted => true,
    }
}

/// `(θ, u)` follows the recorded assignments.
pub open spec fn follows(d: NDomains, letters: Seq<Assignment>, theta: Subst, u: Seq<EventView>) -> bool {
    u.len() == letters.len() && n_history_in(d, u)
        && forall|j: int| 0 <= j < u.len() ==> #[trigger] realizes(theta, u[j], letters[j])
}

/// What a returned outcome means for the query `r ⊑_{Γ₀} s` (`inclusion.tex:257-262`).
pub open spec fn outcome_ok(d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, outcome: Outcome) -> bool {
    match outcome {
        Outcome::Holds => included_under(d, g0, r, s),
        Outcome::Refuted(g, letters) =>
            // realizable, and every realization is a counterexample
            (exists|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g))
            && (forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
                ==> exists|u: Seq<EventView>| #[trigger] follows(d, letters, theta, u))
            && (forall|theta: Subst, u: Seq<EventView>| n_theta_ok(d, theta) && sat_by(theta, g) && #[trigger] follows(d, letters, theta, u)
                ==> inclusion_cex(d, g0, r, s, theta, u))
            // minimum length for this query
            && no_cex_shorter(d, g0, r, s, letters.len()),
        Outcome::Exhausted => true,
    }
}

/// `q₀ = N(r & ¬s)` has the language of `r & ¬s`.
pub open spec fn initial_ok(q0: Regex<model::Test>, r: Regex<model::Test>, s: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta)
        ==> (#[trigger] n_lang(theta, q0, w) == (n_lang(theta, r, w) && !n_lang(theta, s, w)))
}

/// Theorem 5.5, soundness, completeness and minimality: every trace that returns satisfies
/// `outcome_ok`, with or without pruning. Infinite domains.
pub open spec fn stmt_search_correct() -> bool {
    forall|d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, q0: Regex<model::Test>,
        cases_of: spec_fn(Item) -> Set<Case>, t: Trace, outcome: Outcome|
        n_unrestricted(d) && satisfiable(d, g0) && #[trigger] initial_ok(q0, r, s)
            && (forall|i: Item| #[trigger] steps_ok(d, i, cases_of(i)))
            && #[trigger] trace_wf(d, g0, q0, cases_of, t) && #[trigger] trace_outcome(t, outcome)
            ==> outcome_ok(d, g0, r, s, outcome)
}

/// The same for declared finite domains, with `cases_of` built from `domain_pairs`.
pub open spec fn stmt_search_correct_finite_domains() -> bool {
    forall|d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, q0: Regex<model::Test>,
        cases_of: spec_fn(Item) -> Set<Case>, t: Trace, outcome: Outcome|
        satisfiable(d, g0) && #[trigger] initial_ok(q0, r, s)
            && (forall|i: Item| #[trigger] steps_ok(d, i, cases_of(i)))
            && #[trigger] trace_wf(d, g0, q0, cases_of, t) && #[trigger] trace_outcome(t, outcome)
            ==> outcome_ok(d, g0, r, s, outcome)
}

/// Items reachable from `start` through successor cases, in `n` steps.
pub open spec fn reachable_item(cases_of: spec_fn(Item) -> Set<Case>, start: Item, n: nat, j: Item) -> bool
    decreases n,
{
    if n == 0 { j == start } else {
        exists|i: Item, c: Case| reachable_item(cases_of, start, (n - 1) as nat, i)
            && #[trigger] cases_of(i).contains(c) && case_item(c) == j
    }
}

/// Hypothesis of termination: finitely many items are reachable. It follows from finitely many
/// reachable states (`finiteness::stmt_items_from_states`): constraints are `Γ₀` plus literals
/// over the atoms of reachable states. For the paper's model normalizer the states are bounded by
/// Lemma 4.2; for the implementation (after the finiteness fix, `SPEC.md` §9.16) by the same
/// lemma instantiated with `verify::finite_impl::m_impl` (`finiteness::theorem_impl_finitely_many_items`,
/// with the implemented step abstracted by `finiteness::lemma_impl_successor_abstracts`).
pub open spec fn items_within(cases_of: spec_fn(Item) -> Set<Case>, start: Item, f: Set<Item>) -> bool {
    forall|n: nat, j: Item| #[trigger] reachable_item(cases_of, start, n, j) ==> f.contains(j)
}

pub open spec fn finitely_many_items(cases_of: spec_fn(Item) -> Set<Case>, start: Item) -> bool {
    exists|f: Set<Item>| #[trigger] items_within(cases_of, start, f)
}

/// Every trace from `(Γ₀, q₀)` has at most `bound` nodes.
pub open spec fn traces_bounded(g0: Constraint, q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>, bound: nat) -> bool {
    forall|d: NDomains, t: Trace| #[trigger] trace_wf(d, g0, q0, cases_of, t) ==> t.nodes.len() <= bound
}

/// Theorem 5.5, termination, *conditional* on finitely many reachable items: no trace has more
/// than `bound` nodes (nodes are distinct reachable items), so the search returns after at most
/// `bound` expansions.
pub open spec fn stmt_search_terminates() -> bool {
    forall|g0: Constraint, q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>|
        #[trigger] finitely_many_items(cases_of, Item { constraint: g0, state: q0 })
            ==> exists|bound: nat| #[trigger] traces_bounded(g0, q0, cases_of, bound)
}

} // verus!
