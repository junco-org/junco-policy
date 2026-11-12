//! Layer 6: the implementation as the abstract objects of layers 2–4.
//!
//! Views of `history-analysis` internals (verified against them in `history-analysis/src/verify/`) and of the
//! verified runtime (`history-semantics`): interned constants and constraints, letters, items as
//! graph ids, and the reconstruction of counterexamples.
use super::analyzer::*;
use super::encoding::*;
use super::finiteness::*;
use super::inclusion::*;
use super::search::*;
use history_syntax::syntax::Component;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

/// `RegisterConstraint`: equal to one code, or different from a set of codes.
pub enum RegisterView { Equals(nat), Differs(Set<nat>) }

/// `Constraint`: one register constraint per component.
pub type ConstraintView = Seq<RegisterView>;

pub open spec fn register_of(g: ConstraintView, c: Component) -> RegisterView
    recommends c.0 < g.len(),
{
    g[c.0 as int]
}

/// The literals a constraint view stands for.
pub open spec fn constraint_of(g: ConstraintView) -> Constraint {
    Set::new(|l: Literal| l.component.0 < g.len() && match register_of(g, l.component) {
        RegisterView::Equals(v) => l.equal && l.value == v,
        RegisterView::Differs(ds) => !l.equal && ds.contains(l.value),
    }).unwrap_or(Set::empty())
}

/// `Class`: a constant, or the candidate's own value (the register).
pub enum ClassView { Constant(nat), Register }

/// `Letter`: per component, a class (`None` = a value outside every class), and the class the
/// register takes under the letter's constraint.
pub struct LetterView {
    pub classes: Seq<Option<ClassView>>,
    pub registers: Seq<ClassView>,
}

pub open spec fn letter_class(l: LetterView, c: Component) -> Option<ClassView>
    recommends c.0 < l.classes.len(),
{
    l.classes[c.0 as int]
}

pub open spec fn letter_register(l: LetterView, c: Component) -> ClassView
    recommends c.0 < l.registers.len(),
{
    l.registers[c.0 as int]
}

/// `Letter::holds` (`constraint.rs`): an atom holds iff the component's class is the atom's class.
pub open spec fn letter_holds(l: LetterView, p: model::Primitive) -> bool {
    match p {
        model::Primitive::Eq(c, model::GTerm::Constant(v)) => c.0 < l.classes.len()
            && letter_class(l, c) == Some(ClassView::Constant(v)),
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < l.classes.len()
            && v.0 < l.registers.len() && letter_class(l, c) == Some(letter_register(l, v)),
    }
}

/// The assignment of a letter on an atom set (`search.rs` `truth`).
pub open spec fn letter_assignment(l: LetterView, atoms: Set<model::Primitive>) -> Assignment {
    Map::new(atoms, |p: model::Primitive| letter_holds(l, p))
}

/// The implementation's successor cases of an item: `steps(Γ, atoms)` (`constraint.rs:332-345`)
/// with the successor ids returned by `CompiledPair::successor` for each letter. This is the
/// `cases_of` of `search::trace_wf` for the analyzer, read through `abs_state`.
pub open spec fn impl_cases(g: model::Graph, atoms: Set<model::Primitive>,
    steps: Set<(ConstraintView, LetterView, nat)>) -> Set<Case> {
    steps.map(|s: (ConstraintView, LetterView, nat)| Case {
        constraint: constraint_of(s.0), alpha: letter_assignment(s.1, atoms), next: abs_state(g, s.2) })
}

/// Obligations on one expansion (`search.rs:159-184`), for the item `(Γ, q)` in graph `g`:
/// the atoms are complete for `q` (`atoms_wf`, `progress.rs:1347`), the emitted cases satisfy
/// `steps_ok`, and every case only adds literals over the atoms' codes or declared values.
pub open spec fn expansion_ok(d: NDomains, g: model::Graph, gamma: ConstraintView, q: nat,
    atoms: Set<model::Primitive>, steps: Set<(ConstraintView, LetterView, nat)>) -> bool {
    let item = Item { constraint: constraint_of(gamma), state: abs_state(g, q) };
    &&& gamma.len() == d.len()
    &&& atoms_local(atoms) && atoms_bounded(atoms, d.len())
    &&& forall|s: (ConstraintView, LetterView, nat)| #[trigger] steps.contains(s)
        ==> s.0.len() == d.len() && s.1.classes.len() == d.len() && s.1.registers.len() == d.len()
    &&& atoms_complete(item.state, atoms)
    &&& steps_ok(d, item, impl_cases(g, atoms, steps))
}

// ----- counterexample reconstruction (`analyzer.rs:533-568`) -----

/// Slot of a reconstructed component: a code, or a fresh number.
pub enum SlotView { Code(nat), Fresh(nat) }

/// The numeric value of a slot under an injective choice of fresh codes outside the known codes.
pub open spec fn slot_value(s: SlotView, fresh: spec_fn(nat) -> nat) -> nat {
    match s { SlotView::Code(v) => v, SlotView::Fresh(n) => fresh(n) }
}

/// Reconstruction is sound: every numeric instantiation of the reconstructed slots (fresh numbers
/// to distinct codes outside the known codes, within `u64` for the candidate) satisfies the
/// refutation's constraint and follows its letters. With `search::outcome_ok` and
/// `encoding::stmt_front_end_denies`, this gives the typed `analyzer::every_instance`.
pub open spec fn reconstruction_ok(d: NDomains, gamma: Constraint, letters: Seq<Assignment>,
    candidate: Seq<SlotView>, history: Seq<Seq<SlotView>>, known: Set<nat>) -> bool {
    forall|fresh: spec_fn(nat) -> nat| #[trigger] fresh_codes_ok(fresh, known) ==> {
        let theta = slots_event(candidate, fresh);
        let u = history.map(|i: int, e: Seq<SlotView>| slots_event(e, fresh));
        n_theta_ok(d, theta) ==> sat_by(theta, gamma) && follows(d, letters, theta, u)
    }
}

pub open spec fn fresh_codes_ok(fresh: spec_fn(nat) -> nat, known: Set<nat>) -> bool {
    &&& forall|m: nat, n: nat| m != n ==> #[trigger] fresh(m) != #[trigger] fresh(n)
    &&& forall|n: nat| !known.contains(#[trigger] fresh(n))
}

pub open spec fn slots_event(slots: Seq<SlotView>, fresh: spec_fn(nat) -> nat) -> EventView {
    slots.map(|i: int, s: SlotView| slot_value(s, fresh))
}

// ----- the policy-level glue (`analyzer.rs:460-497`, `tables.rs`) -----

/// `covered_with` searches `ρ_R & ¬Σ ρ_R'` per case of `split(Γ_R; Π_P)`; the cases satisfy
/// `split_ok` and the searched expression has the language of `inclusion::firing_denials`.
pub open spec fn covered_with_ok(d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>,
    query: spec_fn(Constraint) -> (Regex<model::Test>, Regex<model::Test>)) -> bool {
    &&& rule.head.len() == d.len()
    &&& forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len()
    &&& split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
    &&& forall|g1: Constraint| #[trigger] cases.contains(g1) ==> query(g1).0 == denial(rule)
        && forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> (#[trigger] n_lang(theta, query(g1).1, w) == n_lang(theta, firing_denials(d, p, g1), w))
}

/// The analyzer's retained case function has a finite trace bound once each real successor
/// abstracts into the implementation model and refinements use the finite atom vocabulary.
pub proof fn theorem_impl_search_bounded(d: NDomains,
    cases_of: spec_fn(Item) -> Set<Case>,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
    g0: Constraint, q0: Regex<model::Test>)
    requires crate::verify::finite_impl::regex_nf(q0),
        cases_follow(crate::verify::finite_impl::m_impl(), cases_of),
        cases_from_atoms(d, cases_of, atoms_of),
    ensures finitely_many_items(cases_of, Item { constraint: g0, state: q0 }),
        exists|bound: nat| #[trigger] traces_bounded(g0, q0, cases_of, bound),
{
    theorem_impl_finitely_many_items(d, cases_of, atoms_of,
        Item { constraint: g0, state: q0 });
    theorem_search_terminates();
}

} // verus!
