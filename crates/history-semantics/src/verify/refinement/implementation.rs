//! Layer 6: the implementation as the abstract objects of layers 2–4.
//!
//! Views of `history-analysis` internals (planned; that crate is not Verus-checked) and of the
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
pub struct ConstraintView { pub principal: RegisterView, pub action: RegisterView, pub resource: RegisterView }

pub open spec fn register_of(g: ConstraintView, c: Component) -> RegisterView {
    match c { Component::Principal => g.principal, Component::Action => g.action, Component::Resource => g.resource }
}

/// The literals a constraint view stands for.
pub open spec fn constraint_of(g: ConstraintView) -> Constraint {
    Set::new(|l: Literal| match register_of(g, l.component) {
        RegisterView::Equals(v) => l.equal && l.value == v,
        RegisterView::Differs(ds) => !l.equal && ds.contains(l.value),
    }).unwrap_or(Set::empty())
}

/// `Class`: a constant, or the candidate's own value (the register).
pub enum ClassView { Constant(nat), Register }

/// `Letter`: per component, a class (`None` = a value outside every class), and the class the
/// register takes under the letter's constraint.
pub struct LetterView {
    pub principal: Option<ClassView>, pub action: Option<ClassView>, pub resource: Option<ClassView>,
    pub reg_principal: ClassView, pub reg_action: ClassView, pub reg_resource: ClassView,
}

pub open spec fn letter_class(l: LetterView, c: Component) -> Option<ClassView> {
    match c { Component::Principal => l.principal, Component::Action => l.action, Component::Resource => l.resource }
}

pub open spec fn letter_register(l: LetterView, c: Component) -> ClassView {
    match c { Component::Principal => l.reg_principal, Component::Action => l.reg_action, Component::Resource => l.reg_resource }
}

/// `Letter::holds` (`constraint.rs`): an atom holds iff the component's class is the atom's class.
pub open spec fn letter_holds(l: LetterView, p: model::Primitive) -> bool {
    match p {
        model::Primitive::Eq(c, model::GTerm::Constant(v)) => letter_class(l, c) == Some(ClassView::Constant(v)),
        model::Primitive::Eq(c, model::GTerm::Variable(_)) => letter_class(l, c) == Some(letter_register(l, c)),
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
    EventView { principal: slot_value(slots[0], fresh), action: slot_value(slots[1], fresh), resource: slot_value(slots[2], fresh) }
}

// ----- the policy-level glue (`analyzer.rs:460-497`, `tables.rs`) -----

/// `covered_with` searches `ρ_R & ¬Σ ρ_R'` per case of `split(Γ_R; Π_P)`; the cases satisfy
/// `split_ok` and the searched expression has the language of `inclusion::firing_denials`.
pub open spec fn covered_with_ok(d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>,
    query: spec_fn(Constraint) -> (Regex<model::Test>, Regex<model::Test>)) -> bool {
    &&& split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
    &&& forall|g1: Constraint| #[trigger] cases.contains(g1) ==> query(g1).0 == denial(rule)
        && forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta)
            ==> (#[trigger] n_lang(theta, query(g1).1, w) == n_lang(theta, firing_denials(d, p, g1), w))
}

} // verus!
