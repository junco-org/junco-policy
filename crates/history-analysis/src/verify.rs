//! Ghost views and contracts linking the executable analyzer to the frozen refinement layers.

pub(crate) mod constraint_unique;
pub(crate) mod policy_bridge;
pub(crate) mod policy_case_profile;
pub(crate) mod policy_firing;
pub(crate) mod policy_minimality;
pub(crate) mod policy_operands;
pub(crate) mod policy_queries;
pub(crate) mod policy_removal;
pub(crate) mod policy_source;
pub(crate) mod prune_exec;
pub(crate) mod reconstruction;
pub(crate) mod search_exec;
pub(crate) mod simulation_exec;
pub(crate) mod typed_numeric;
pub(crate) mod verdict;

use crate::analyzer::Constants;
use crate::constraint::equality::{constraint_key, register_key};
use crate::constraint::{
    Atom, Class, Constraint, ConstraintTable, Letter, Operand, Operands, RegisterConstraint,
    Universe, Universes,
};
use crate::verify::constraint_unique::{product_size, row_rank, row_valid};
use alloc::vec::Vec;
use history_semantics::verify::refinement::*;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::arity;
use history_syntax::syntax::Component;
use junco_core::kernel::verify as model;
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::history_specs::{self as language, EventView, Subst};
use vstd::prelude::*;

verus! {
pub(crate) open spec fn constant_book<E: Event>(c: Constants<E>)
    -> junco_core::verify::encoding::Codebook<E::Component> {
    Seq::new(arity::<E>(), |i: int| frontend::field_entries::<E>(c.values@, Component(i as u8)))
}
pub(crate) open spec fn component_at(index: usize) -> Component { Component(index as u8) }

pub(crate) open spec fn component_index(component: Component) -> usize { component.0 as usize }

pub(crate) open spec fn codes(values: Seq<u32>) -> Set<nat> {
    values.to_set().map(|value: u32| value as nat)
}

pub(crate) open spec fn canonical(values: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] < values[j]
}

impl View for Atom {
    type V = model::Primitive;
    open(crate) spec fn view(&self) -> model::Primitive {
        let c = component_at(self.component);
        model::Primitive::Eq(c, match self.operand {
            Operand::Register => model::GTerm::Variable(c),
            Operand::Constant(v) => model::GTerm::Constant(v as nat),
        })
    }
}

impl View for RegisterConstraint {
    type V = implementation::RegisterView;
    open(crate) spec fn view(&self) -> implementation::RegisterView {
        match self { RegisterConstraint::Equals(v) => implementation::RegisterView::Equals(*v as nat),
            RegisterConstraint::Differs(vs) => implementation::RegisterView::Differs(codes(vs.view())) }
    }
}

impl View for Constraint {
    type V = implementation::ConstraintView;
    open(crate) spec fn view(&self) -> implementation::ConstraintView {
        self.0@.map_values(|r: RegisterConstraint| r@)
    }
}

impl View for Class {
    type V = implementation::ClassView;
    open(crate) spec fn view(&self) -> implementation::ClassView {
        match self { Class::Register => implementation::ClassView::Register,
            Class::Constant(v) => implementation::ClassView::Constant(*v as nat) }
    }
}

pub(crate) open spec fn class_option(value: Option<Class>) -> Option<implementation::ClassView> {
    match value { None => None, Some(c) => Some(c@) }
}

impl View for Letter {
    type V = implementation::LetterView;
    open(crate) spec fn view(&self) -> implementation::LetterView {
        implementation::LetterView {
            classes: self.classes@.map_values(|c: Option<Class>| class_option(c)),
            registers: self.registers@.map_values(|c: Class| c@),
        }
    }
}

pub(crate) open spec fn domain_view(universe: Universe) -> Option<Set<nat>> {
    match universe { None => None, Some(values) => Some(codes((*values)@)) }
}

pub(crate) open spec fn ndomains(universes: Universes) -> encoding::NDomains {
    universes@.map_values(|u: Universe| domain_view(u))
}

pub(crate) open spec fn atom_set(atoms: Seq<Atom>) -> Set<model::Primitive> {
    atoms.to_set().map(|a: Atom| a@)
}

pub(crate) open spec fn atoms_wf(atoms: Seq<Atom>, arity: nat) -> bool {
    1 <= arity <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < atoms.len() ==> atoms[i].component < arity
}

pub(crate) open spec fn register_wf(register: RegisterConstraint) -> bool {
    match register { RegisterConstraint::Equals(_) => true,
        RegisterConstraint::Differs(vs) => canonical(vs.view()) }
}

pub(crate) open spec fn constraint_wf(constraint: Constraint) -> bool {
    1 <= constraint.0@.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < constraint.0@.len() ==> register_wf(constraint.0[i])
}

pub(crate) open spec fn letter_wf(letter: Letter) -> bool {
    1 <= letter.classes@.len() <= history_syntax::MAX_ARITY
        && letter.registers@.len() == letter.classes@.len()
}

pub(crate) open spec fn shape_wf(g: Constraint, operands: Operands, universes: Universes) -> bool {
    constraint_wf(g) && operands_wf(operands)
        && g@.len() == operands.register@.len() && g@.len() == universes@.len()
}

pub(crate) open spec fn register_sat(register: implementation::RegisterView, value: nat) -> bool {
    match register { implementation::RegisterView::Equals(v) => value == v,
        implementation::RegisterView::Differs(vs) => !vs.contains(value) }
}

pub(crate) open spec fn register_entails(a: implementation::RegisterView,
    b: implementation::RegisterView) -> bool {
    match (a, b) {
        (implementation::RegisterView::Equals(v), implementation::RegisterView::Equals(w)) => v == w,
        (implementation::RegisterView::Differs(_), implementation::RegisterView::Equals(_)) => false,
        (implementation::RegisterView::Equals(v), implementation::RegisterView::Differs(ws)) => !ws.contains(v),
        (implementation::RegisterView::Differs(vs), implementation::RegisterView::Differs(ws)) => ws.subset_of(vs),
    }
}
pub(crate) open spec fn option_code(value: Option<u32>) -> Option<nat> {
    match value { None => None, Some(v) => Some(v as nat) }
}


pub(crate) open spec fn head_view(constants: Seq<Option<u32>>) -> encoding::NHead {
    constants.map_values(|v: Option<u32>| option_code(v))
}

pub(crate) struct Scope {
    pub register: bool,
    pub constants: Seq<u32>,
}

impl View for Operands {
    type V = Seq<Scope>;
    open(crate) spec fn view(&self) -> Seq<Scope> {
        Seq::new(self.register@.len(), |i: int| Scope { register: self.register[i],
            constants: self.constants[i].view() })
    }
}

pub(crate) open spec fn operands_wf(operands: Operands) -> bool {
    1 <= operands.register@.len() <= history_syntax::MAX_ARITY
        && operands.register@.len() == operands.constants@.len()
        && forall|i: int| 0 <= i < operands.constants@.len() ==> canonical(operands.constants[i].view())
}

pub(crate) open spec fn operands_of(operands: Operands, atoms: Seq<Atom>) -> bool {
    operands_wf(operands) && atoms_wf(atoms, operands.register@.len()) && operands_members(operands, atoms)
}

pub(crate) open spec fn operands_members(operands: Operands, atoms: Seq<Atom>) -> bool {
    &&& operands.constants@.len() == operands.register@.len()
    &&& forall|i: int| #![trigger operands.register[i]] 0 <= i < operands.register@.len()
        ==> operands.register[i] == (exists|j: int| 0 <= j < atoms.len()
            && atoms[j].component == i && atoms[j].operand == Operand::Register)
    &&& forall|i: int, v: u32| #![trigger operands.constants[i].view().contains(v)]
        0 <= i < operands.register@.len() ==> operands.constants[i].view().contains(v)
            == (exists|j: int| 0 <= j < atoms.len() && atoms[j].component == i
                && atoms[j].operand == Operand::Constant(v))
}

impl View for ConstraintTable {
    type V = Seq<implementation::ConstraintView>;
    open(crate) spec fn view(&self) -> Seq<implementation::ConstraintView> {
        self.constraints@.map(|i: int, c: Constraint| c@)
    }
}
}

verus! {
pub(crate) proof fn lemma_codes(values: Seq<u32>)
    ensures forall|v: nat| #[trigger] codes(values).contains(v)
        == (exists|i: int| 0 <= i < values.len() && values[i] as nat == v),
{
    assert forall|v: nat| #[trigger] codes(values).contains(v) implies
        exists|i: int| 0 <= i < values.len() && values[i] as nat == v by {
        let x = choose|x: u32| values.to_set().contains(x) && x as nat == v;
        let i = choose|i: int| 0 <= i < values.len() && values[i] == x;
        assert(values[i] as nat == v);
    }
    assert forall|v: nat| (exists|i: int| 0 <= i < values.len() && values[i] as nat == v)
        implies #[trigger] codes(values).contains(v) by {
        let i = choose|i: int| 0 <= i < values.len() && values[i] as nat == v;
        assert(values.to_set().contains(values[i]));
    }
}
pub(crate) proof fn lemma_constraint_view(g: implementation::ConstraintView)
    ensures forall|l: inclusion::Literal| #[trigger] implementation::constraint_of(g).contains(l)
        == (l.component.0 < g.len() && match implementation::register_of(g, l.component) {
            implementation::RegisterView::Equals(v) => l.equal && l.value == v,
            implementation::RegisterView::Differs(vs) => !l.equal && vs.contains(l.value),
        }),
{
    let bound = constraint_literal_bound(g);
    lemma_constraint_literal_bound(g);
    let pred = |l: inclusion::Literal| l.component.0 < g.len() && match implementation::register_of(g, l.component) {
        implementation::RegisterView::Equals(v) => l.equal && l.value == v,
        implementation::RegisterView::Differs(vs) => !l.equal && vs.contains(l.value),
    };
    inclusion::lemma_set_new_bounded(pred, bound.to_iset());
}

pub(crate) open spec fn constraint_literal_bound(g: implementation::ConstraintView) -> Set<inclusion::Literal>
    decreases g.len(),
{
    if g.len() == 0 { Set::empty() } else {
        constraint_literal_bound(g.drop_last()).union(register_literals(Component((g.len() - 1) as u8), g.last()))
    }
}

pub(crate) proof fn lemma_constraint_literal_bound(g: implementation::ConstraintView)
    ensures forall|l: inclusion::Literal| l.component.0 < g.len()
        && register_literals(l.component, g[l.component.0 as int]).contains(l)
        ==> constraint_literal_bound(g).contains(l),
    decreases g.len(),
{
    if g.len() > 0 {
        lemma_constraint_literal_bound(g.drop_last());
        assert forall|l: inclusion::Literal| l.component.0 < g.len()
            && register_literals(l.component, g[l.component.0 as int]).contains(l)
            implies constraint_literal_bound(g).contains(l) by {
let prior = g.drop_last();
let c = l.component;
if c.0 < g.len() - 1 {
    assert(c.0 < prior.len());
    assert(prior[c.0 as int] == g[c.0 as int]);
    assert(register_literals(c, prior[c.0 as int]).contains(l));
    assert(constraint_literal_bound(prior).contains(l));
} else {
    assert(c.0 as int == g.len() - 1);
    assert(c == Component((g.len() - 1) as u8));
    assert(g.last() == g[c.0 as int]);
    assert(register_literals(Component((g.len() - 1) as u8), g.last()).contains(l));
}
assert(constraint_literal_bound(g) == constraint_literal_bound(prior)
    .union(register_literals(Component((g.len() - 1) as u8), g.last())));
        }
    }
}

pub(crate) open spec fn register_literals(c: Component, r: implementation::RegisterView)
    -> Set<inclusion::Literal> {
    match r {
        implementation::RegisterView::Equals(v) => Set::empty().insert(inclusion::eq_literal(c, v)),
        implementation::RegisterView::Differs(vs) =>
            vs.map(|v: nat| inclusion::ne_literal(c, v)),
    }
}

pub(crate) proof fn lemma_constraint_sat(g: implementation::ConstraintView, theta: Subst)
    requires g.len() == theta.len(), g.len() <= history_syntax::MAX_ARITY,
    ensures inclusion::sat_by(theta, implementation::constraint_of(g))
        == (forall|i: int| 0 <= i < g.len() ==> register_sat(g[i], theta[i])),
{
    lemma_constraint_view(g);
    if inclusion::sat_by(theta, implementation::constraint_of(g)) {
        assert forall|i: int| 0 <= i < g.len() implies register_sat(g[i], theta[i]) by {
            let c = Component(i as u8);
            match g[i] {
                implementation::RegisterView::Equals(v) => {
                    assert(implementation::constraint_of(g).contains(inclusion::eq_literal(c, v)));
                },
                implementation::RegisterView::Differs(vs) => {
                    if vs.contains(theta[i]) {
                        assert(implementation::constraint_of(g).contains(inclusion::ne_literal(c, theta[i])));
                    }
                },
            }
        }
    } else if forall|i: int| 0 <= i < g.len() ==> register_sat(g[i], theta[i]) {
        assert forall|l: inclusion::Literal| #[trigger] implementation::constraint_of(g).contains(l)
            implies inclusion::literal_holds(theta, l) by {
            assert(register_sat(g[l.component.0 as int], theta[l.component.0 as int]));
        }
    }
}
pub(crate) open spec fn register_possible(r: RegisterConstraint, u: Universe) -> bool {
    match domain_view(u) { None => true,
        Some(vs) => exists|v: nat| vs.contains(v) && register_sat(r@, v) }
}

pub(crate) proof fn lemma_register_witness(r: RegisterConstraint, u: Universe) -> (v: nat)
    requires register_possible(r, u),
    ensures v <= u64::MAX, register_sat(r@, v),
        domain_view(u) matches Some(vs) ==> vs.contains(v),
{
    match u {
        Some(values) => {
            lemma_codes((*values)@);
            let v = choose|v: nat| codes((*values)@).contains(v) && register_sat(r@, v);
            let i = choose|i: int| 0 <= i < (*values)@.len() && (*values)@[i] as nat == v;
            v
        },
        None => match r {
            RegisterConstraint::Equals(v) => v as nat,
            RegisterConstraint::Differs(vs) => {
                lemma_codes(vs.view());
                assert(!codes(vs.view()).contains(0x100000000nat));
                0x100000000nat
            },
        },
    }
}

pub(crate) proof fn lemma_constraint_possible(g: Constraint, universes: Universes)
    requires constraint_wf(g), g@.len() == universes@.len(),
    ensures inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@))
        == (forall|i: int| 0 <= i < g@.len() ==> register_possible(g.0[i], universes[i])),
{
    let d = ndomains(universes);
    if forall|i: int| 0 <= i < g@.len() ==> register_possible(g.0[i], universes[i]) {
assert forall|i: int| #![trigger g.0[i]] 0 <= i < g@.len() implies exists|v: nat|
            register_allowed(domain_view(universes[i]), v) && register_sat(g.0[i]@, v) by {
let v = lemma_register_witness(g.0[i], universes[i]);
assert(v <= u64::MAX);
assert(register_sat(g.0[i]@, v));
match domain_view(universes[i]) {
    None => {}, Some(vs) => { assert(vs.contains(v)); },
}
assert(register_allowed(domain_view(universes[i]), v));
        }
        let theta = Seq::new(g@.len(), |i: int| choose|v: nat|
            register_allowed(domain_view(universes[i]), v) && register_sat(g.0[i]@, v));
        lemma_constraint_sat(g@, theta);
        assert(encoding::n_theta_ok(d, theta));
    } else if inclusion::satisfiable(d, implementation::constraint_of(g@)) {
        let theta = choose|theta: Subst| encoding::n_theta_ok(d, theta)
            && inclusion::sat_by(theta, implementation::constraint_of(g@));
lemma_constraint_sat(g@, theta);
lemma_theta_allowed(universes, theta);
assert forall|i: int| 0 <= i < g@.len() implies register_possible(g.0[i], universes[i]) by {
    assert(g@[i] == g.0@[i]@);
    assert(g.0[i] == g.0@[i]);
    assert(register_sat(g@[i], theta[i]));
    assert(register_sat(g.0[i]@, theta[i]));
    assert(register_allowed(domain_view(universes[i]), theta[i]));
    match domain_view(universes[i]) {
        None => {},
        Some(vs) => {
            assert(vs.contains(theta[i]));
            assert(exists|v: nat| vs.contains(v) && register_sat(g.0[i]@, v));
        },
    }
        }
    }
}
pub(crate) proof fn lemma_head_view(g: Constraint, constants: Seq<Option<u32>>)
    requires g@.len() == constants.len(), 1 <= constants.len() <= history_syntax::MAX_ARITY,
        forall|i: int| 0 <= i < constants.len() ==> g.0[i]@ == match constants[i] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        },
    ensures implementation::constraint_of(g@) == inclusion::head_constraint(head_view(constants)),
{
    lemma_constraint_view(g@);
    inclusion::lemma_head_constraint(head_view(constants));
    assert forall|l: inclusion::Literal| implementation::constraint_of(g@).contains(l)
        == inclusion::head_constraint(head_view(constants)).contains(l) by {
        if l.component.0 < constants.len() {
            assert(implementation::register_of(g@, l.component) == g.0[l.component.0 as int]@);
        }
    }
    assert(implementation::constraint_of(g@) =~= inclusion::head_constraint(head_view(constants)));
}

pub(crate) proof fn lemma_constraint_entails(a: implementation::ConstraintView, b: implementation::ConstraintView)
    requires a.len() == b.len(), forall|i: int| 0 <= i < a.len() ==> register_entails(a[i], b[i]),
    ensures forall|d: encoding::NDomains|
        inclusion::entails(d, implementation::constraint_of(a), implementation::constraint_of(b)),
{
    lemma_constraint_view(a); lemma_constraint_view(b);
    assert forall|d: encoding::NDomains, theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, implementation::constraint_of(a))
        implies inclusion::sat_by(theta, implementation::constraint_of(b)) by {
        assert forall|l: inclusion::Literal| implementation::constraint_of(b).contains(l)
            implies inclusion::literal_holds(theta, l) by {
            let i = l.component.0 as int;
            match a[i] {
                implementation::RegisterView::Equals(v) => {
                    assert(implementation::constraint_of(a).contains(inclusion::eq_literal(l.component, v)));
                },
                implementation::RegisterView::Differs(vs) => {
                    assert(implementation::constraint_of(a).contains(l));
                },
            }
        }
    }
}
}

verus! {
pub(crate) proof fn lemma_register_entails_point(a: implementation::RegisterView,
    values: Set<nat>, value: nat)
    requires values.contains(value), register_entails(a, implementation::RegisterView::Differs(values)),
    ensures !register_sat(a, value),
{
    reveal(register_entails);
    reveal(register_sat);
    match a {
        implementation::RegisterView::Equals(v) => {
            assert(forall|w: nat| values.contains(w) ==> w != v);
        },
        implementation::RegisterView::Differs(vs) => {
            assert(forall|w: nat| values.contains(w) ==> vs.contains(w));
        },
    }
}
}

verus! {
pub(crate) proof fn lemma_operands_push(before: Operands, after: Operands,
    atoms: Seq<Atom>, atom: Atom)
    requires after.register@.len() == before.register@.len(),
        after.constants@.len() == before.constants@.len(), atom.component < before.register@.len(), operands_members(before, atoms),
        forall|i: int| #![trigger after.register[i]] 0 <= i < before.register@.len()
            ==> after.register[i] == (before.register[i]
                || i == atom.component && atom.operand == Operand::Register),
        forall|i: int| #![trigger after.constants[i].view()] 0 <= i < before.register@.len()
            ==> after.constants[i].view() == match atom.operand {
                Operand::Constant(v) => if i == atom.component { before.constants[i].view().push(v) }
                    else { before.constants[i].view() },
                Operand::Register => before.constants[i].view(),
            },
    ensures operands_members(after, atoms.push(atom)),
{
    assert forall|i: int| 0 <= i < before.register@.len() implies after.register[i]
        == (exists|j: int| 0 <= j < atoms.push(atom).len()
            && atoms.push(atom)[j].component == i
            && atoms.push(atom)[j].operand == Operand::Register) by {
        lemma_exists_push(atoms, atom, |a: Atom| a.component == i && a.operand == Operand::Register);
    }
    assert forall|i: int, v: u32| 0 <= i < before.register@.len() implies after.constants[i].view().contains(v)
        == (exists|j: int| 0 <= j < atoms.push(atom).len()
            && atoms.push(atom)[j].component == i
            && atoms.push(atom)[j].operand == Operand::Constant(v)) by {
        lemma_exists_push(atoms, atom, |a: Atom| a.component == i && a.operand == Operand::Constant(v));
        assert(before.constants[i].view().contains(v) == (exists|j: int|
            0 <= j < atoms.len() && atoms[j].component == i && atoms[j].operand == Operand::Constant(v)));
        match atom.operand {
            Operand::Register => {},
            Operand::Constant(w) => {
                if i == atom.component {
                    vstd::seq_lib::lemma_seq_contains_after_push(before.constants[i].view(), w, v);
                }
            },
        }
    }
}

pub(crate) proof fn lemma_operands_preserved(before: Operands, after: Operands, atoms: Seq<Atom>)
    requires after.constants@.len() == before.constants@.len(), operands_members(before, atoms), after.register == before.register,
        forall|i: int| 0 <= i < before.register@.len() ==> after.constants[i].view().to_set()
            == before.constants[i].view().to_set(),
    ensures operands_members(after, atoms),
{
    assert forall|i: int, v: u32| 0 <= i < before.register@.len() implies
        after.constants[i].view().contains(v) == before.constants[i].view().contains(v) by {
        assert(after.constants[i].view().to_set().contains(v)
            == before.constants[i].view().to_set().contains(v));
    }
}
}

verus! {
pub(crate) proof fn lemma_exists_push<T>(values: Seq<T>, value: T, p: spec_fn(T) -> bool)
    ensures (exists|i: int| 0 <= i < values.push(value).len() && p(values.push(value)[i]))
        == (p(value) || exists|i: int| 0 <= i < values.len() && p(values[i])),
{
    if exists|i: int| 0 <= i < values.push(value).len() && p(values.push(value)[i]) {
        let i = choose|i: int| 0 <= i < values.push(value).len() && p(values.push(value)[i]);
        if i < values.len() { assert(p(values[i])); } else { assert(p(value)); }
    } else if p(value) {
        assert(p(values.push(value)[values.len() as int]));
    } else if exists|i: int| 0 <= i < values.len() && p(values[i]) {
        let i = choose|i: int| 0 <= i < values.len() && p(values[i]);
        assert(p(values.push(value)[i]));
    }
}
}

verus! {



pub(crate) open spec fn table_wf(table: ConstraintTable) -> bool {
    let reps = crate::native::representatives(table.ids);
    &&& reps.len() == table.constraints@.len()
    &&& forall|i: int| #![trigger reps[i]] 0 <= i < reps.len() ==> reps[i].1 == i
        && constraint_wf(reps[i].0)
        && constraint_key(reps[i].0) == constraint_key(table.constraints@[i])
    &&& forall|i: int| #![trigger table.constraints@[i]] 0 <= i < table.constraints@.len()
        ==> constraint_wf(table.constraints@[i])
    &&& forall|i: int, j: int| 0 <= i < j < reps.len()
        ==> constraint_key(reps[i].0) != constraint_key(reps[j].0)
}
}

verus! {
pub(crate) open spec fn register_options(current: implementation::RegisterView, register: bool,
    constants: Set<nat>, universe: Option<Set<nat>>) -> Set<implementation::RegisterView> {
    match current {
        implementation::RegisterView::Equals(_) => Set::empty().insert(current),
        implementation::RegisterView::Differs(differs) => if !register { Set::empty().insert(current) }
            else { match universe {
                Some(values) => values.difference(differs).map(|v: nat| implementation::RegisterView::Equals(v)),
                None => {
                    let undecided = constants.difference(differs);
                    if undecided.len() == 0 { Set::empty().insert(current) }
                    else { undecided.map(|v: nat| implementation::RegisterView::Equals(v))
                        .insert(implementation::RegisterView::Differs(differs.union(undecided))) }
                },
            } },
    }
}

pub(crate) open spec fn split_views(g: Constraint, operands: Operands, universes: Universes)
    -> Set<implementation::ConstraintView> { register_product(split_axes(g, operands, universes)) }

pub(crate) open spec fn split_axes(g: Constraint, operands: Operands, universes: Universes)
    -> Seq<Set<implementation::RegisterView>> {
    Seq::new(g@.len(), |i: int| register_options(g.0[i]@, operands.register[i],
        codes(operands.constants[i].view()), domain_view(universes[i])))
}

pub(crate) open spec fn constraint_views(values: Seq<Constraint>) -> Set<implementation::ConstraintView> {
    values.to_set().map(|g: Constraint| g@)
}

pub(crate) open spec fn register_views(values: Seq<RegisterConstraint>) -> Set<implementation::RegisterView> {
    values.to_set().map(|g: RegisterConstraint| g@)
}
}

verus! {
pub(crate) proof fn lemma_codes_push(values: Seq<u32>, value: u32)
    ensures codes(values.push(value)) == codes(values).insert(value as nat),
{
    values.lemma_push_to_set_commute(value);
    assert(values.push(value).to_set() =~= values.to_set().insert(value));
    values.to_set().lemma_set_map_insert_commute(value, |v: u32| v as nat);
}

pub(crate) proof fn lemma_register_views_push(values: Seq<RegisterConstraint>, value: RegisterConstraint)
    ensures register_views(values.push(value)) == register_views(values).insert(value@),
{
    values.lemma_push_to_set_commute(value);
    assert(values.push(value).to_set() =~= values.to_set().insert(value));
    values.to_set().lemma_set_map_insert_commute(value, |g: RegisterConstraint| g@);
}

pub(crate) proof fn lemma_register_views_empty()
    ensures register_views(Seq::empty()) == Set::<implementation::RegisterView>::empty(),
{
    assert(Seq::<RegisterConstraint>::empty().to_set() =~= Set::<RegisterConstraint>::empty());
    assert(register_views(Seq::empty()) =~= Set::<implementation::RegisterView>::empty());
}

pub(crate) proof fn lemma_codes_concat(a: Seq<u32>, b: Seq<u32>)
    ensures codes(a + b) == codes(a).union(codes(b)),
{
    vstd::seq_lib::seq_to_set_distributes_over_add(a, b);
    assert((a + b).to_set() =~= a.to_set().union(b.to_set()));
    a.to_set().lemma_map_union_commute(b.to_set(), |v: u32| v as nat);
    assert(codes(a + b) =~= codes(a).union(codes(b)));
}
}

verus! {
pub(crate) proof fn lemma_register_filter_insert(values: Set<nat>, differs: Set<nat>, value: nat)
    ensures values.insert(value).difference(differs)
        == if differs.contains(value) { values.difference(differs) }
            else { values.difference(differs).insert(value) },
        values.insert(value).difference(differs).map(|v: nat| implementation::RegisterView::Equals(v))
        == if differs.contains(value) { values.difference(differs).map(|v: nat| implementation::RegisterView::Equals(v)) }
            else { values.difference(differs).map(|v: nat| implementation::RegisterView::Equals(v))
                .insert(implementation::RegisterView::Equals(value)) },
{
    if differs.contains(value) {
        assert(values.insert(value).difference(differs) =~= values.difference(differs));
    } else {
        assert(values.insert(value).difference(differs) =~= values.difference(differs).insert(value));
        values.difference(differs).lemma_set_map_insert_commute(value,
            |v: nat| implementation::RegisterView::Equals(v));
    }
}
}

verus! {
pub(crate) open spec fn remaining(values: Seq<u32>, differs: Set<nat>) -> Seq<u32> {
    values.filter(|v: u32| !differs.contains(v as nat))
}

pub(crate) open spec fn register_count(current: implementation::RegisterView, register: bool,
    constants: Seq<u32>, universe: Universe) -> nat {
    match current {
        implementation::RegisterView::Equals(_) => 1,
        implementation::RegisterView::Differs(differs) => if !register { 1 }
            else { match universe {
                Some(values) => remaining((*values)@, differs).len(),
                None => if remaining(constants, differs).len() == 0 { 1 }
                    else { remaining(constants, differs).len() + 1 },
            } },
    }
}

pub(crate) open spec fn split_capacity(g: Constraint, operands: Operands, universes: Universes) -> bool {
    let sizes = Seq::new(g@.len(), |i: int| register_count(g.0[i]@, operands.register[i], operands.constants[i].view(), universes[i]));
    forall|i: int| 0 <= i <= sizes.len() ==> product_size(sizes.take(i)) <= usize::MAX
}
}

verus! {
pub(crate) open spec fn finite_product<T>(axes: Seq<Set<T>>) -> Set<Seq<T>>
    decreases axes.len(),
{
    if axes.len() == 0 { Set::empty().insert(Seq::empty()) } else {
        finite_product(axes.drop_last()).map(|prefix: Seq<T>|
            axes.last().map(|value: T| prefix.push(value))).flatten()
    }
}

pub(crate) proof fn lemma_finite_product_members<T>(axes: Seq<Set<T>>)
    ensures forall|row: Seq<T>| #[trigger] finite_product(axes).contains(row)
        == (row.len() == axes.len() && forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(row[i])),
    decreases axes.len(),
{
    broadcast use vstd::set::Set::lemma_flatten_contains;
    if axes.len() > 0 {
        let prior = axes.drop_last();
        lemma_finite_product_members(prior);
        let f = |prefix: Seq<T>| axes.last().map(|value: T| prefix.push(value));
        assert forall|row: Seq<T>| finite_product(axes).contains(row)
            implies row.len() == axes.len() && forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(row[i]) by {
            let s = choose|s: Set<Seq<T>>| finite_product(prior).map(f).contains(s) && s.contains(row);
            let prefix = choose|prefix: Seq<T>| finite_product(prior).contains(prefix) && f(prefix) == s;
            let value = choose|value: T| axes.last().contains(value) && prefix.push(value) == row;
        }
        assert forall|row: Seq<T>| row.len() == axes.len()
            && (forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(row[i]))
            implies finite_product(axes).contains(row) by {
            let prefix = row.drop_last();
            assert(prefix.push(row.last()) =~= row);
            assert(finite_product(prior).contains(prefix));
            assert(f(prefix).contains(row));
            assert(finite_product(prior).map(f).contains(f(prefix)));
        }
    } else {
        assert forall|row: Seq<T>| row.len() == 0 implies row == Seq::<T>::empty() by { assert(row =~= Seq::<T>::empty()); }
    }
}

pub(crate) open spec fn register_product(axes: Seq<Set<implementation::RegisterView>>) -> Set<implementation::ConstraintView> {
    finite_product(axes)
}

pub(crate) open spec fn choice_view(axes: Seq<Seq<RegisterConstraint>>, position: Seq<usize>) -> implementation::ConstraintView {
    Seq::new(axes.len(), |i: int| axes[i][position[i] as int]@)
}

pub(crate) open spec fn product_done(axes: Seq<Seq<RegisterConstraint>>, result: Set<implementation::ConstraintView>, count: nat) -> bool {
    forall|p: Seq<usize>| row_valid(axis_sizes(axes), p) && row_rank(axis_sizes(axes), p) < count
        ==> result.contains(choice_view(axes, p))
}

pub(crate) open spec fn axis_sizes<T>(axes: Seq<Seq<T>>) -> Seq<nat> {
    axes.map_values(|axis: Seq<T>| axis.len())
}

pub(crate) proof fn lemma_constraint_views_push(values: Seq<Constraint>, value: Constraint)
    ensures constraint_views(values.push(value)) == constraint_views(values).insert(value@),
{
    values.lemma_push_to_set_commute(value);
    values.to_set().lemma_set_map_insert_commute(value, |g: Constraint| g@);
}

pub(crate) proof fn lemma_register_product_members(axes: Seq<Set<implementation::RegisterView>>)
    ensures forall|g: implementation::ConstraintView| #[trigger] register_product(axes).contains(g)
        == (g.len() == axes.len() && forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(g[i])),
{ lemma_finite_product_members(axes); }

pub(crate) proof fn lemma_product_step(axes: Seq<Seq<RegisterConstraint>>, before: Set<implementation::ConstraintView>,
    after: Set<implementation::ConstraintView>, position: Seq<usize>, count: nat)
    requires row_valid(axis_sizes(axes), position), row_rank(axis_sizes(axes), position) == count,
        product_done(axes, before, count), after == before.insert(choice_view(axes, position)),
    ensures product_done(axes, after, count + 1),
{
    assert forall|p: Seq<usize>| row_valid(axis_sizes(axes), p) && row_rank(axis_sizes(axes), p) < count + 1
        implies after.contains(choice_view(axes, p)) by {
        if row_rank(axis_sizes(axes), p) == count {
            constraint_unique::lemma_row_rank_injective(axis_sizes(axes), p, position);
        }
    }
}
}

verus! {
pub(crate) proof fn lemma_register_view_at(values: Seq<RegisterConstraint>, index: int)
    requires 0 <= index < values.len(),
    ensures register_views(values).contains(values[index]@),
    decreases values.len(),
{
    let prior = values.drop_last();
    assert(prior.push(values.last()) =~= values);
    lemma_register_views_push(prior, values.last());
    if index < prior.len() {
        lemma_register_view_at(prior, index);
        assert(prior[index] == values[index]);
    } else { assert(values[index] == values.last()); }
}
}

verus! {
pub(crate) open spec fn bounded_codes(values: Set<nat>) -> bool {
    forall|v: nat| #[trigger] values.contains(v) ==> v <= u32::MAX
}

pub(crate) open spec fn register_codes(r: implementation::RegisterView) -> Set<nat> {
    match r { implementation::RegisterView::Equals(v) => Set::empty().insert(v),
        implementation::RegisterView::Differs(vs) => vs }
}

pub(crate) open spec fn register_allowed(domain: Option<Set<nat>>, value: nat) -> bool {
    value <= u64::MAX && match domain { None => true, Some(vs) => vs.contains(value) }
}

pub(crate) proof fn lemma_register_options_members(current: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>, target: implementation::RegisterView)
    ensures register_options(current, register, constants, domain).contains(target)
        == match current {
            implementation::RegisterView::Equals(_) => target == current,
            implementation::RegisterView::Differs(differs) => if !register { target == current }
                else { match domain {
                    Some(values) => match target { implementation::RegisterView::Equals(v)
                        => values.contains(v) && !differs.contains(v), _ => false },
                    None => {
                        let undecided = constants.difference(differs);
                        if undecided.len() == 0 { target == current }
                        else { match target {
                            implementation::RegisterView::Equals(v) => undecided.contains(v),
                            implementation::RegisterView::Differs(vs) => vs == differs.union(undecided),
                        } }
                    },
                } },
        },
{
    match current {
        implementation::RegisterView::Equals(_) => {},
        implementation::RegisterView::Differs(differs) => if register {
            match domain {
                Some(values) => match target {
                    implementation::RegisterView::Equals(v) => {
                        if values.contains(v) && !differs.contains(v) {
                            assert(values.difference(differs).contains(v));
                        }
                    },
                    implementation::RegisterView::Differs(_) => {},
                },
                None => {
                    let undecided = constants.difference(differs);
                    if undecided.len() == 0 { undecided.lemma_len0_is_empty(); }
                    else { match target {
                        implementation::RegisterView::Equals(v) => {},
                        implementation::RegisterView::Differs(vs) => {},
                    } }
                },
            }
        },
    }
}

pub(crate) proof fn lemma_register_options_cover(current: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>, value: nat) -> (target: implementation::RegisterView)
    requires register_sat(current, value), register_allowed(domain, value),
    ensures register_options(current, register, constants, domain).contains(target), register_sat(target, value),
{
    let target = match current {
        implementation::RegisterView::Equals(_) => current,
        implementation::RegisterView::Differs(differs) => if !register { current }
            else { match domain {
                Some(_) => implementation::RegisterView::Equals(value),
                None => {
                    let undecided = constants.difference(differs);
                    if undecided.len() == 0 { current }
                    else if undecided.contains(value) { implementation::RegisterView::Equals(value) }
                    else { implementation::RegisterView::Differs(differs.union(undecided)) }
                },
            } },
    };
    lemma_register_options_members(current, register, constants, domain, target);
    target
}

pub(crate) proof fn lemma_register_options_unique(current: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>, a: implementation::RegisterView,
    b: implementation::RegisterView, value: nat)
    requires register_options(current, register, constants, domain).contains(a),
        register_options(current, register, constants, domain).contains(b),
        register_sat(a, value), register_sat(b, value),
    ensures a == b,
{
    lemma_register_options_members(current, register, constants, domain, a);
    lemma_register_options_members(current, register, constants, domain, b);
    match current {
        implementation::RegisterView::Equals(_) => {},
        implementation::RegisterView::Differs(differs) => if register {
            match domain {
                Some(_) => {},
                None => {
                    let undecided = constants.difference(differs);
                    if undecided.len() != 0 { match (a, b) {
                        (implementation::RegisterView::Equals(v), implementation::RegisterView::Differs(vs)) => {
                            assert(vs.contains(v));
                        },
                        (implementation::RegisterView::Differs(vs), implementation::RegisterView::Equals(v)) => {
                            assert(vs.contains(v));
                        },
                        _ => {},
                    } }
                },
            }
        },
    }
}

pub(crate) proof fn lemma_register_options_sound(current: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>, target: implementation::RegisterView)
    requires bounded_codes(register_codes(current)), bounded_codes(constants),
        domain matches Some(vs) ==> bounded_codes(vs),
        exists|v: nat| register_allowed(domain, v) && register_sat(current, v),
        register_options(current, register, constants, domain).contains(target),
    ensures exists|v: nat| register_allowed(domain, v) && register_sat(target, v),
        forall|v: nat| register_sat(target, v) ==> register_sat(current, v),
{
    lemma_register_options_members(current, register, constants, domain, target);
    if target != current {
        match current {
            implementation::RegisterView::Equals(_) => {},
            implementation::RegisterView::Differs(differs) => match target {
                implementation::RegisterView::Equals(v) => {
                    assert(register_allowed(domain, v));
                    assert(register_sat(target, v));
                },
                implementation::RegisterView::Differs(vs) => {
                    assert(domain is None);
                    assert(bounded_codes(vs));
                    assert(!vs.contains(0x100000000nat));
                    assert(register_allowed(domain, 0x100000000nat) && register_sat(target, 0x100000000nat));
                },
            },
        }
    }
}
}

verus! {
pub(crate) proof fn lemma_operand_atoms(operands: Operands, atoms: Seq<Atom>)
    requires operands_of(operands, atoms),
    ensures search::atoms_local(atom_set(atoms)), search::atoms_bounded(atom_set(atoms), operands.register@.len()),
        forall|c: Component| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c)))
            == (c.0 < operands.register@.len() && operands.register[c.0 as int]),
        forall|c: Component, v: nat| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
            == (c.0 < operands.register@.len() && codes(operands.constants[c.0 as int].view()).contains(v)),
{
    assert forall|p: model::Primitive| #[trigger] atom_set(atoms).contains(p)
        == (exists|i: int| 0 <= i < atoms.len() && atoms[i]@ == p) by {
        if atom_set(atoms).contains(p) {
            let a = choose|a: Atom| atoms.to_set().contains(a) && a@ == p;
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i] == a;
        } else if exists|i: int| 0 <= i < atoms.len() && atoms[i]@ == p {
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i]@ == p;
            assert(atoms.to_set().contains(atoms[i]));
        }
    }
    assert forall|p: model::Primitive| atom_set(atoms).contains(p) implies
        match p { model::Primitive::Eq(c, t) => c.0 < operands.register@.len()
            && match t { model::GTerm::Variable(v) => v == c, _ => true } } by {
        let i = choose|i: int| 0 <= i < atoms.len() && atoms[i]@ == p;
        assert(atoms[i].component < operands.register@.len());
        match atoms[i].operand { Operand::Register => {}, Operand::Constant(_) => {} }
    }
    assert forall|c: Component| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c)))
        == (c.0 < operands.register@.len() && operands.register[c.0 as int]) by {
        if c.0 < operands.register@.len() {
            if operands.register[c.0 as int] {
                let i = choose|i: int| 0 <= i < atoms.len() && atoms[i].component == c.0
                    && atoms[i].operand == Operand::Register;
                assert(atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Variable(c)));
            } else if atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c))) {
                let i = choose|i: int| 0 <= i < atoms.len() && atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Variable(c));
                assert(atoms[i].component == c.0 && atoms[i].operand == Operand::Register);
            }
        }
    }
    assert forall|c: Component, v: nat| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
        == (c.0 < operands.register@.len() && codes(operands.constants[c.0 as int].view()).contains(v)) by {
        if c.0 < operands.register@.len() {
            let k = c.0 as int;
            lemma_codes(operands.constants[k].view());
            if atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v))) {
                let i = choose|i: int| 0 <= i < atoms.len() && atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Constant(v));
                match atoms[i].operand {
                    Operand::Constant(w) => { assert(operands.constants[k].view().contains(w)); },
                    Operand::Register => {},
                }
            } else if codes(operands.constants[k].view()).contains(v) {
                let j = choose|j: int| 0 <= j < operands.constants[k].view().len() && operands.constants[k].view()[j] as nat == v;
                let w = operands.constants[k].view()[j];
                let i = choose|i: int| 0 <= i < atoms.len() && atoms[i].component == k && atoms[i].operand == Operand::Constant(w);
                assert(atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Constant(v)));
            }
        }
    }
}

pub(crate) proof fn lemma_operand_pairs(operands: Operands, atoms: Seq<Atom>, universes: Universes)
    requires operands_of(operands, atoms), operands.register@.len() == universes@.len(),
    ensures forall|p: (Component, nat)| #[trigger] search::domain_pairs(ndomains(universes), atom_set(atoms)).contains(p)
        == (p.0.0 < universes@.len() && operands.register[p.0.0 as int]
            && (codes(operands.constants[p.0.0 as int].view()).contains(p.1)
                || match domain_view(universes[p.0.0 as int]) { None => false, Some(vs) => vs.contains(p.1) })),
{
    lemma_operand_atoms(operands, atoms);
    search::lemma_atom_pairs_members(atom_set(atoms));
    search::lemma_domain_pairs_members(ndomains(universes), atom_set(atoms));
}

pub(crate) proof fn lemma_register_bounded(register: RegisterConstraint)
    ensures bounded_codes(register_codes(register@)),
{
    match register {
        RegisterConstraint::Equals(v) => {},
        RegisterConstraint::Differs(vs) => { lemma_codes(vs.view()); },
    }
}

pub(crate) proof fn lemma_domain_bounded(universe: Universe)
    ensures domain_view(universe) matches Some(vs) ==> bounded_codes(vs),
{
    if let Some(values) = universe { lemma_codes((*values)@); }
}
}

verus! {
pub(crate) proof fn lemma_constraint_decides(d: encoding::NDomains, g: implementation::ConstraintView, c: Component, value: nat)
    requires g.len() == d.len(), g.len() <= history_syntax::MAX_ARITY, c.0 < g.len(),
        implementation::register_of(g, c) is Equals || !register_sat(implementation::register_of(g, c), value),
    ensures inclusion::decides(d, implementation::constraint_of(g), c, value),
{
    let equal = match implementation::register_of(g, c) { implementation::RegisterView::Equals(v) => v == value, _ => false };
    let l = inclusion::Literal { component: c, value, equal };
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta) && inclusion::sat_by(theta, implementation::constraint_of(g))
        implies inclusion::sat_by(theta, Set::empty().insert(l)) by {
        lemma_constraint_sat(g, theta);
        assert(register_sat(g[c.0 as int], theta[c.0 as int]));
    }
}

pub(crate) proof fn lemma_register_option_decision(current: implementation::RegisterView,
    constants: Set<nat>, domain: Option<Set<nat>>, target: implementation::RegisterView, value: nat)
    requires register_options(current, true, constants, domain).contains(target),
        constants.contains(value) || match domain { None => false, Some(vs) => vs.contains(value) },
    ensures target is Equals || !register_sat(target, value),
{
    lemma_register_options_members(current, true, constants, domain, target);
    match current {
        implementation::RegisterView::Equals(_) => {},
        implementation::RegisterView::Differs(differs) => match domain {
            Some(_) => {},
            None => {
                let undecided = constants.difference(differs);
                match target {
                    implementation::RegisterView::Equals(_) => {},
                    implementation::RegisterView::Differs(vs) => {
                        if undecided.len() == 0 {
                            undecided.lemma_len0_is_empty();
                            assert(vs == differs);
                            assert(constants.contains(value));
                            assert(!undecided.contains(value));
                            if !differs.contains(value) { assert(undecided.contains(value)); }
                            assert(differs.contains(value));
                        } else {
                            assert(vs == differs.union(undecided));
                            if !differs.contains(value) { assert(undecided.contains(value)); }
                            assert(vs.contains(value));
                        }
                    },
                }
            },
        },
    }
}

pub(crate) proof fn lemma_split_options_sound(g: Constraint, operands: Operands, universes: Universes, target: implementation::ConstraintView)
    requires shape_wf(g, operands, universes),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)), split_views(g, operands, universes).contains(target),
    ensures target.len() == g@.len(), inclusion::satisfiable(ndomains(universes), implementation::constraint_of(target)),
        inclusion::entails(ndomains(universes), implementation::constraint_of(target), implementation::constraint_of(g@)),
{
    let d = ndomains(universes);
    let theta0 = choose|theta: Subst| encoding::n_theta_ok(d, theta) && inclusion::sat_by(theta, implementation::constraint_of(g@));
    lemma_theta_allowed(universes, theta0); lemma_constraint_sat(g@, theta0);
    lemma_register_product_members(split_axes(g, operands, universes));
assert forall|i: int| #![trigger target[i]] 0 <= i < g@.len() implies
        (exists|v: nat| register_allowed(domain_view(universes[i]), v) && register_sat(target[i], v))
        && (forall|v: nat| register_sat(target[i], v) ==> register_sat(g.0[i]@, v)) by {
        lemma_register_bounded(g.0[i]); lemma_domain_bounded(universes[i]); lemma_codes(operands.constants[i].view());
assert(g@[i] == g.0@[i]@);
assert(g.0[i] == g.0@[i]);
assert(register_sat(g@[i], theta0[i]));
assert(register_sat(g.0[i]@, theta0[i]));
assert(register_allowed(domain_view(universes[i]), theta0[i]));
assert(exists|v: nat| register_allowed(domain_view(universes[i]), v) && register_sat(g.0[i]@, v));
lemma_register_options_sound(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i]), target[i]);
    }
    let theta = Seq::new(g@.len(), |i: int| choose|v: nat| register_allowed(domain_view(universes[i]), v) && register_sat(target[i], v));
    lemma_constraint_sat(target, theta);
    assert(encoding::n_theta_ok(d, theta));
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta) && inclusion::sat_by(theta, implementation::constraint_of(target))
        implies inclusion::sat_by(theta, implementation::constraint_of(g@)) by {
        lemma_constraint_sat(target, theta); lemma_constraint_sat(g@, theta);
    }
}

pub(crate) proof fn lemma_split_views_ok(g: Constraint, operands: Operands, universes: Universes, atoms: Seq<Atom>)
    requires shape_wf(g, operands, universes), operands_of(operands, atoms),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
    ensures inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
        search::domain_pairs(ndomains(universes), atom_set(atoms)),
        split_views(g, operands, universes).map(|v: implementation::ConstraintView| implementation::constraint_of(v))),
{
    reveal(inclusion::split_ok);
    let d = ndomains(universes);
    let options = split_views(g, operands, universes);
    let cases = options.map(|v: implementation::ConstraintView| implementation::constraint_of(v));
    let pi = search::domain_pairs(d, atom_set(atoms));
    lemma_operand_pairs(operands, atoms, universes);
    lemma_register_product_members(split_axes(g, operands, universes));
    assert forall|gamma: inclusion::Constraint| #[trigger] cases.contains(gamma) implies
        inclusion::satisfiable(d, gamma) && inclusion::entails(d, gamma, implementation::constraint_of(g@))
        && forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] inclusion::decides(d, gamma, p.0, p.1) by {
        let target = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma;
        lemma_split_options_sound(g, operands, universes, target);
        assert forall|p: (Component, nat)| pi.contains(p) implies inclusion::decides(d, gamma, p.0, p.1) by {
            let i = p.0.0 as int;
            lemma_register_option_decision(g.0[i]@, codes(operands.constants[i].view()), domain_view(universes[i]), target[i], p.1);
            lemma_constraint_decides(d, target, p.0, p.1);
        }
    }
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta) && #[trigger] inclusion::sat_by(theta, implementation::constraint_of(g@))
        implies exists|gamma: inclusion::Constraint| #[trigger] cases.contains(gamma) && inclusion::sat_by(theta, gamma) by {
        lemma_constraint_sat(g@, theta); lemma_theta_allowed(universes, theta);
        assert forall|i: int| #![trigger split_axes(g, operands, universes)[i]] 0 <= i < g@.len() implies exists|r: implementation::RegisterView|
            split_axes(g, operands, universes)[i].contains(r) && register_sat(r, theta[i]) by {
            lemma_register_options_cover(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i]), theta[i]);
        }
        let target = Seq::new(g@.len(), |i: int| choose|r: implementation::RegisterView|
            split_axes(g, operands, universes)[i].contains(r) && register_sat(r, theta[i]));
        assert(options.contains(target)); lemma_constraint_sat(target, theta);
        assert(cases.contains(implementation::constraint_of(target)));
    }
    assert forall|theta: Subst, gamma1: inclusion::Constraint, gamma2: inclusion::Constraint|
        encoding::n_theta_ok(d, theta) && cases.contains(gamma1) && cases.contains(gamma2)
        && #[trigger] inclusion::sat_by(theta, gamma1) && #[trigger] inclusion::sat_by(theta, gamma2) implies gamma1 == gamma2 by {
        let a = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma1;
        let b = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma2;
        lemma_constraint_sat(a, theta); lemma_constraint_sat(b, theta);
        assert forall|i: int| 0 <= i < g@.len() implies a[i] == b[i] by {
            lemma_register_options_unique(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i]), a[i], b[i], theta[i]);
        }
        assert(a =~= b);
    }
}
}

verus! {
pub(crate) proof fn lemma_theta_allowed(universes: Universes, theta: Subst)
    requires encoding::n_theta_ok(ndomains(universes), theta),
    ensures theta.len() == universes@.len(),
        forall|i: int| 0 <= i < universes@.len() ==> register_allowed(domain_view(universes[i]), theta[i]),
{
    let d = ndomains(universes);
    assert(d.len() == universes@.len());
    assert(language::event_wf(theta, d.len()));
    assert(encoding::n_event_in(d, theta));
    assert forall|i: int| 0 <= i < universes@.len() implies register_allowed(domain_view(universes[i]), theta[i]) by {
        assert(d[i] == domain_view(universes@[i]));
        assert(universes[i] == universes@[i]);
        assert(theta[i] <= u64::MAX);
        match d[i] {
            None => {}, Some(vs) => { assert(vs.contains(theta[i])); },
        }
    }
}
}

verus! {
pub(crate) open spec fn register_class(r: implementation::RegisterView) -> implementation::ClassView {
    match r { implementation::RegisterView::Equals(v) => implementation::ClassView::Constant(v),
        implementation::RegisterView::Differs(_) => implementation::ClassView::Register }
}

pub(crate) open spec fn named_codes(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>) -> Set<nat> {
    let names = match domain { None => constants, Some(vs) => constants.intersect(vs) };
    if register { match r { implementation::RegisterView::Equals(v) => names.insert(v), _ => names } }
    else { names }
}

pub(crate) open spec fn first_other_index(values: Seq<u32>, names: Set<nat>) -> Option<int> {
    values.map(|i: int, v: u32| names.contains(v as nat)).index_of_first(false)
}

pub(crate) open spec fn first_other(values: Seq<u32>, names: Set<nat>) -> Option<u32> {
    match first_other_index(values, names) { None => None, Some(i) => Some(values[i]) }
}

pub(crate) open spec fn option_views(values: Seq<Option<Class>>) -> Set<Option<implementation::ClassView>> {
    values.to_set().map(|c: Option<Class>| class_option(c))
}

pub(crate) open spec fn class_options(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, universe: Universe) -> Set<Option<implementation::ClassView>> {
    let names = named_codes(r, register, constants, domain_view(universe));
    let choices = names.map(|v: nat| Some(implementation::ClassView::Constant(v)));
    let choices = if register && r is Differs { choices.insert(Some(implementation::ClassView::Register)) }
        else { choices };
    match universe {
        None => choices.insert(None),
        Some(values) => match first_other((*values)@, names) {
            None => choices, Some(v) => choices.insert(Some(implementation::ClassView::Constant(v as nat))),
        },
    }
}

pub(crate) proof fn lemma_first_other(values: Seq<u32>, names: Set<nat>)
    ensures match first_other_index(values, names) {
        Some(i) => 0 <= i < values.len() && !names.contains(values[i] as nat)
            && forall|j: int| 0 <= j < i ==> names.contains(values[j] as nat),
        None => forall|j: int| 0 <= j < values.len() ==> names.contains(values[j] as nat),
    },
{
    let flags = values.map(|i: int, v: u32| names.contains(v as nat));
    flags.index_of_first_ensures(false);
    assert(flags.len() == values.len());
    match first_other_index(values, names) {
        None => {
            assert forall|j: int| 0 <= j < values.len() implies names.contains(values[j] as nat) by {
                assert(flags.contains(flags[j]));
                assert(flags[j] != false);
            }
        },
        Some(i) => {
            assert(flags[i] == names.contains(values[i] as nat));
            assert forall|j: int| 0 <= j < i implies names.contains(values[j] as nat) by {
                assert(flags[j] != false);
                assert(flags[j] == names.contains(values[j] as nat));
            }
        },
    }
}

pub(crate) proof fn lemma_option_views_push(values: Seq<Option<Class>>, value: Option<Class>)
    ensures option_views(values.push(value)) == option_views(values).insert(class_option(value)),
{
    values.lemma_push_to_set_commute(value);
    values.to_set().lemma_set_map_insert_commute(value, |c: Option<Class>| class_option(c));
}

pub(crate) open spec fn letter_capacity(g: Constraint, operands: Operands, universes: Universes) -> bool {
    let sizes = letter_axes(g, operands, universes).map_values(|axis: Set<Option<implementation::ClassView>>| axis.len());
    forall|i: int| 0 <= i <= sizes.len() ==> product_size(sizes.take(i)) <= usize::MAX
}
}

verus! {
pub(crate) proof fn lemma_first_other_at(values: Seq<u32>, names: Set<nat>, index: int)
    requires 0 <= index < values.len(), !names.contains(values[index] as nat),
        forall|i: int| 0 <= i < index ==> names.contains(values[i] as nat),
    ensures first_other_index(values, names) == Some(index), first_other(values, names) == Some(values[index]),
{
    lemma_first_other(values, names);
    match first_other_index(values, names) {
        None => {},
        Some(i) => {
            if i < index { assert(names.contains(values[i] as nat)); }
            else if i > index { assert(names.contains(values[index] as nat)); }
        },
    }
}

pub(crate) proof fn lemma_constant_choices_insert(initial: Set<Option<implementation::ClassView>>,
    names: Set<nat>, value: nat)
    ensures initial.union(names.map(|v: nat| Some(implementation::ClassView::Constant(v))))
        .insert(Some(implementation::ClassView::Constant(value)))
        == initial.union(names.insert(value).map(|v: nat| Some(implementation::ClassView::Constant(v)))),
{
    names.lemma_set_map_insert_commute(value, |v: nat| Some(implementation::ClassView::Constant(v)));
    assert(initial.union(names.map(|v: nat| Some(implementation::ClassView::Constant(v))))
        .insert(Some(implementation::ClassView::Constant(value)))
        =~= initial.union(names.insert(value).map(|v: nat| Some(implementation::ClassView::Constant(v)))));
}

pub(crate) proof fn lemma_filtered_codes(values: Seq<u32>, domain: Option<Set<nat>>)
    ensures codes(values.filter(|v: u32| match domain { None => true, Some(vs) => vs.contains(v as nat) }))
        == match domain { None => codes(values), Some(vs) => codes(values).intersect(vs) },
{
    let pred = |v: u32| match domain { None => true, Some(vs) => vs.contains(v as nat) };
    lemma_codes(values); lemma_codes(values.filter(pred));
    assert forall|v: nat| codes(values.filter(pred)).contains(v)
        == (codes(values).contains(v) && match domain { None => true, Some(vs) => vs.contains(v) }) by {
        if codes(values.filter(pred)).contains(v) {
            let i = choose|i: int| 0 <= i < values.filter(pred).len() && values.filter(pred)[i] as nat == v;
            let w = values.filter(pred)[i];
            values.lemma_filter_contains_rev(pred, w);
            assert(codes(values).contains(v));
        } else if codes(values).contains(v) && match domain { None => true, Some(vs) => vs.contains(v) } {
            let i = choose|i: int| 0 <= i < values.len() && values[i] as nat == v;
            values.lemma_filter_contains(pred, i);
            assert(values.filter(pred).contains(values[i]));
        }
    }
    match domain {
        None => { assert(codes(values.filter(pred)) =~= codes(values)); },
        Some(vs) => { assert(codes(values.filter(pred)) =~= codes(values).intersect(vs)); },
    }
}
}

verus! {
pub(crate) proof fn lemma_option_views_empty()
    ensures option_views(Seq::empty()) == Set::<Option<implementation::ClassView>>::empty(),
{
    assert(Seq::<Option<Class>>::empty().to_set() =~= Set::<Option<Class>>::empty());
    assert(option_views(Seq::empty()) =~= Set::<Option<implementation::ClassView>>::empty());
}
}

verus! {
pub(crate) open spec fn raw_register_class(r: RegisterConstraint) -> Class {
    match r { RegisterConstraint::Equals(v) => Class::Constant(v), RegisterConstraint::Differs(_) => Class::Register }
}

pub(crate) open spec fn letter_product(axes: Seq<Set<Option<implementation::ClassView>>>, registers: Seq<Class>) -> Set<implementation::LetterView> {
    finite_product(axes).map(|classes: Seq<Option<implementation::ClassView>>| implementation::LetterView {
        classes, registers: registers.map_values(|c: Class| c@),
    })
}

pub(crate) open spec fn letters_views(g: Constraint, operands: Operands, universes: Universes) -> Set<implementation::LetterView> {
    letter_product(letter_axes(g, operands, universes), g.0@.map_values(|r: RegisterConstraint| raw_register_class(r)))
}

pub(crate) open spec fn letter_axes(g: Constraint, operands: Operands, universes: Universes) -> Seq<Set<Option<implementation::ClassView>>> {
    Seq::new(g@.len(), |i: int| class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]))
}

pub(crate) open spec fn letter_views(values: Seq<Letter>) -> Set<implementation::LetterView> {
    values.to_set().map(|l: Letter| l@)
}

pub(crate) open spec fn letter_choice_view(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, position: Seq<usize>) -> implementation::LetterView {
    implementation::LetterView { classes: Seq::new(axes.len(), |i: int| class_option(axes[i][position[i] as int])),
        registers: registers.map_values(|c: Class| c@) }
}

pub(crate) open spec fn letter_product_done(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, result: Set<implementation::LetterView>, count: nat) -> bool {
    forall|p: Seq<usize>| row_valid(axis_sizes(axes), p) && row_rank(axis_sizes(axes), p) < count
        ==> result.contains(letter_choice_view(axes, registers, p))
}

pub(crate) proof fn lemma_letter_views_push(values: Seq<Letter>, value: Letter)
    ensures letter_views(values.push(value)) == letter_views(values).insert(value@),
{
    values.lemma_push_to_set_commute(value);
    values.to_set().lemma_set_map_insert_commute(value, |l: Letter| l@);
}

pub(crate) proof fn lemma_option_view_at(values: Seq<Option<Class>>, index: int)
    requires 0 <= index < values.len(),
    ensures option_views(values).contains(class_option(values[index])),
    decreases values.len(),
{
    let prior = values.drop_last();
    assert(prior.push(values.last()) =~= values);
    lemma_option_views_push(prior, values.last());
    if index < prior.len() {
        lemma_option_view_at(prior, index);
        assert(prior[index] == values[index]);
    } else { assert(values[index] == values.last()); }
}

pub(crate) proof fn lemma_letter_product_members(axes: Seq<Set<Option<implementation::ClassView>>>, registers: Seq<Class>)
    ensures forall|l: implementation::LetterView| #[trigger] letter_product(axes, registers).contains(l)
        == (l.classes.len() == axes.len() && l.registers == registers.map_values(|c: Class| c@)
            && forall|i: int| 0 <= i < axes.len() ==> #[trigger] axes[i].contains(l.classes[i])),
{
    lemma_finite_product_members(axes);
    assert forall|l: implementation::LetterView| letter_product(axes, registers).contains(l)
        implies l.classes.len() == axes.len() && l.registers == registers.map_values(|c: Class| c@)
            && forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(l.classes[i]) by {
        let cs = choose|cs: Seq<Option<implementation::ClassView>>| finite_product(axes).contains(cs)
            && implementation::LetterView { classes: cs, registers: registers.map_values(|c: Class| c@) } == l;
    }
    assert forall|l: implementation::LetterView| l.classes.len() == axes.len()
        && l.registers == registers.map_values(|c: Class| c@)
        && (forall|i: int| 0 <= i < axes.len() ==> axes[i].contains(l.classes[i]))
        implies letter_product(axes, registers).contains(l) by {
        assert(finite_product(axes).contains(l.classes));
        assert(implementation::LetterView { classes: l.classes, registers: registers.map_values(|c: Class| c@) } == l);
    }
}

pub(crate) proof fn lemma_letter_product_step(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>,
    before: Set<implementation::LetterView>, after: Set<implementation::LetterView>, position: Seq<usize>, count: nat)
    requires row_valid(axis_sizes(axes), position), row_rank(axis_sizes(axes), position) == count,
        letter_product_done(axes, registers, before, count), after == before.insert(letter_choice_view(axes, registers, position)),
    ensures letter_product_done(axes, registers, after, count + 1),
{
    assert forall|p: Seq<usize>| row_valid(axis_sizes(axes), p) && row_rank(axis_sizes(axes), p) < count + 1
        implies after.contains(letter_choice_view(axes, registers, p)) by {
        if row_rank(axis_sizes(axes), p) == count {
            constraint_unique::lemma_row_rank_injective(axis_sizes(axes), p, position);
        }
    }
}
}

verus! {
pub(crate) open spec fn field_ready(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, domain: Option<Set<nat>>) -> bool {
    !register || ((forall|v: nat| #[trigger] constants.contains(v) ==> r is Equals || !register_sat(r, v))
        && (domain is Some ==> r is Equals))
}

pub(crate) open spec fn field_letter(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, class: Option<implementation::ClassView>, theta: nat, event: nat) -> bool {
    &&& forall|v: nat| #[trigger] constants.contains(v)
        ==> (class == Some(implementation::ClassView::Constant(v))) == (event == v)
    &&& register ==> (class == Some(register_class(r))) == (event == theta)
}

pub(crate) proof fn lemma_class_options_members(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, universe: Universe, class: Option<implementation::ClassView>)
    ensures class_options(r, register, constants, universe).contains(class) == match class {
        None => universe is None,
        Some(implementation::ClassView::Register) => register && r is Differs,
        Some(implementation::ClassView::Constant(v)) => named_codes(r, register, constants, domain_view(universe)).contains(v)
            || match universe { None => false, Some(values) =>
                first_other((*values)@, named_codes(r, register, constants, domain_view(universe)))
                    matches Some(w) && w as nat == v },
    },
{
    match class {
        None => {},
        Some(implementation::ClassView::Register) => {},
        Some(implementation::ClassView::Constant(v)) => {},
    }
}

pub(crate) proof fn lemma_field_letter_sound(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, universe: Universe, class: Option<implementation::ClassView>, theta: nat)
    -> (event: nat)
    requires register_allowed(domain_view(universe), theta), register_sat(r, theta),
        field_ready(r, register, constants, domain_view(universe)),
        class_options(r, register, constants, universe).contains(class),
    ensures domain_view(universe) matches Some(vs) ==> vs.contains(event),
        field_letter(r, register, constants, class, theta, event),
{
    lemma_class_options_members(r, register, constants, universe, class);
    match class {
        None => {
            let event = search::lemma_finite_nat_bound(constants.insert(theta));
            assert(constants.insert(theta).contains(theta));
            assert(theta < event);
            if constants.contains(event) { assert(constants.insert(theta).contains(event)); }
            assert(!constants.contains(event));
            assert(event != theta);
            event
        },
        Some(implementation::ClassView::Register) => {
            assert(universe is None);
            assert forall|v: nat| constants.contains(v) implies theta != v by {
                assert(!register_sat(r, v));
            }
            theta
        },
        Some(implementation::ClassView::Constant(v)) => {
            let names = named_codes(r, register, constants, domain_view(universe));
            if let Some(values) = universe {
                lemma_codes((*values)@);
                lemma_first_other((*values)@, names);
                assert(codes((*values)@).contains(v));
            }
            if register { match r {
                implementation::RegisterView::Equals(w) => {},
                implementation::RegisterView::Differs(vs) => {
                    assert(universe is None);
                    assert(constants.contains(v));
                    assert(!register_sat(r, v));
                    assert(v != theta);
                },
            } }
            v
        },
    }
}

pub(crate) proof fn lemma_field_letter_complete(r: implementation::RegisterView, register: bool,
    constants: Set<nat>, universe: Universe, theta: nat, event: nat)
    -> (class: Option<implementation::ClassView>)
    requires register_allowed(domain_view(universe), theta), register_sat(r, theta),
        field_ready(r, register, constants, domain_view(universe)),
        domain_view(universe) matches Some(vs) ==> vs.contains(event),
    ensures class_options(r, register, constants, universe).contains(class),
        field_letter(r, register, constants, class, theta, event),
{
    let names = named_codes(r, register, constants, domain_view(universe));
    let class = if register && event == theta {
        match r {
            implementation::RegisterView::Equals(v) => Some(implementation::ClassView::Constant(v)),
            implementation::RegisterView::Differs(vs) => {
                assert forall|v: nat| constants.contains(v) implies theta != v by {
                    assert(!register_sat(r, v));
                }
                Some(implementation::ClassView::Register)
            },
        }
    } else if constants.contains(event) {
        Some(implementation::ClassView::Constant(event))
    } else {
        match universe {
            None => None,
            Some(values) => {
                lemma_codes((*values)@);
                lemma_first_other((*values)@, names);
                assert(!names.contains(event));
                if first_other_index((*values)@, names) is None {
                    let i = choose|i: int| 0 <= i < (*values)@.len() && (*values)@[i] as nat == event;
                    assert(names.contains((*values)@[i] as nat));
                }
                let i = first_other_index((*values)@, names)->Some_0;
                let v = (*values)@[i] as nat;
                assert(!names.contains(v));
                assert(!constants.contains(v));
                if register { match r {
                    implementation::RegisterView::Equals(w) => { assert(names.contains(w)); assert(v != w); },
                    implementation::RegisterView::Differs(_) => {},
                } }
                Some(implementation::ClassView::Constant(v))
            },
        }
    };
    lemma_class_options_members(r, register, constants, universe, class);
    class
}

pub(crate) proof fn lemma_refined_ready(g: Constraint, operands: Operands, universes: Universes, refined: implementation::ConstraintView)
    requires shape_wf(g, operands, universes), split_views(g, operands, universes).contains(refined),
    ensures refined.len() == g@.len(), forall|i: int| 0 <= i < refined.len() ==> field_ready(refined[i], operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i])),
{
    lemma_register_product_members(split_axes(g, operands, universes));
    assert forall|i: int| 0 <= i < refined.len() implies field_ready(refined[i], operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i])) by {
        let r = refined[i];
        lemma_register_options_members(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i]), r);
        if operands.register[i] {
            assert forall|v: nat| codes(operands.constants[i].view()).contains(v) implies r is Equals || !register_sat(r, v) by {
                lemma_register_option_decision(g.0[i]@, codes(operands.constants[i].view()), domain_view(universes[i]), r, v);
            }
        }
    }
}
}

verus! {
pub(crate) proof fn lemma_letters_members(g: Constraint, operands: Operands, universes: Universes)
    requires shape_wf(g, operands, universes),
    ensures forall|l: implementation::LetterView| #[trigger] letters_views(g, operands, universes).contains(l)
        == (l.classes.len() == g@.len() && l.registers.len() == g@.len()
            && forall|i: int| 0 <= i < g@.len() ==> #[trigger] class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i])
                && l.registers[i] == register_class(g.0[i]@)),
{
let axes = letter_axes(g, operands, universes);
let registers = g.0@.map_values(|r: RegisterConstraint| raw_register_class(r));
let views = registers.map_values(|c: Class| c@);
lemma_letter_product_members(axes, registers);
assert(axes.len() == g@.len());
assert(views.len() == g@.len());
assert forall|i: int| 0 <= i < g@.len() implies views[i] == register_class(g.0[i]@) by {
    assert(g.0[i] == g.0@[i]);
    assert(registers[i] == raw_register_class(g.0@[i]));
    assert(views[i] == registers[i]@);
    match g.0[i] {
        RegisterConstraint::Equals(_) => {}, RegisterConstraint::Differs(_) => {},
    }
}
assert forall|l: implementation::LetterView| letters_views(g, operands, universes).contains(l)
    implies l.classes.len() == g@.len() && l.registers.len() == g@.len()
        && (forall|i: int| 0 <= i < g@.len() ==> class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i])
            && l.registers[i] == register_class(g.0[i]@)) by {
    assert(letter_product(axes, registers).contains(l));
    assert(l.registers == views);
    assert forall|i: int| 0 <= i < g@.len() implies class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i])
        && l.registers[i] == register_class(g.0[i]@) by {
        assert(axes[i].contains(l.classes[i]));
        assert(axes[i] == class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]));
        assert(l.registers[i] == views[i]);
    }
}
assert forall|l: implementation::LetterView| l.classes.len() == g@.len() && l.registers.len() == g@.len()
    && (forall|i: int| 0 <= i < g@.len() ==> class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i])
        && l.registers[i] == register_class(g.0[i]@))
    implies letters_views(g, operands, universes).contains(l) by {
    assert forall|i: int| 0 <= i < g@.len() implies l.registers[i] == views[i] && axes[i].contains(l.classes[i]) by {
        assert(class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i]));
        assert(l.registers[i] == register_class(g.0[i]@));
        assert(views[i] == register_class(g.0[i]@));
    }
    assert(l.registers =~= views);
    assert forall|i: int| 0 <= i < axes.len() implies #[trigger] axes[i].contains(l.classes[i]) by {
        assert(0 <= i < g@.len());
        assert(l.registers[i] == register_class(g.0[i]@));
        assert(class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(l.classes[i]));
        assert(axes[i] == class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]));
    }
    lemma_finite_product_members(axes);
    assert(finite_product(axes).contains(l.classes));
    assert(implementation::LetterView { classes: l.classes, registers: registers.map_values(|c: Class| c@) } == l);
    assert(letter_product(axes, registers).contains(l));
}
}

pub(crate) proof fn lemma_field_realizes(g: Constraint, operands: Operands, atoms: Seq<Atom>, letter: implementation::LetterView, theta: Subst, event: EventView)
    requires operands_of(operands, atoms), g@.len() == operands.register@.len(),
        letter.classes.len() == g@.len(), letter.registers.len() == g@.len(), theta.len() == g@.len(), event.len() == g@.len(),
        forall|i: int| 0 <= i < g@.len() ==> letter.registers[i] == register_class(g.0[i]@),
        forall|i: int| 0 <= i < g@.len() ==> field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), letter.classes[i], theta[i], event[i]),
    ensures search::realizes(theta, event, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_operand_atoms(operands, atoms);
    let alpha = implementation::letter_assignment(letter, atom_set(atoms));
    assert forall|p: model::Primitive| alpha.dom().contains(p) implies alpha[p] == model::primitive_holds(theta, p, event) by {
        match p {
            model::Primitive::Eq(c, model::GTerm::Constant(v)) => {
                assert(c.0 < g@.len()); assert(codes(operands.constants[c.0 as int].view()).contains(v));
            },
            model::Primitive::Eq(c, model::GTerm::Variable(c2)) => {
                assert(c == c2); assert(c.0 < g@.len()); assert(operands.register[c.0 as int]);
            },
        }
    }
}

pub(crate) proof fn lemma_letters_realize(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes, letter: implementation::LetterView, theta: Subst)
    requires shape_wf(g, operands, universes), operands_of(operands, atoms), encoding::n_theta_ok(ndomains(universes), theta),
        inclusion::sat_by(theta, implementation::constraint_of(g@)), letters_views(g, operands, universes).contains(letter), letters_ready(g@, operands, universes),
    ensures exists|e: EventView| encoding::n_event_in(ndomains(universes), e) && search::realizes(theta, e, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_letters_members(g, operands, universes); lemma_constraint_sat(g@, theta); lemma_theta_allowed(universes, theta);
    assert(forall|i: int| 0 <= i < g@.len() ==>
        #[trigger] class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(letter.classes[i]));
    assert forall|i: int| #![trigger g.0[i]@] 0 <= i < g@.len() implies exists|v: nat|
        (domain_view(universes[i]) matches Some(vs) ==> vs.contains(v))
        && #[trigger] field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), letter.classes[i], theta[i], v) by {
assert(class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(letter.classes[i]));
let v = lemma_field_letter_sound(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i], letter.classes[i], theta[i]);
assert(field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), letter.classes[i], theta[i], v));
    }
    let event = Seq::new(g@.len(), |i: int| choose|v: nat|
        (domain_view(universes[i]) matches Some(vs) ==> vs.contains(v))
        && #[trigger] field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), letter.classes[i], theta[i], v));
    lemma_field_realizes(g, operands, atoms, letter, theta, event);
    assert(encoding::n_event_in(ndomains(universes), event));
}

pub(crate) proof fn lemma_letters_complete(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes, theta: Subst, event: EventView) -> (letter: implementation::LetterView)
    requires shape_wf(g, operands, universes), operands_of(operands, atoms), encoding::n_theta_ok(ndomains(universes), theta),
        inclusion::sat_by(theta, implementation::constraint_of(g@)), encoding::n_event_in(ndomains(universes), event), letters_ready(g@, operands, universes),
    ensures letters_views(g, operands, universes).contains(letter), search::realizes(theta, event, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_constraint_sat(g@, theta); lemma_theta_allowed(universes, theta); lemma_event_domains(universes, event);
    assert forall|i: int| #![trigger g.0[i]@] 0 <= i < g@.len() implies exists|c: Option<implementation::ClassView>|
        #[trigger] class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(c)
        && field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), c, theta[i], event[i]) by {
        lemma_field_letter_complete(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i], theta[i], event[i]);
    }
    let letter = implementation::LetterView {
        classes: Seq::new(g@.len(), |i: int| choose|c: Option<implementation::ClassView>|
            #[trigger] class_options(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), universes[i]).contains(c)
            && field_letter(g.0[i]@, operands.register[i], codes(operands.constants[i].view()), c, theta[i], event[i])),
        registers: g@.map_values(|r: implementation::RegisterView| register_class(r)),
    };
    lemma_letters_members(g, operands, universes); lemma_field_realizes(g, operands, atoms, letter, theta, event);
    letter
}

pub(crate) proof fn lemma_letters_are_realizable(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes)
    requires shape_wf(g, operands, universes), operands_of(operands, atoms),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
        letters_ready(g@, operands, universes),
    ensures forall|alpha: search::Assignment|
        letters_views(g, operands, universes).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(alpha)
        == (alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
            encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
            && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha)),
{
    let assignments = letters_views(g, operands, universes).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms)));
    assert forall|alpha: search::Assignment| assignments.contains(alpha) implies
        alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
            encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
            && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha) by {
        let l = choose|l: implementation::LetterView| letters_views(g, operands, universes).contains(l)
            && implementation::letter_assignment(l, atom_set(atoms)) == alpha;
        let theta = choose|theta: Subst| encoding::n_theta_ok(ndomains(universes), theta)
            && inclusion::sat_by(theta, implementation::constraint_of(g@));
        lemma_letters_realize(g, operands, atoms, universes, l, theta);
    }
    assert forall|alpha: search::Assignment| alpha.dom() == atom_set(atoms) && (exists|theta: Subst, event: EventView|
        encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
            && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha))
        implies assignments.contains(alpha) by {
        let theta = choose|theta: Subst| #[trigger] encoding::n_theta_ok(ndomains(universes), theta)
            && inclusion::sat_by(theta, implementation::constraint_of(g@))
            && exists|event: EventView| encoding::n_event_in(ndomains(universes), event)
                && #[trigger] search::realizes(theta, event, alpha);
        let event = choose|event: EventView| encoding::n_theta_ok(ndomains(universes), theta)
            && encoding::n_event_in(ndomains(universes), event) && inclusion::sat_by(theta, implementation::constraint_of(g@))
            && search::realizes(theta, event, alpha);
        let l = lemma_letters_complete(g, operands, atoms, universes, theta, event);
        search::lemma_realizes_unique(theta, event, atom_set(atoms), alpha, implementation::letter_assignment(l, atom_set(atoms)));
        assert(assignments.contains(alpha));
    }
}
}

verus! {
pub(crate) open spec fn letters_ready(g: implementation::ConstraintView, operands: Operands, universes: Universes) -> bool {
    g.len() == operands.register@.len() && g.len() == universes@.len()
        && forall|i: int| 0 <= i < g.len() ==> field_ready(g[i], operands.register[i], codes(operands.constants[i].view()), domain_view(universes[i]))
}

pub(crate) proof fn lemma_event_domains(universes: Universes, event: EventView)
    requires encoding::n_event_in(ndomains(universes), event),
    ensures event.len() == universes@.len(), forall|i: int| #![trigger domain_view(universes[i])] 0 <= i < universes@.len()
        ==> (domain_view(universes[i]) matches Some(vs) ==> vs.contains(event[i])),
{
    let d = ndomains(universes);
    assert(d.len() == universes@.len());
    assert forall|i: int| #![trigger domain_view(universes[i])] 0 <= i < universes@.len()
        implies (domain_view(universes[i]) matches Some(vs) ==> vs.contains(event[i])) by {
        assert(d[i] == domain_view(universes@[i]));
        assert(universes[i] == universes@[i]);
        match d[i] {
            None => {}, Some(vs) => { assert(vs.contains(event[i])); },
        }
    }
}
}

verus! {
pub(crate) open spec fn group_constraints(groups: Seq<(Constraint, Vec<Letter>)>) -> Seq<Constraint> {
    groups.map(|i: int, group: (Constraint, Vec<Letter>)| group.0)
}

pub(crate) open spec fn steps_result(g: Constraint, atoms: Seq<Atom>, universes: Universes, groups: Seq<(Constraint, Vec<Letter>)>) -> bool {
    &&& constraint_wf(g)
    &&& g@.len() == universes@.len()
    &&& atoms_wf(atoms, universes@.len())
    &&& exists|operands: Operands| operands_of(operands, atoms) && operands.register@.len() == universes@.len()
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && groups[i].0@.len() == universes@.len()
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes)
            && forall|j: int| 0 <= j < groups[i].1@.len() ==> letter_wf(groups[i].1@[j])
                && groups[i].1@[j]@.classes.len() == universes@.len()
}

pub(crate) open spec fn steps_capacity(g: Constraint, atoms: Seq<Atom>, universes: Universes) -> bool {
    forall|operands: Operands| operands_of(operands, atoms) ==> split_capacity(g, operands, universes)
        && forall|refined: Constraint| constraint_wf(refined) && split_views(g, operands, universes).contains(refined@)
            ==> letter_capacity(refined, operands, universes)
}

pub(crate) proof fn lemma_group_constraints(groups: Seq<(Constraint, Vec<Letter>)>)
    ensures forall|c: implementation::ConstraintView| #[trigger] constraint_views(group_constraints(groups)).contains(c)
        == (exists|i: int| 0 <= i < groups.len() && groups[i].0@ == c),
{
    assert forall|c: implementation::ConstraintView| constraint_views(group_constraints(groups)).contains(c)
        implies exists|i: int| 0 <= i < groups.len() && groups[i].0@ == c by {
        let value = choose|value: Constraint| group_constraints(groups).to_set().contains(value) && value@ == c;
        let i = choose|i: int| 0 <= i < groups.len() && group_constraints(groups)[i] == value;
    }
    assert forall|c: implementation::ConstraintView| (exists|i: int| 0 <= i < groups.len() && groups[i].0@ == c)
        implies constraint_views(group_constraints(groups)).contains(c) by {
        let i = choose|i: int| 0 <= i < groups.len() && groups[i].0@ == c;
        group_constraints(groups).to_set_ensures();
        assert(group_constraints(groups)[i] == groups[i].0);
        assert(group_constraints(groups).to_set().contains(groups[i].0));
    }
}
}

verus! {
pub(crate) proof fn lemma_constraint_view_at(values: Seq<Constraint>, index: int)
    requires 0 <= index < values.len(),
    ensures constraint_views(values).contains(values[index]@),
    decreases values.len(),
{
    let prior = values.drop_last();
    assert(prior.push(values.last()) =~= values);
    lemma_constraint_views_push(prior, values.last());
    if index < prior.len() { lemma_constraint_view_at(prior, index); assert(prior[index] == values[index]); }
    else { assert(values[index] == values.last()); }
}

pub(crate) proof fn lemma_refined_letters_ready(g: Constraint, operands: Operands, universes: Universes, refined: Constraint)
    requires shape_wf(g, operands, universes), split_views(g, operands, universes).contains(refined@),
    ensures letters_ready(refined@, operands, universes),
{ lemma_refined_ready(g, operands, universes, refined@); }

pub(crate) open spec fn group_cases(group: (Constraint, Vec<Letter>), atoms: Set<model::Primitive>,
    next: spec_fn(search::Assignment) -> language::Regex<model::Test>) -> Set<search::Case> {
    letter_views(group.1@).map(|l: implementation::LetterView| {
        let alpha = implementation::letter_assignment(l, atoms);
        search::Case { constraint: implementation::constraint_of(group.0@), alpha, next: next(alpha) }
    })
}

pub(crate) open spec fn implemented_cases(groups: Seq<(Constraint, Vec<Letter>)>, atoms: Set<model::Primitive>,
    next: spec_fn(search::Assignment) -> language::Regex<model::Test>) -> Set<search::Case> {
    groups.to_set().map(|group: (Constraint, Vec<Letter>)| group_cases(group, atoms, next)).flatten()
}

pub(crate) proof fn lemma_implemented_cases_members(groups: Seq<(Constraint, Vec<Letter>)>, atoms: Set<model::Primitive>,
    next: spec_fn(search::Assignment) -> language::Regex<model::Test>)
    ensures forall|c: search::Case| #[trigger] implemented_cases(groups, atoms, next).contains(c)
        == (exists|i: int, l: implementation::LetterView| 0 <= i < groups.len() && letter_views(groups[i].1@).contains(l)
            && c.constraint == implementation::constraint_of(groups[i].0@)
            && c.alpha == implementation::letter_assignment(l, atoms) && c.next == next(c.alpha)),
{
    broadcast use vstd::set::Set::lemma_flatten_contains;
    let f = |group: (Constraint, Vec<Letter>)| group_cases(group, atoms, next);
    assert forall|c: search::Case| implemented_cases(groups, atoms, next).contains(c)
        implies exists|i: int, l: implementation::LetterView| 0 <= i < groups.len() && letter_views(groups[i].1@).contains(l)
            && c.constraint == implementation::constraint_of(groups[i].0@)
            && c.alpha == implementation::letter_assignment(l, atoms) && c.next == next(c.alpha) by {
        let s = choose|s: Set<search::Case>| groups.to_set().map(f).contains(s) && s.contains(c);
        let group = choose|group: (Constraint, Vec<Letter>)| groups.to_set().contains(group) && f(group) == s;
        let i = choose|i: int| 0 <= i < groups.len() && groups[i] == group;
        let l = choose|l: implementation::LetterView| letter_views(group.1@).contains(l)
            && search::Case { constraint: implementation::constraint_of(group.0@),
                alpha: implementation::letter_assignment(l, atoms), next: next(implementation::letter_assignment(l, atoms)) } == c;
    }
    assert forall|c: search::Case| (exists|i: int, l: implementation::LetterView| 0 <= i < groups.len()
        && letter_views(groups[i].1@).contains(l) && c.constraint == implementation::constraint_of(groups[i].0@)
        && c.alpha == implementation::letter_assignment(l, atoms) && c.next == next(c.alpha))
        implies implemented_cases(groups, atoms, next).contains(c) by {
        let i = choose|i: int| #![trigger groups[i]] 0 <= i < groups.len() && exists|l: implementation::LetterView|
            letter_views(groups[i].1@).contains(l) && c.constraint == implementation::constraint_of(groups[i].0@)
            && c.alpha == implementation::letter_assignment(l, atoms) && c.next == next(c.alpha);
        let l = choose|l: implementation::LetterView| letter_views(groups[i].1@).contains(l)
            && c.constraint == implementation::constraint_of(groups[i].0@)
            && c.alpha == implementation::letter_assignment(l, atoms) && c.next == next(c.alpha);
        assert(group_cases(groups[i], atoms, next).contains(c));
        assert(groups.to_set().contains(groups[i]));
        assert(groups.to_set().map(f).contains(group_cases(groups[i], atoms, next)));
    }
}

pub(crate) proof fn lemma_steps_are_paper_steps(g: Constraint, atoms: Seq<Atom>, universes: Universes,
    groups: Seq<(Constraint, Vec<Letter>)>, state: language::Regex<model::Test>,
    next: spec_fn(search::Assignment) -> language::Regex<model::Test>)
    requires atoms_wf(atoms, universes@.len()), steps_result(g, atoms, universes, groups),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
    ensures implemented_cases(groups, atom_set(atoms), next).to_iset() == search::paper_steps(ndomains(universes),
        search::Item { constraint: implementation::constraint_of(g@), state }, atom_set(atoms),
        constraint_views(group_constraints(groups)).map(|v: implementation::ConstraintView| implementation::constraint_of(v)), next),
{
    let operands = choose|operands: Operands| operands_of(operands, atoms) && operands.register@.len() == universes@.len()
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && groups[i].0@.len() == universes@.len()
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes)
            && forall|j: int| 0 <= j < groups[i].1@.len() ==> letter_wf(groups[i].1@[j])
                && groups[i].1@[j]@.classes.len() == universes@.len();
    let cases = implemented_cases(groups, atom_set(atoms), next);
    let splits = constraint_views(group_constraints(groups)).map(|v: implementation::ConstraintView| implementation::constraint_of(v));
    let paper = search::paper_steps(ndomains(universes), search::Item { constraint: implementation::constraint_of(g@), state }, atom_set(atoms), splits, next);
    lemma_group_constraints(groups); lemma_implemented_cases_members(groups, atom_set(atoms), next);
    assert forall|c: search::Case| cases.contains(c) implies paper.contains(c) by {
        let i = choose|i: int| #![trigger groups[i]] 0 <= i < groups.len() && exists|l: implementation::LetterView| letter_views(groups[i].1@).contains(l)
            && c.constraint == implementation::constraint_of(groups[i].0@)
            && c.alpha == implementation::letter_assignment(l, atom_set(atoms)) && c.next == next(c.alpha);
        let l = choose|l: implementation::LetterView| letter_views(groups[i].1@).contains(l)
            && c.alpha == implementation::letter_assignment(l, atom_set(atoms));
        lemma_split_options_sound(g, operands, universes, groups[i].0@);
        lemma_refined_letters_ready(g, operands, universes, groups[i].0);
        lemma_letters_are_realizable(groups[i].0, operands, atoms, universes);
        assert(letters_views(groups[i].0, operands, universes)
            .map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(c.alpha));
        assert(c.constraint == implementation::constraint_of(groups[i].0@));
        lemma_constraint_view_at(group_constraints(groups), i);
        constraint_views(group_constraints(groups)).lemma_map_contains(
            |v: implementation::ConstraintView| implementation::constraint_of(v), c.constraint);
        assert(splits.contains(c.constraint));
    }
    assert forall|c: search::Case| paper.contains(c) implies cases.contains(c) by {
        let view = choose|view: implementation::ConstraintView| constraint_views(group_constraints(groups)).contains(view)
            && implementation::constraint_of(view) == c.constraint;
        let i = choose|i: int| 0 <= i < groups.len() && groups[i].0@ == view;
        lemma_split_options_sound(g, operands, universes, view);
        lemma_refined_letters_ready(g, operands, universes, groups[i].0);
        lemma_letters_are_realizable(groups[i].0, operands, atoms, universes);
        let l = choose|l: implementation::LetterView| letters_views(groups[i].0, operands, universes).contains(l)
            && implementation::letter_assignment(l, atom_set(atoms)) == c.alpha;
        assert(cases.contains(c));
    }
    assert(cases.to_iset() =~= paper);
}

pub(crate) proof fn implemented_steps_ok(g: Constraint, atoms: Seq<Atom>, universes: Universes,
    groups: Seq<(Constraint, Vec<Letter>)>, state: language::Regex<model::Test>,
    next: spec_fn(search::Assignment) -> language::Regex<model::Test>)
    requires atoms_wf(atoms, universes@.len()), steps_result(g, atoms, universes, groups),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
        search::atoms_complete(state, atom_set(atoms)),
        forall|alpha: search::Assignment| alpha.dom() == atom_set(atoms) ==> search::successor_ok(state, alpha, next(alpha)),
    ensures search::steps_ok(ndomains(universes), search::Item { constraint: implementation::constraint_of(g@), state },
        implemented_cases(groups, atom_set(atoms), next)),
{
    hide(search::steps_ok);
    hide(search::successor_ok);
    hide(search::atoms_complete);
    hide(search::paper_steps);
    hide(encoding::n_lang);
    hide(language::numeric_lang);
    hide(class_options);
    hide(register_options);
    let operands = choose|operands: Operands| operands_of(operands, atoms) && operands.register@.len() == universes@.len()
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && groups[i].0@.len() == universes@.len()
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes)
            && forall|j: int| 0 <= j < groups[i].1@.len() ==> letter_wf(groups[i].1@[j])
                && groups[i].1@[j]@.classes.len() == universes@.len();
    lemma_operand_atoms(operands, atoms); lemma_split_views_ok(g, operands, universes, atoms);
    lemma_steps_are_paper_steps(g, atoms, universes, groups, state, next);
    search::theorem_successor_cases();
    let splits = constraint_views(group_constraints(groups)).map(|v: implementation::ConstraintView| implementation::constraint_of(v));
    let item = search::Item { constraint: implementation::constraint_of(g@), state };
    let paper = search::paper_steps(ndomains(universes), item, atom_set(atoms), splits, next);
    assert(paper.finite());
    broadcast use vstd::set::lemma_set_new_from_iset;
    assert(Set::new_from_iset(paper) is Some);
    assert(Set::new_from_iset(paper).unwrap() =~= implemented_cases(groups, atom_set(atoms), next));
    assert(search::steps_ok(ndomains(universes), item, implemented_cases(groups, atom_set(atoms), next)));
}
}

verus! {
pub(crate) proof fn lemma_canonical_codes_injective(a: Seq<u32>, b: Seq<u32>)
    requires canonical(a), canonical(b), codes(a) == codes(b),
    ensures a == b,
{
    lemma_codes(a); lemma_codes(b);
    assert(a.no_duplicates()); assert(b.no_duplicates());
    a.lemma_multiset_has_no_duplicates(); b.lemma_multiset_has_no_duplicates();
    assert forall|v: u32| a.contains(v) == b.contains(v) by {
        assert(codes(a).contains(v as nat) == a.contains(v));
        assert(codes(b).contains(v as nat) == b.contains(v));
    }
    assert forall|v: u32| a.to_multiset().count(v) == b.to_multiset().count(v) by {
        vstd::seq_lib::to_multiset_contains(a, v); vstd::seq_lib::to_multiset_contains(b, v);
    }
    assert(a.to_multiset() =~= b.to_multiset());
    vstd::seq_lib::lemma_sorted_unique(a, b, |x: u32, y: u32| x <= y);
}

pub(crate) proof fn lemma_register_view_injective(a: RegisterConstraint, b: RegisterConstraint)
    requires register_wf(a), register_wf(b), a@ == b@,
    ensures register_key(a) == register_key(b),
{
    match (a, b) {
        (RegisterConstraint::Equals(v), RegisterConstraint::Equals(w)) => {},
        (RegisterConstraint::Differs(vs), RegisterConstraint::Differs(ws)) => {
            lemma_canonical_codes_injective(vs.view(), ws.view());
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_constraint_view_injective(a: Constraint, b: Constraint)
    requires constraint_wf(a), constraint_wf(b), a@ == b@,
    ensures constraint_key(a) == constraint_key(b),
{
assert(a@.len() == a.0@.len());
assert(b@.len() == b.0@.len());
assert forall|i: int| 0 <= i < a@.len() implies constraint_key(a)[i] == constraint_key(b)[i] by {
    assert(a.0[i] == a.0@[i]); assert(b.0[i] == b.0@[i]);
    assert(a@[i] == a.0@[i]@); assert(b@[i] == b.0@[i]@);
    assert(a.0[i]@ == b.0[i]@);
    lemma_register_view_injective(a.0[i], b.0[i]);
    assert(constraint_key(a)[i] == register_key(a.0@[i]));
    assert(constraint_key(b)[i] == register_key(b.0@[i]));
    }
    assert(constraint_key(a) =~= constraint_key(b));
}

pub(crate) proof fn lemma_register_key_view(a: RegisterConstraint, b: RegisterConstraint)
    requires register_key(a) == register_key(b),
    ensures a@ == b@,
{
    match (a, b) {
        (RegisterConstraint::Equals(v), RegisterConstraint::Equals(w)) => {},
        (RegisterConstraint::Differs(vs), RegisterConstraint::Differs(ws)) => {},
        _ => {},
    }
}

pub(crate) proof fn lemma_constraint_key_view(a: Constraint, b: Constraint)
    requires constraint_key(a) == constraint_key(b), ensures a@ == b@,
{
assert(constraint_key(a).len() == a.0@.len());
assert(constraint_key(b).len() == b.0@.len());
assert(a@.len() == b@.len());
assert forall|i: int| 0 <= i < a@.len() implies a@[i] == b@[i] by {
    assert(a.0[i] == a.0@[i]); assert(b.0[i] == b.0@[i]);
    assert(constraint_key(a)[i] == register_key(a.0@[i]));
    assert(constraint_key(b)[i] == register_key(b.0@[i]));
    assert(register_key(a.0[i]) == register_key(b.0[i]));
    lemma_register_key_view(a.0[i], b.0[i]);
    assert(a@[i] == a.0@[i]@); assert(b@[i] == b.0@[i]@);
}
    assert(a@ =~= b@);
}

pub(crate) proof fn lemma_constraint_literals_injective(a: implementation::ConstraintView, b: implementation::ConstraintView)
    requires a.len() == b.len(), a.len() <= history_syntax::MAX_ARITY, implementation::constraint_of(a) == implementation::constraint_of(b),
    ensures a == b,
{
    lemma_constraint_view(a); lemma_constraint_view(b);
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        let c = Component(i as u8);
        match implementation::register_of(a, c) {
            implementation::RegisterView::Equals(v) => {
                let l = inclusion::eq_literal(c, v);
                assert(implementation::constraint_of(a).contains(l));
                assert(implementation::constraint_of(b).contains(l));
            },
            implementation::RegisterView::Differs(vs) => match implementation::register_of(b, c) {
                implementation::RegisterView::Equals(v) => {
                    let l = inclusion::eq_literal(c, v);
                    assert(implementation::constraint_of(b).contains(l));
                    assert(!implementation::constraint_of(a).contains(l));
                },
                implementation::RegisterView::Differs(ws) => {
                    assert forall|v: nat| vs.contains(v) == ws.contains(v) by {
                        let l = inclusion::ne_literal(c, v);
                        assert(implementation::constraint_of(a).contains(l) == vs.contains(v));
                        assert(implementation::constraint_of(b).contains(l) == ws.contains(v));
                    }
                    assert(vs =~= ws);
                },
            },
        }
    }
    assert(a =~= b);
}

pub(crate) proof fn lemma_table_injective(table: ConstraintTable, i: int, j: int)
    requires table_wf(table), 0 <= i < table@.len(), 0 <= j < table@.len(), table@[i] == table@[j],
    ensures i == j,
{
    let reps = crate::native::representatives(table.ids);
    lemma_constraint_view_injective(table.constraints@[i], table.constraints@[j]);
    assert(constraint_key(reps[i].0) == constraint_key(reps[j].0));
}
}

verus! {
pub(crate) open spec fn split_contract(g: Constraint, operands: Operands, universes: Universes,
    result: Seq<Constraint>) -> bool {
    inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@))
        ==> forall|atoms: Seq<Atom>| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms)
            ==> inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
                search::domain_pairs(ndomains(universes), atom_set(atoms)),
                constraint_views(result).map(|v: implementation::ConstraintView| implementation::constraint_of(v)))
}

pub(crate) open spec fn letters_contract(g: Constraint, operands: Operands, universes: Universes,
    result: Seq<Letter>) -> bool {
    inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) && letters_ready(g@, operands, universes)
        ==> forall|atoms: Seq<Atom>, alpha: search::Assignment| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms) ==>
            letter_views(result).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(alpha)
                == (alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
                    encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
                    && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha))
}

pub(crate) proof fn lemma_split_contract(g: Constraint, operands: Operands, universes: Universes, result: Seq<Constraint>)
    requires shape_wf(g, operands, universes), constraint_views(result) == split_views(g, operands, universes),
    ensures split_contract(g, operands, universes, result),
{
    if inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) {
        assert forall|atoms: Seq<Atom>| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms) implies
            inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
                search::domain_pairs(ndomains(universes), atom_set(atoms)),
                constraint_views(result).map(|v: implementation::ConstraintView| implementation::constraint_of(v))) by {
            lemma_split_views_ok(g, operands, universes, atoms);
        }
    }
}

pub(crate) proof fn lemma_letters_contract(g: Constraint, operands: Operands, universes: Universes, result: Seq<Letter>)
    requires shape_wf(g, operands, universes), letter_views(result) == letters_views(g, operands, universes),
    ensures letters_contract(g, operands, universes, result),
{
    if inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) && letters_ready(g@, operands, universes) {
        assert forall|atoms: Seq<Atom>, alpha: search::Assignment| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms) implies
            letter_views(result).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(alpha)
                == (alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
                    encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
                    && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha)) by {
            lemma_letters_are_realizable(g, operands, atoms, universes);
        }
    }
}

}

verus! {
impl View for crate::constraint::RegisterChoices {
    type V = Seq<RegisterConstraint>;
    open(crate) spec fn view(&self) -> Seq<RegisterConstraint> {
        self.equals.view().map(|i: int, v: u32| RegisterConstraint::Equals(v))
            + match self.last { None => Seq::empty(), Some(r) => Seq::empty().push(r) }
    }
}

impl View for crate::constraint::ClassChoices {
    type V = Seq<Option<Class>>;
    open(crate) spec fn view(&self) -> Seq<Option<Class>> {
        (if self.infinite { Seq::empty().push(None) } else { Seq::empty() })
            + (if self.register { Seq::empty().push(Some(Class::Register)) } else { Seq::empty() })
            + self.names.view().map(|i: int, v: u32| Some(Class::Constant(v)))
            + match self.other { None => Seq::empty(), Some(v) => Seq::empty().push(Some(Class::Constant(v))) }
    }
}

pub(crate) proof fn lemma_register_choices(c: crate::constraint::RegisterChoices)
    requires c.last matches Some(r) ==> register_wf(r),
    ensures register_views(c@) == codes(c.equals.view()).map(|v: nat| implementation::RegisterView::Equals(v))
        .union(match c.last { None => Set::empty(), Some(r) => Set::empty().insert(r@) }),
        c@.len() == c.equals.view().len() + (if c.last is Some { 1nat } else { 0nat }),
        forall|i: int| 0 <= i < c@.len() ==> register_wf(c@[i]),
{
    let ids = c.equals.view().map(|i: int, v: u32| RegisterConstraint::Equals(v));
    let tail = match c.last { None => Seq::empty(), Some(r) => Seq::empty().push(r) };
    vstd::seq_lib::seq_to_set_distributes_over_add(ids, tail);
    c.equals.view().lemma_to_set_map_commutes(|v: u32| RegisterConstraint::Equals(v));
    ids.to_set().lemma_map_union_commute(tail.to_set(), |r: RegisterConstraint| r@);
    lemma_set_map_compose(c.equals.view().to_set(), |v: u32| RegisterConstraint::Equals(v), |r: RegisterConstraint| r@);
    lemma_set_map_compose(c.equals.view().to_set(), |v: u32| v as nat, |v: nat| implementation::RegisterView::Equals(v));
    assert(ids =~= c.equals.view().map_values(|v: u32| RegisterConstraint::Equals(v)));
    lemma_set_map_equal(c.equals.view().to_set(), |v: u32| (|r: RegisterConstraint| r@)(RegisterConstraint::Equals(v)),
        |v: u32| implementation::RegisterView::Equals(v as nat));
    assert(register_views(ids) =~= codes(c.equals.view()).map(|v: nat| implementation::RegisterView::Equals(v)));
    if let Some(r) = c.last { lemma_register_views_push(Seq::empty(), r); }
    else { lemma_register_views_empty(); }
    assert forall|i: int| 0 <= i < c@.len() implies register_wf(c@[i]) by {
        if i < ids.len() { assert(c@[i] is Equals); }
        else { assert(c@[i] == c.last->Some_0); }
    }
}

pub(crate) open spec fn class_choices_wf(c: crate::constraint::ClassChoices) -> bool {
    canonical(c.names.view()) && (c.other matches Some(v) ==> !c.names.view().contains(v))
        && (c.infinite ==> c.other is None)
}

pub(crate) proof fn lemma_class_choices(c: crate::constraint::ClassChoices)
    requires class_choices_wf(c),
    ensures option_views(c@) == codes(c.names.view()).map(|v: nat| Some(implementation::ClassView::Constant(v)))
        .union(if c.infinite { Set::empty().insert(None) } else { Set::empty() })
        .union(if c.register { Set::empty().insert(Some(implementation::ClassView::Register)) } else { Set::empty() })
        .union(match c.other { None => Set::empty(), Some(v) => Set::empty().insert(Some(implementation::ClassView::Constant(v as nat))) }),
        c@.len() == option_views(c@).len(),
{
    c.names.view().lemma_to_set_map_commutes(|v: u32| Some(Class::Constant(v)));
    let zero = if c.infinite { Seq::empty().push(None) } else { Seq::empty() };
    let reg = if c.register { Seq::empty().push(Some(Class::Register)) } else { Seq::empty() };
    let names = c.names.view().map(|i: int, v: u32| Some(Class::Constant(v)));
    let rest = match c.other { None => Seq::empty(), Some(v) => Seq::empty().push(Some(Class::Constant(v))) };
    vstd::seq_lib::seq_to_set_distributes_over_add(zero, reg);
    vstd::seq_lib::seq_to_set_distributes_over_add(zero + reg, names);
    vstd::seq_lib::seq_to_set_distributes_over_add(zero + reg + names, rest);
    (zero + reg).to_set().lemma_map_union_commute(names.to_set(), |v: Option<Class>| class_option(v));
    (zero + reg + names).to_set().lemma_map_union_commute(rest.to_set(), |v: Option<Class>| class_option(v));
    zero.to_set().lemma_map_union_commute(reg.to_set(), |v: Option<Class>| class_option(v));
    if c.infinite { lemma_option_views_push(Seq::empty(), None); } else { lemma_option_views_empty(); }
    if c.register { lemma_option_views_push(Seq::empty(), Some(Class::Register)); }
    if let Some(v) = c.other { lemma_option_views_push(Seq::empty(), Some(Class::Constant(v))); }
    lemma_set_map_compose(c.names.view().to_set(), |v: u32| Some(Class::Constant(v)), |v: Option<Class>| class_option(v));
    lemma_set_map_compose(c.names.view().to_set(), |v: u32| v as nat, |v: nat| Some(implementation::ClassView::Constant(v)));
    assert(names =~= c.names.view().map_values(|v: u32| Some(Class::Constant(v))));
    lemma_set_map_equal(c.names.view().to_set(), |v: u32| class_option(Some(Class::Constant(v))),
        |v: u32| Some(implementation::ClassView::Constant(v as nat)));
    assert(option_views(names) =~= codes(c.names.view()).map(|v: nat| Some(implementation::ClassView::Constant(v))));
    assert(c@.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < j < c@.len() implies c@[i] != c@[j] by {
            if i < zero.len() {} else if i < zero.len() + reg.len() {} else {
                if j < zero.len() + reg.len() + names.len() {
                    let a = i - zero.len() - reg.len(); let b = j - zero.len() - reg.len();
                    assert(c.names.view()[a] < c.names.view()[b]);
                } else {
                    let a = i - zero.len() - reg.len();
                    assert(c.names.view().contains(c.names.view()[a]));
                }
            }
        }
    }
    c@.unique_seq_to_set();
    assert(c@.to_set().injective_on(|v: Option<Class>| class_option(v))) by {
        assert forall|a: Option<Class>, b: Option<Class>| class_option(a) == class_option(b) implies a == b by {
            match (a, b) {
                (Some(Class::Constant(v)), Some(Class::Constant(w))) => {},
                (Some(Class::Register), Some(Class::Register)) => {},
                (None, None) => {}, _ => {},
            }
        }
    }
    vstd::set_lib::lemma_map_size(c@.to_set(), option_views(c@), |v: Option<Class>| class_option(v));
}
}

verus! {
pub(crate) proof fn lemma_set_map_compose<A, B, C>(values: Set<A>, first: spec_fn(A) -> B, second: spec_fn(B) -> C)
    ensures values.map(first).map(second) == values.map(|v: A| second(first(v))),
{
    assert forall|c: C| values.map(first).map(second).contains(c)
        implies values.map(|v: A| second(first(v))).contains(c) by {
        let b = choose|b: B| values.map(first).contains(b) && second(b) == c;
        let a = choose|a: A| values.contains(a) && first(a) == b;
    }
    assert forall|c: C| values.map(|v: A| second(first(v))).contains(c)
        implies values.map(first).map(second).contains(c) by {
        let a = choose|a: A| values.contains(a) && second(first(a)) == c;
        assert(values.map(first).contains(first(a)));
    }
    assert(values.map(first).map(second) =~= values.map(|v: A| second(first(v))));
}
}

verus! {
pub(crate) proof fn lemma_set_map_equal<A, B>(values: Set<A>, first: spec_fn(A) -> B, second: spec_fn(A) -> B)
    requires forall|a: A| values.contains(a) ==> first(a) == second(a),
    ensures values.map(first) == values.map(second),
{
    assert forall|b: B| values.map(first).contains(b) implies values.map(second).contains(b) by {
        let a = choose|a: A| values.contains(a) && first(a) == b;
        assert(second(a) == b);
    }
    assert forall|b: B| values.map(second).contains(b) implies values.map(first).contains(b) by {
        let a = choose|a: A| values.contains(a) && second(a) == b;
        assert(first(a) == b);
    }
    assert(values.map(first) =~= values.map(second));
}
}

verus! {

pub(crate) open spec fn dimensions_view(sizes: Seq<usize>) -> Seq<nat> {
    sizes.map_values(|n: usize| n as nat)
}

pub(crate) proof fn lemma_constraint_product_complete(axes: Seq<Seq<RegisterConstraint>>, values: Seq<Constraint>)
    requires product_done(axes, constraint_views(values), product_size(axis_sizes(axes))),
        constraint_views(values).subset_of(register_product(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)))),
        forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
    ensures constraint_views(values) == register_product(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a))),
{
    let full = register_product(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)));
    lemma_register_product_members(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)));
    assert forall|g: implementation::ConstraintView| full.contains(g) implies constraint_views(values).contains(g) by {
assert forall|i: int| #![trigger axes[i]] 0 <= i < axes.len() implies exists|p: usize| p < axes[i].len() && axes[i][p as int]@ == g[i] by {
            let r = choose|r: RegisterConstraint| axes[i].to_set().contains(r) && r@ == g[i];
            let j = choose|j: int| 0 <= j < axes[i].len() && axes[i][j] == r;
            assert(j == j as usize);
        }
        let p = Seq::new(axes.len(), |i: int| choose|p: usize| p < axes[i].len() && axes[i][p as int]@ == g[i]);
        assert(row_valid(axis_sizes(axes), p)); constraint_unique::lemma_row_bound(axis_sizes(axes), p);
        assert(choice_view(axes, p) =~= g);
    }
    assert(constraint_views(values) =~= full);
}

pub(crate) proof fn lemma_letter_product_complete(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, values: Seq<Letter>)
    requires letter_product_done(axes, registers, letter_views(values), product_size(axis_sizes(axes))),
        letter_views(values).subset_of(letter_product(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers)),
        forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
    ensures letter_views(values) == letter_product(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers),
{
    let full = letter_product(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers);
    lemma_letter_product_members(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers);
    assert forall|l: implementation::LetterView| full.contains(l) implies letter_views(values).contains(l) by {
        assert forall|i: int| #![trigger axes[i]] 0 <= i < axes.len() implies exists|p: usize| p < axes[i].len() && class_option(axes[i][p as int]) == l.classes[i] by {
            let domains = axes.map_values(|a: Seq<Option<Class>>| option_views(a));
            assert(domains[i] == option_views(axes[i]));
            assert(domains[i].contains(l.classes[i]));
            assert(option_views(axes[i]).contains(l.classes[i]));
            axes[i].to_set_ensures();
            assert(axes[i].len() <= usize::MAX);
            let r = choose|r: Option<Class>| axes[i].to_set().contains(r) && class_option(r) == l.classes[i];
            let j = choose|j: int| 0 <= j < axes[i].len() && axes[i][j] == r;
            assert(0 <= j < axes[i].len());
            assert(class_option(axes[i][j as usize as int]) == l.classes[i]);
            assert(j == j as usize);
        }
        let p = Seq::new(axes.len(), |i: int| choose|p: usize| p < axes[i].len() && class_option(axes[i][p as int]) == l.classes[i]);
        assert(row_valid(axis_sizes(axes), p)); constraint_unique::lemma_row_bound(axis_sizes(axes), p);
        assert(letter_choice_view(axes, registers, p).classes =~= l.classes);
        assert(letter_choice_view(axes, registers, p) == l);
    }
    assert(letter_views(values) =~= full);
}
}

pub(crate) mod table {
    use super::*;
    use crate::tables::Tables;
    use history_semantics::compile_verify as numeric;
    use junco_core::flat::verify as flat;
    use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTest};

    verus! {
    broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};
    impl View for Tables {
        type V = FlatPair<u64>;
        open(crate) spec fn view(&self) -> FlatPair<u64> {
            FlatPair { head: self.head,
                tests: self.tests, regexes: self.regexes, root: 0 }
        }
    }

    pub(crate) open spec fn test_dag(test: FlatTest<u64>, index: nat) -> bool {
        match test {
            FlatTest::And(children) | FlatTest::Or(children) =>
                flat::references_before(children@, index),
            _ => true,
        }
    }

    pub(crate) open spec fn dag(pair: FlatPair<u64>) -> bool {
        (forall|i: int| 0 <= i < pair.tests@.len() ==> test_dag(#[trigger] pair.tests@[i], i as nat))
        && (forall|i: int| 0 <= i < pair.regexes@.len() ==>
            flat::regex_wf(#[trigger] pair.regexes@[i], i as nat, pair.tests@.len()))
    }

    pub(crate) proof fn lemma_dag_elim(pair: FlatPair<u64>)
        requires dag(pair),
        ensures forall|i: int| 0 <= i < pair.tests@.len()
            ==> test_dag(#[trigger] pair.tests@[i], i as nat),
            forall|i: int| 0 <= i < pair.regexes@.len()
                ==> flat::regex_wf(#[trigger] pair.regexes@[i], i as nat, pair.tests@.len()),
    {}

    pub(crate) proof fn lemma_structural_dag(pair: FlatPair<u64>)
        requires flat::structural_wf(pair),
        ensures dag(pair), pair.root < pair.regexes@.len(),
    {
        reveal(flat::structural_wf);
        reveal(flat::prefix_wf);
        assert forall|i: int| 0 <= i < pair.tests@.len() implies
            test_dag(pair.tests@[i], i as nat) by {
            assert(flat::test_wf(pair.head@, pair.tests@[i], i as nat));
            reveal(flat::test_wf);
        }
    }

    pub(crate) open spec fn frame(before: FlatPair<u64>, after: FlatPair<u64>) -> bool {
        before.head@.len() == after.head@.len()
        && before.tests@.len() <= after.tests@.len()
        && before.regexes@.len() <= after.regexes@.len()
        && (forall|i: int| 0 <= i < before.tests@.len()
            ==> #[trigger] after.tests@[i] == before.tests@[i])
        && (forall|i: int| 0 <= i < before.regexes@.len()
            ==> #[trigger] after.regexes@[i] == before.regexes@[i])
    }

    pub(crate) open spec fn shifted(a: Seq<u32>, b: Seq<u32>, by: nat) -> bool {
        a.len() == b.len() && forall|i: int| 0 <= i < a.len()
            ==> b[i] as nat == a[i] as nat + by
    }

    pub(crate) open spec fn test_shift(a: FlatTest<u64>, b: FlatTest<u64>, by: nat) -> bool {
        match (a, b) {
            (FlatTest::Bool(x), FlatTest::Bool(y)) => x == y,
            (FlatTest::Atom { field: f, term: t, positive: p },
             FlatTest::Atom { field: g, term: u, positive: q }) => f == g && t == u && p == q,
            (FlatTest::And(x), FlatTest::And(y)) | (FlatTest::Or(x), FlatTest::Or(y)) =>
                shifted(x@, y@, by),
            _ => false,
        }
    }

    pub(crate) open spec fn regex_shift(a: FlatRegex, b: FlatRegex, tests: nat, regexes: nat) -> bool {
        match (a, b) {
            (FlatRegex::Empty, FlatRegex::Empty) | (FlatRegex::All, FlatRegex::All)
            | (FlatRegex::Epsilon, FlatRegex::Epsilon) => true,
            (FlatRegex::Test(x), FlatRegex::Test(y)) => y as nat == x as nat + tests,
            (FlatRegex::Star(x), FlatRegex::Star(y))
            | (FlatRegex::Complement(x), FlatRegex::Complement(y)) => y as nat == x as nat + regexes,
            (FlatRegex::Concat(x), FlatRegex::Concat(y)) | (FlatRegex::Union(x), FlatRegex::Union(y))
            | (FlatRegex::Intersect(x), FlatRegex::Intersect(y)) => shifted(x@, y@, regexes),
            _ => false,
        }
    }

    pub(crate) open spec fn tests_copied(source: FlatPair<u64>, target: FlatPair<u64>, by: nat, count: nat) -> bool {
        count <= source.tests@.len() && by + count <= target.tests@.len()
        && forall|i: int| 0 <= i < count ==>
            test_shift(source.tests@[i], target.tests@[(by + i) as int], by)
    }

    pub(crate) open spec fn regexes_copied(source: FlatPair<u64>, target: FlatPair<u64>,
        tests: nat, regexes: nat, count: nat) -> bool {
        count <= source.regexes@.len() && regexes + count <= target.regexes@.len()
        && forall|i: int| 0 <= i < count ==>
            regex_shift(source.regexes@[i], target.regexes@[(regexes + i) as int], tests, regexes)
    }

    pub(crate) proof fn lemma_test_shift_wf(a: FlatTest<u64>, b: FlatTest<u64>, index: nat, by: nat)
        requires test_dag(a, index), test_shift(a, b, by),
        ensures test_dag(b, index + by),
    {
        match (a, b) {
            (FlatTest::And(x), FlatTest::And(y)) | (FlatTest::Or(x), FlatTest::Or(y)) => {
                assert forall|i: int| 0 <= i < y@.len() implies y@[i] < index + by by {
                    assert(x@[i] < index);
                }
            },
            _ => {},
        }
    }

    pub(crate) proof fn lemma_regex_shift_wf(a: FlatRegex, b: FlatRegex,
        index: nat, tests: nat, test_base: nat, regex_base: nat)
        requires flat::regex_wf(a, index, tests), regex_shift(a, b, test_base, regex_base),
        ensures flat::regex_wf(b, index + regex_base, tests + test_base),
    {
        match (a, b) {
            (FlatRegex::Concat(x), FlatRegex::Concat(y)) | (FlatRegex::Union(x), FlatRegex::Union(y))
            | (FlatRegex::Intersect(x), FlatRegex::Intersect(y)) => {
                assert forall|i: int| 0 <= i < y@.len() implies y@[i] < index + regex_base by {
                    assert(x@[i] < index);
                }
            },
            _ => {},
        }
    }

    pub(crate) proof fn lemma_test_copy(source: FlatPair<u64>, target: FlatPair<u64>,
        by: nat, count: nat, index: nat, theta: Subst, event: EventView)
        requires dag(source), tests_copied(source, target, by, count), index < count,
        ensures numeric::source_test(source, index, theta, event)
            == numeric::source_test(target, index + by, theta, event),
        decreases index,
    {
        reveal_with_fuel(numeric::source_test, 1);
        assert(test_dag(source.tests@[index as int], index));
        assert(test_shift(source.tests@[index as int], target.tests@[(index + by) as int], by));
        match (source.tests@[index as int], target.tests@[(index + by) as int]) {
            (FlatTest::And(x), FlatTest::And(y)) | (FlatTest::Or(x), FlatTest::Or(y)) => {
                assert forall|i: int| 0 <= i < x@.len() implies
                    numeric::source_test(source, x@[i] as nat, theta, event)
                        == numeric::source_test(target, y@[i] as nat, theta, event) by {
                    assert(x@[i] < index);
                    lemma_test_copy(source, target, by, count, x@[i] as nat, theta, event);
                }
            },
            _ => {},
        }
    }

    pub(crate) proof fn lemma_regex_copy(source: FlatPair<u64>, target: FlatPair<u64>,
        tests: nat, regexes: nat, count: nat, index: nat, theta: Subst, word: Seq<EventView>)
        requires dag(source), tests_copied(source, target, tests, source.tests@.len()),
            regexes_copied(source, target, tests, regexes, count), index < count,
        ensures numeric::source_regex(source, index, theta, word)
            == numeric::source_regex(target, index + regexes, theta, word),
        decreases index,
    {
        reveal_with_fuel(numeric::source_regex, 1);
        assert(flat::regex_wf(source.regexes@[index as int], index, source.tests@.len()));
        assert(regex_shift(source.regexes@[index as int], target.regexes@[(index + regexes) as int], tests, regexes));
        match (source.regexes@[index as int], target.regexes@[(index + regexes) as int]) {
            (FlatRegex::Test(x), FlatRegex::Test(y)) => {
                if word.len() == 1 {
                    lemma_test_copy(source, target, tests, source.tests@.len(), x as nat, theta, word[0]);
                }
            },
            (FlatRegex::Union(x), FlatRegex::Union(y)) | (FlatRegex::Intersect(x), FlatRegex::Intersect(y)) => {
                assert forall|i: int| 0 <= i < x@.len() implies
                    numeric::source_regex(source, x@[i] as nat, theta, word)
                        == numeric::source_regex(target, y@[i] as nat, theta, word) by {
                    assert(x@[i] < index);
                    lemma_regex_copy(source, target, tests, regexes, count, x@[i] as nat, theta, word);
                }
            },
            (FlatRegex::Concat(x), FlatRegex::Concat(y)) => {
                assert forall|i: int, part: Seq<EventView>| 0 <= i < x@.len() implies
                    numeric::source_regex(source, x@[i] as nat, theta, part)
                        == numeric::source_regex(target, y@[i] as nat, theta, part) by {
                    assert(x@[i] < index);
                    lemma_regex_copy(source, target, tests, regexes, count, x@[i] as nat, theta, part);
                }
                if numeric::source_regex(source, index, theta, word) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == x@.len()
                        && parts.flatten() == word && forall|i: int| 0 <= i < x@.len()
                            ==> x@[i] < index && numeric::source_regex(source, x@[i] as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < y@.len() implies
                        y@[i] < index + regexes
                            && numeric::source_regex(target, y@[i] as nat, theta, parts[i]) by {}
                    assert(numeric::source_regex(target, index + regexes, theta, word));
                }
                if numeric::source_regex(target, index + regexes, theta, word) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == y@.len()
                        && parts.flatten() == word && forall|i: int| 0 <= i < y@.len()
                            ==> y@[i] < index + regexes
                                && numeric::source_regex(target, y@[i] as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < x@.len() implies
                        x@[i] < index && numeric::source_regex(source, x@[i] as nat, theta, parts[i]) by {}
                    assert(numeric::source_regex(source, index, theta, word));
                }
            },
            (FlatRegex::Star(x), FlatRegex::Star(y)) => {
                assert forall|part: Seq<EventView>| numeric::source_regex(source, x as nat, theta, part)
                    == #[trigger] numeric::source_regex(target, y as nat, theta, part) by {
                    lemma_regex_copy(source, target, tests, regexes, count, x as nat, theta, part);
                }
                if numeric::source_regex(source, index, theta, word) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == word
                        && forall|i: int| 0 <= i < parts.len()
                            ==> numeric::source_regex(source, x as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        numeric::source_regex(target, y as nat, theta, parts[i]) by {}
                    assert(numeric::source_regex(target, index + regexes, theta, word));
                }
                if numeric::source_regex(target, index + regexes, theta, word) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == word
                        && forall|i: int| 0 <= i < parts.len()
                            ==> numeric::source_regex(target, y as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        numeric::source_regex(source, x as nat, theta, parts[i]) by {}
                    assert(numeric::source_regex(source, index, theta, word));
                }
            },
            (FlatRegex::Complement(x), FlatRegex::Complement(y)) => {
                lemma_regex_copy(source, target, tests, regexes, count, x as nat, theta, word);
            },
            _ => {},
        }
    }

    pub(crate) proof fn lemma_frame_languages(before: FlatPair<u64>, after: FlatPair<u64>)
        requires dag(before), frame(before, after),
        ensures forall|index: nat, theta: Subst, word: Seq<EventView>| index < before.regexes@.len()
            ==> numeric::source_regex(before, index, theta, word)
                == numeric::source_regex(after, index, theta, word),
    {
        assert forall|i: int| 0 <= i < before.tests@.len() implies
            test_shift(before.tests@[i], after.tests@[i], 0) by {
            assert(before.tests@[i] == after.tests@[i]);
            match before.tests@[i] {
                FlatTest::And(xs) | FlatTest::Or(xs) => { assert(shifted(xs@, xs@, 0)); },
                _ => {},
            }
        }
        assert forall|i: int| 0 <= i < before.regexes@.len() implies
            regex_shift(before.regexes@[i], after.regexes@[i], 0, 0) by {
            assert(before.regexes@[i] == after.regexes@[i]);
            match before.regexes@[i] {
                FlatRegex::Concat(xs) | FlatRegex::Union(xs) | FlatRegex::Intersect(xs) => {
                    assert(shifted(xs@, xs@, 0));
                },
                _ => {},
            }
        }
        assert forall|index: nat, theta: Subst, word: Seq<EventView>| index < before.regexes@.len()
            implies numeric::source_regex(before, index, theta, word)
                == numeric::source_regex(after, index, theta, word) by {
            lemma_regex_copy(before, after, 0, 0, before.regexes@.len(), index, theta, word);
        }
    }
    }
}

verus! {
/// What the analyzer assumes about its event type: exactly R4's `event_obligations` (open so
/// external clients discharge it through R4's witnesses).
pub open spec fn analyzer_obligations<E: Event>() -> bool {
    junco_core::spec::hypotheses::event_obligations::<E>()
}
}

pub use frontend::{analyzer_state_wf, analyzer_view};

pub(crate) mod frontend {
    use super::*;
    use crate::analyzer::{Domains, PolicyAnalyzer, RuleId, StoredRule};
    use crate::spec::analyzer::{AnalyzerView, declared_sets, known_count, known_with};
    use history_syntax::spec::events::RuleView;
    use history_syntax::syntax::Rule;
    use junco_core::flat::{FlatHead, FlatPair};
    use junco_core::spec::questions::{DomainsView, in_domain};
    use junco_core::verify::{encoding as enc, flatten as fl};
    use vstd::std_specs::cmp::PartialEqSpec;

    verus! {
        broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

        pub(crate) open spec fn value_field<E: Event>(v: E::Component) -> Component {
            Component(E::coordinate_spec(v) as u8)
        }

        pub(crate) open spec fn entries<E: Event>(values: Seq<E::Component>) -> Seq<(E::Component, u64)> {
            values.map(|i: int, v: E::Component| (v, (i + 1) as u64))
        }

        pub(crate) open spec fn field_entries<E: Event>(values: Seq<E::Component>, field: Component) -> Seq<(E::Component, u64)> {
            entries::<E>(values).filter(|p: (E::Component, u64)| value_field::<E>(p.0) == field)
        }

        pub(crate) open spec fn native_entries<E: Event>(values: Seq<E::Component>, field: Component) -> Seq<(E::Component, u32)> {
            values.map(|i: int, v: E::Component| (v, (i + 1) as u32))
                .filter(|p: (E::Component, u32)| value_field::<E>(p.0) == field)
        }

        pub(crate) open spec fn constants_wf<E: Event>(c: Constants<E>) -> bool {
            &&& 1 <= arity::<E>() <= history_syntax::MAX_ARITY
            &&& c.values@.len() <= u32::MAX
            &&& c.ids@.len() == arity::<E>()
            &&& forall|j: int| 0 <= j < c.values@.len() ==> E::coordinate_spec(c.values@[j]) < arity::<E>()
            &&& forall|i: int| 0 <= i < c.ids@.len() ==> crate::native::representatives(c.ids@[i])
                == native_entries::<E>(c.values@, Component(i as u8))
            &&& forall|i: int, j: int| 0 <= i < j < c.values@.len()
                && value_field::<E>(c.values@[i]) == value_field::<E>(c.values@[j])
                ==> !c.values@[i].eq_spec(&c.values@[j])
        }

        pub(crate) open spec fn constants_frame<E: Event>(a: Constants<E>, b: Constants<E>) -> bool {
            a.values@.is_prefix_of(b.values@)
        }

        pub(crate) open spec fn stored_code<E: Event>(c: Constants<E>, v: E::Component, id: u32) -> bool {
            id > 0 && id <= c.values@.len()
                && value_field::<E>(v) == value_field::<E>(c.values@[id as int - 1])
                && v.eq_spec(&c.values@[id as int - 1])
        }

        pub(crate) proof fn lemma_native_entry_source<E: Event>(values: Seq<E::Component>, field: Component, i: int)
            requires 0 <= i < native_entries::<E>(values, field).len(),
            ensures exists|j: int| 0 <= j < values.len() && native_entries::<E>(values, field)[i] == (values[j], (j + 1) as u32),
                value_field::<E>(native_entries::<E>(values, field)[i].0) == field,
        {
            let source = values.map(|j: int, v: E::Component| (v, (j + 1) as u32));
            let pred = |p: (E::Component, u32)| value_field::<E>(p.0) == field;
            source.lemma_filter_pred(pred, i);
            source.lemma_filter_contains_rev(pred, native_entries::<E>(values, field)[i]);
            let j = choose|j: int| 0 <= j < source.len() && source[j] == native_entries::<E>(values, field)[i];
        }

        pub(crate) proof fn lemma_constant_lookup<E: Event>(c: Constants<E>, field: Component, value: E::Component, id: u32)
            requires constants_wf(c), analyzer_obligations::<E>(), field.0 < arity::<E>(), value_field::<E>(value) == field,
                exists|i: int| 0 <= i < crate::native::representatives(c.ids@[field.0 as int]).len()
                    && crate::native::representatives(c.ids@[field.0 as int])[i].1 == id
                    && value.eq_spec(&crate::native::representatives(c.ids@[field.0 as int])[i].0),
            ensures stored_code(c, value, id),
        {
            let reps = crate::native::representatives(c.ids@[field.0 as int]);
            let i = choose|i: int| 0 <= i < reps.len() && reps[i].1 == id && value.eq_spec(&reps[i].0);
            lemma_native_entry_source::<E>(c.values@, field, i);
            let j = choose|j: int| 0 <= j < c.values@.len() && reps[i] == (c.values@[j], (j + 1) as u32);
            assert(j + 1 == id);
        }

        pub(crate) proof fn lemma_constants_insert<E: Event>(before: Constants<E>, after: Constants<E>, field: Component, value: E::Component, id: u32)
            requires constants_wf(before), analyzer_obligations::<E>(), field.0 < arity::<E>(), value_field::<E>(value) == field,
                E::coordinate_spec(value) < arity::<E>(), before.values@.len() < u32::MAX,
                id as nat == before.values@.len() + 1, after.values@ == before.values@.push(value),
                after.ids@.len() == before.ids@.len(),
                crate::native::representatives(after.ids@[field.0 as int])
                    == crate::native::representatives(before.ids@[field.0 as int]).push((value, id)),
                forall|i: int| 0 <= i < before.ids@.len() && i != field.0 ==> after.ids@[i] == before.ids@[i],
                forall|i: int| 0 <= i < crate::native::representatives(before.ids@[field.0 as int]).len()
                    ==> !value.eq_spec(&crate::native::representatives(before.ids@[field.0 as int])[i].0),
            ensures constants_wf(after), constants_frame(before, after), stored_code(after, value, id),
        {
            let source = before.values@.map(|i: int, v: E::Component| (v, (i + 1) as u32));
            assert(after.values@.map(|i: int, v: E::Component| (v, (i + 1) as u32)) =~= source.push((value, id)));
            assert forall|i: int| 0 <= i < after.ids@.len() implies crate::native::representatives(after.ids@[i])
                == native_entries::<E>(after.values@, Component(i as u8)) by {
                source.lemma_filter_push((value, id), |p: (E::Component, u32)| value_field::<E>(p.0) == Component(i as u8));
            }
            assert forall|i: int, j: int| 0 <= i < j < after.values@.len()
                && value_field::<E>(after.values@[i]) == value_field::<E>(after.values@[j])
                implies !after.values@[i].eq_spec(&after.values@[j]) by {
                if j < before.values@.len() { assert(!before.values@[i].eq_spec(&before.values@[j])); }
                else {
                    source.lemma_filter_contains(|p: (E::Component, u32)| value_field::<E>(p.0) == field, i);
                    let k = choose|k: int| 0 <= k < native_entries::<E>(before.values@, field).len()
                        && native_entries::<E>(before.values@, field)[k] == source[i];
                    assert(!value.eq_spec(&before.values@[i]));
                    assert(!before.values@[i].eq_spec(&value));
                }
            }
        }

        pub(crate) proof fn lemma_field_book<E: Event>(c: Constants<E>, field: Component)
            requires field.0 < arity::<E>(),
            ensures constant_book(c)[field.0 as int] == field_entries::<E>(c.values@, field),
        {}

        pub(crate) proof fn lemma_field_entry_source<E: Event>(values: Seq<E::Component>, field: Component, i: int)
            requires 0 <= i < field_entries::<E>(values, field).len(),
            ensures exists|j: int| 0 <= j < values.len() && field_entries::<E>(values, field)[i] == (values[j], (j + 1) as u64),
                value_field::<E>(field_entries::<E>(values, field)[i].0) == field,
        {
            let pred = |p: (E::Component, u64)| value_field::<E>(p.0) == field;
            entries::<E>(values).lemma_filter_pred(pred, i);
            entries::<E>(values).lemma_filter_contains_rev(pred, field_entries::<E>(values, field)[i]);
            let j = choose|j: int| 0 <= j < entries::<E>(values).len() && entries::<E>(values)[j] == field_entries::<E>(values, field)[i];
        }

        pub(crate) proof fn lemma_constants_maps<E: Event>(c: Constants<E>)
            requires constants_wf(c), analyzer_obligations::<E>(),
            ensures enc::maps_wf(constant_book(c), fl::component_equality::<E>(), fl::component_domain::<E>()),
        {
            assert(enc::equality_laws(fl::component_equality::<E>(), fl::component_domain::<E>()));
            assert forall|f: int, i: int| 0 <= f < arity::<E>() && 0 <= i < constant_book(c)[f].len()
                implies fl::component_domain::<E>()(enc::field_at(f), constant_book(c)[f][i].0) && constant_book(c)[f][i].1 > 0 by {
                lemma_field_entry_source::<E>(c.values@, enc::field_at(f), i);
                let j = choose|j: int| 0 <= j < c.values@.len() && constant_book(c)[f][i] == (c.values@[j], (j + 1) as u64);
            }
            assert forall|f: int, i: int, k: int| 0 <= f < arity::<E>() && 0 <= i < constant_book(c)[f].len() && 0 <= k < constant_book(c)[f].len()
                implies fl::component_equality::<E>()(enc::field_at(f), constant_book(c)[f][i].0, constant_book(c)[f][k].0)
                    == (constant_book(c)[f][i].1 == constant_book(c)[f][k].1) by {
                let field = enc::field_at(f);
                lemma_field_entry_source::<E>(c.values@, field, i); lemma_field_entry_source::<E>(c.values@, field, k);
                let j = choose|j: int| 0 <= j < c.values@.len() && constant_book(c)[f][i] == (c.values@[j], (j + 1) as u64);
                let l = choose|l: int| 0 <= l < c.values@.len() && constant_book(c)[f][k] == (c.values@[l], (l + 1) as u64);
                if j < l { assert(!c.values@[j].eq_spec(&c.values@[l])); }
                if l < j { assert(!c.values@[l].eq_spec(&c.values@[j])); }
            }
        }

    proof fn lemma_field_entry_at<E: Event>(values: Seq<E::Component>, field: Component, index: int)
        requires 0 <= index < values.len(), value_field::<E>(values[index]) == field,
        ensures field_entries::<E>(values, field).contains((values[index], (index + 1) as u64)),
    {
        let source = entries::<E>(values);
        let pred = |p: (E::Component, u64)| value_field::<E>(p.0) == field;
        assert(source[index] == (values[index], (index + 1) as u64));
        source.lemma_filter_contains(pred, index);
        assert(field_entries::<E>(values, field) == source.filter(pred));
    }

    pub(crate) proof fn lemma_stored_encoded<E: Event>(c: Constants<E>, v: E::Component, id: u32)
        requires constants_wf(c), stored_code(c, v, id),
        ensures enc::encoded(constant_book(c), fl::component_equality::<E>(), value_field::<E>(v), v, id as u64),
    {
        let field = value_field::<E>(v);
        let j = id as int - 1;
        assert(0 <= j < c.values@.len());
        assert(E::coordinate_spec(c.values@[j]) < arity::<E>());
        assert(value_field::<E>(c.values@[j]) == field);
        assert(field.0 < arity::<E>());
        lemma_field_book(c, field);
        lemma_field_entry_at::<E>(c.values@, field, j);
        let entry = (c.values@[j], id as u64);
        assert(field_entries::<E>(c.values@, field).contains(entry));
        let i = choose|i: int| 0 <= i < field_entries::<E>(c.values@, field).len()
            && field_entries::<E>(c.values@, field)[i] == entry;
        assert(constant_book(c)[field.0 as int][i] == entry);
        assert(fl::component_equality::<E>()(field, v, entry.0));
        assert(enc::encoded(constant_book(c), fl::component_equality::<E>(), field, v, id as u64));
    }

        pub(crate) proof fn lemma_constants_extend<E: Event>(a: Constants<E>, b: Constants<E>)
            requires constants_wf(a), constants_wf(b), constants_frame(a, b),
            ensures enc::extends(constant_book(a), constant_book(b), fl::component_equality::<E>()),
        {
            assert forall|field: Component, v: E::Component, id: u64|
                enc::encoded(constant_book(a), fl::component_equality::<E>(), field, v, id)
                implies enc::encoded(constant_book(b), fl::component_equality::<E>(), field, v, id) by {
    let f = field.0 as int;
    assert(field.0 < arity::<E>());
    lemma_field_book(a, field); lemma_field_book(b, field);
    let i = choose|i: int| 0 <= i < constant_book(a)[f].len() && constant_book(a)[f][i].1 == id
        && fl::component_equality::<E>()(field, v, constant_book(a)[f][i].0);
    lemma_field_entry_source::<E>(a.values@, field, i);
    let j = choose|j: int| 0 <= j < a.values@.len()
        && field_entries::<E>(a.values@, field)[i] == (a.values@[j], (j + 1) as u64);
    assert(a.values@[j] == b.values@[j]);
    assert(value_field::<E>(b.values@[j]) == field);
    lemma_field_entry_at::<E>(b.values@, field, j);
    let entry = (b.values@[j], id);
    assert(field_entries::<E>(b.values@, field).contains(entry));
    let k = choose|k: int| 0 <= k < field_entries::<E>(b.values@, field).len()
        && field_entries::<E>(b.values@, field)[k] == entry;
    assert(constant_book(b)[f][k] == entry);
    assert(fl::component_equality::<E>()(field, v, constant_book(b)[f][k].0));
            }
        }

        pub(crate) open spec fn universe_id<E: Event>(c: Constants<E>, values: Seq<E::Component>, id: u32) -> bool {
            exists|j: int| 0 <= j < values.len() && stored_code(c, values[j], id)
        }

        pub(crate) open spec fn universe_value<E: Event>(c: Constants<E>, ids: Seq<u32>, value: E::Component) -> bool {
            exists|i: int| 0 <= i < ids.len() && stored_code(c, value, ids[i])
        }

        pub(crate) open spec fn universe_encoded<E: Event>(c: Constants<E>, ids: Seq<u32>, values: Seq<E::Component>) -> bool {
            &&& ids.no_duplicates()
            &&& forall|i: int| 0 <= i < ids.len() ==> #[trigger] universe_id(c, values, ids[i])
            &&& forall|j: int| 0 <= j < values.len() ==> #[trigger] universe_value(c, ids, values[j])
        }

        pub(crate) proof fn lemma_stored_frame<E: Event>(a: Constants<E>, b: Constants<E>, v: E::Component, id: u32)
            requires constants_frame(a, b), stored_code(a, v, id),
            ensures stored_code(b, v, id),
        {}

        pub(crate) proof fn lemma_universe_frame<E: Event>(a: Constants<E>, b: Constants<E>, ids: Seq<u32>, values: Seq<E::Component>)
            requires constants_frame(a, b), universe_encoded(a, ids, values),
            ensures universe_encoded(b, ids, values),
        {
            hide(stored_code);
            hide(constants_frame);
            assert forall|i: int| 0 <= i < ids.len() implies #[trigger] universe_id(b, values, ids[i]) by {
                assert(universe_id(a, values, ids[i]));
                let j = choose|j: int| 0 <= j < values.len() && stored_code(a, values[j], ids[i]);
                lemma_stored_frame(a, b, values[j], ids[i]);
            }
            assert forall|j: int| 0 <= j < values.len() implies #[trigger] universe_value(b, ids, values[j]) by {
                assert(universe_value(a, ids, values[j]));
                let i = choose|i: int| 0 <= i < ids.len() && stored_code(a, values[j], ids[i]);
                lemma_stored_frame(a, b, values[j], ids[i]);
            }
        }

        pub(crate) open spec fn option_len<T>(values: Option<Vec<T>>) -> nat {
            match values { Some(v) => v@.len(), None => 0 }
        }

        pub(crate) open spec fn selected_values<E: Event>(c: Constants<E>, u: Universe) -> Option<Set<E::Component>> {
            match u { None => None, Some(ids) => Some((*ids)@.to_set().map(|id: u32| c.values@[id as int - 1])) }
        }

        pub(crate) proof fn lemma_universe_empty<E: Event>(c: Constants<E>)
            ensures universe_encoded(c, Seq::<u32>::empty(), Seq::<E::Component>::empty()),
        {}

        pub(crate) proof fn lemma_universe_step<E: Event>(c: Constants<E>, ids: Seq<u32>, next: Seq<u32>, vs: Seq<E::Component>, v: E::Component, id: u32)
            requires universe_encoded(c, ids, vs), stored_code(c, v, id),
                next == if ids.contains(id) { ids } else { ids.push(id) },
            ensures universe_encoded(c, next, vs.push(v)),
        {
            hide(stored_code);
            if ids.contains(id) { assert(next == ids); } else { assert(next[ids.len() as int] == id); }
            assert(next.contains(id));
            assert forall|i: int, j: int| 0 <= i < j < next.len() implies next[i] != next[j] by {
                if j < ids.len() { assert(ids[i] != ids[j]); }
                else { assert(!ids.contains(id)); assert(ids[i] != id); }
            }
            assert forall|i: int| 0 <= i < next.len() implies #[trigger] universe_id(c, vs.push(v), next[i]) by {
                if i < ids.len() {
                    assert(universe_id(c, vs, ids[i]));
                    let j = choose|j: int| 0 <= j < vs.len() && stored_code(c, vs[j], ids[i]);
                    assert(stored_code(c, vs.push(v)[j], next[i]));
                } else { assert(stored_code(c, vs.push(v)[vs.len() as int], next[i])); }
            }
            assert forall|j: int| 0 <= j < vs.push(v).len() implies #[trigger] universe_value(c, next, vs.push(v)[j]) by {
                if j < vs.len() {
                    assert(universe_value(c, ids, vs[j]));
                    let i = choose|i: int| 0 <= i < ids.len() && stored_code(c, vs[j], ids[i]);
                    assert(stored_code(c, vs.push(v)[j], next[i]));
                } else {
                    assert(next.contains(id));
                    let i = choose|i: int| 0 <= i < next.len() && next[i] == id;
                    assert(stored_code(c, vs.push(v)[j], next[i]));
                }
            }
        }

        pub(crate) open spec fn selected_code_values<E: Event>(c: Constants<E>, ids: Seq<u32>) -> Set<E::Component> {
            ids.to_set().map(|id: u32| c.values@[id as int - 1])
        }

        proof fn lemma_selected_members<E: Event>(c: Constants<E>, ids: Seq<u32>)
            ensures forall|v: E::Component| #[trigger] selected_code_values(c, ids).contains(v)
                == (exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v),
        {
            let selected = ids.to_set().map(|id: u32| c.values@[id as int - 1]);
            assert forall|v: E::Component| selected.contains(v) implies exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v by {
                let id = choose|id: u32| ids.to_set().contains(id) && c.values@[id as int - 1] == v;
                let i = choose|i: int| 0 <= i < ids.len() && ids[i] == id;
                assert(c.values@[ids[i] as int - 1] == v);
            }
            assert forall|v: E::Component| (exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v) implies selected.contains(v) by {
                let i = choose|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v;
                assert(ids.to_set().contains(ids[i]));
                assert(selected.contains(c.values@[ids[i] as int - 1]));
            }
        }

        pub(crate) proof fn lemma_known_count_prefix<C>(sets: Seq<Set<C>>, count: int)
            requires 0 <= count <= sets.len(),
            ensures known_count(sets.take(count)) <= known_count(sets),
            decreases sets.len(),
        {
            if count < sets.len() {
                lemma_known_count_prefix(sets.drop_last(), count);
                assert(sets.take(count) =~= sets.drop_last().take(count));
            } else { assert(sets.take(count) =~= sets); }
        }

        /// The capacity consumed by the first `index + 1` declared sets, and what the next one is.
        pub(crate) proof fn lemma_declared_count_step<E: Event>(d: Domains<E>, index: int)
            requires 0 <= index < d.components@.len(),
            ensures known_count(declared_sets(d@).take(index + 1))
                    == known_count(declared_sets(d@).take(index)) + declared_sets(d@)[index].len(),
                known_count(declared_sets(d@).take(index + 1)) <= known_count(declared_sets(d@)),
                declared_sets(d@)[index] == match d.components@[index] {
                    None => Set::<E::Component>::empty(), Some(vs) => vs@.to_set(),
                },
        {
            let sets = declared_sets(d@);
            assert(sets.take(index + 1).drop_last() =~= sets.take(index));
            lemma_known_count_prefix(sets, index + 1);
        }

        /// Declared values are tagged with their coordinate (`domains_wf`).
        pub(crate) proof fn lemma_declared_values_tagged<E: Event>(d: Domains<E>, index: int)
            requires junco_core::spec::questions::domains_wf::<E>(d@), 0 <= index < d@.len(),
                d.components@[index] is Some,
            ensures forall|j: int| 0 <= j < d.components@[index].unwrap()@.len()
                ==> E::coordinate_spec(d.components@[index].unwrap()@[j]) == index,
        {
            broadcast use vstd::prelude::Seq::to_set_ensures;
            let vs = d.components@[index].unwrap();
            assert(d@[index] == Some(vs@.to_set()));
            assert forall|j: int| 0 <= j < vs@.len() implies E::coordinate_spec(vs@[j]) == index by {
                assert(vs@.to_set().contains(vs@[j]));
            }
        }

        /// A declared value whose `==`-equal was interned before has an `eq_spec`-equal stored
        /// constant at its field.
        proof fn lemma_seen_stored<E: Event>(c: Constants<E>, field: Component, ids: Seq<u32>, values: Seq<E::Component>, i: int)
            requires constants_wf(c), 0 <= i < values.len(), field.0 < arity::<E>(),
                E::coordinate_spec(values[i]) == field.0 as nat,
                universe_encoded(c, ids, values.take(i)), values.take(i).to_set().contains(values[i]),
            ensures exists|j: int| 0 <= j < c.values@.len() && value_field::<E>(c.values@[j]) == field
                && values[i].eq_spec(&c.values@[j]),
        {
            broadcast use vstd::prelude::Seq::to_set_ensures;
            let seen = values.take(i);
            let k = choose|k: int| 0 <= k < seen.len() && seen[k] == values[i];
            assert(universe_value(c, ids, seen[k]));
            let n = choose|n: int| 0 <= n < ids.len() && stored_code(c, seen[k], ids[n]);
            let j = ids[n] as int - 1;
            assert(value_field::<E>(values[i]) == field);
            assert(0 <= j < c.values@.len() && value_field::<E>(c.values@[j]) == field && values[i].eq_spec(&c.values@[j]));
        }

        /// A value not among the first `i` adds one to the set of distinct values.
        proof fn lemma_next_distinct<C>(values: Seq<C>, i: int)
            requires 0 <= i < values.len(), !values.take(i).to_set().contains(values[i]),
            ensures values.take(i).to_set().len() + 1 <= values.to_set().len(),
        {
            broadcast use vstd::prelude::Seq::to_set_ensures;
            let seen = values.take(i).to_set();
            let grown = seen.insert(values[i]);
            assert forall|x: C| grown.contains(x) implies values.to_set().contains(x) by {
                if x != values[i] {
                    let k = choose|k: int| 0 <= k < values.take(i).len() && values.take(i)[k] == x;
                    assert(values[k] == x);
                }
            }
            vstd::set_lib::lemma_len_subset(grown, values.to_set());
        }

        /// `try_intern` cannot run out of ids while interning a declared universe within capacity.
        pub(crate) proof fn lemma_universe_no_overflow<E: Event>(c: Constants<E>, field: Component, ids: Seq<u32>,
            values: Seq<E::Component>, i: int, base: int)
            requires constants_wf(c), 0 <= i < values.len(), field.0 < arity::<E>(),
                E::coordinate_spec(values[i]) == field.0 as nat,
                universe_encoded(c, ids, values.take(i)),
                c.values@.len() <= base + values.take(i).to_set().len(),
                base + values.to_set().len() <= u32::MAX,
                c.values@.len() == u32::MAX,
                forall|j: int| 0 <= j < c.values@.len() && value_field::<E>(c.values@[j]) == field
                    ==> !values[i].eq_spec(&c.values@[j]),
            ensures false,
        {
            if values.take(i).to_set().contains(values[i]) {
                lemma_seen_stored(c, field, ids, values, i);
            } else {
                lemma_next_distinct(values, i);
            }
        }

        /// Interning `values[i]` adds at most one constant, and none if an `==`-equal value was
        /// interned before.
        pub(crate) proof fn lemma_universe_count_step<E: Event>(before: Constants<E>, after: Constants<E>, field: Component,
            ids: Seq<u32>, values: Seq<E::Component>, i: int, base: int)
            requires constants_wf(before), constants_wf(after), analyzer_obligations::<E>(), constants_frame(before, after),
                0 <= i < values.len(), field.0 < arity::<E>(), E::coordinate_spec(values[i]) == field.0 as nat,
                universe_encoded(before, ids, values.take(i)),
                after.values@.len() <= before.values@.len() + 1,
                forall|j: int| before.values@.len() <= j < after.values@.len() ==> after.values@[j] == values[i],
                before.values@.len() <= base + values.take(i).to_set().len(),
            ensures after.values@.len() <= base + values.take(i + 1).to_set().len(),
        {
            broadcast use vstd::prelude::Seq::to_set_ensures;
            let seen = values.take(i);
            let next = values.take(i + 1);
            assert(next =~= seen + seq![values[i]]);
            Seq::lemma_to_set_insert_commutes(seen, values[i]);
            assert(next.to_set() == seen.to_set().insert(values[i]));
            if seen.to_set().contains(values[i]) {
                lemma_seen_stored(before, field, ids, values, i);
                let j = choose|j: int| 0 <= j < before.values@.len() && value_field::<E>(before.values@[j]) == field
                    && values[i].eq_spec(&before.values@[j]);
                if after.values@.len() > before.values@.len() {
                    let last = before.values@.len() as int;
                    assert(after.values@[last] == values[i]);
                    assert(after.values@[j] == before.values@[j]);
                    assert(value_field::<E>(after.values@[j]) == value_field::<E>(after.values@[last]));
                    assert(!after.values@[j].eq_spec(&after.values@[last]));
                    assert(values[i].eq_spec(&before.values@[j]) == before.values@[j].eq_spec(&values[i]));
                }
            }
        }

        /// A missed lookup at `field` means no stored constant of that field is `eq_spec`-equal.
        pub(crate) proof fn lemma_lookup_missed<E: Event>(c: Constants<E>, field: Component, value: E::Component)
            requires constants_wf(c), field.0 < arity::<E>(),
                forall|i: int| 0 <= i < crate::native::representatives(c.ids@[field.0 as int]).len()
                    ==> !value.eq_spec(&crate::native::representatives(c.ids@[field.0 as int])[i].0),
            ensures forall|j: int| 0 <= j < c.values@.len() && value_field::<E>(c.values@[j]) == field
                ==> !value.eq_spec(&c.values@[j]),
        {
            let reps = crate::native::representatives(c.ids@[field.0 as int]);
            assert(reps == native_entries::<E>(c.values@, field));
            let source = c.values@.map(|i: int, v: E::Component| (v, (i + 1) as u32));
            let pred = |p: (E::Component, u32)| value_field::<E>(p.0) == field;
            assert forall|j: int| 0 <= j < c.values@.len() && value_field::<E>(c.values@[j]) == field
                implies !value.eq_spec(&c.values@[j]) by {
                source.lemma_filter_contains(pred, j);
                let k = choose|k: int| 0 <= k < reps.len() && reps[k] == source[j];
                assert(reps[k].0 == c.values@[j]);
            }
        }

        /// R6 `ids_of`, under the name the internal lemmas use.
        pub open(crate) spec fn rule_ids(ids: Seq<RuleId>) -> Seq<nat> {
            crate::spec::analyzer::ids_of(ids)
        }

        pub open(crate) spec fn valid_ids<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>) -> bool {
            forall|i: int| 0 <= i < ids.len() ==> ids[i].0 < a.rules@.len()
        }

        impl View for RuleId {
            type V = nat;
            open(crate) spec fn view(&self) -> nat { self.0 as nat }
        }

        pub(crate) open spec fn stored_rule_wf<E: Event>(c: Constants<E>, us: Universes, r: StoredRule<E>) -> bool {
            &&& fl::flattened(r.original@, r.flat@)
            &&& enc::constants_in_domain(r.flat@.source, fl::component_domain::<E>())
            &&& enc::lowering(r.flat@.source, r.numeric, constant_book(c), fl::component_equality::<E>())
            &&& r.mode == r.original@.mode
            &&& junco_core::flat::verify::structural_wf(r.numeric)
            &&& r.numeric.head@.len() == arity::<E>()
            &&& r.constants@.len() == arity::<E>()
            &&& numeric_head_wf(r.numeric.head@)
            &&& head_view(r.constants@) == pins(r.numeric.head@)
            &&& super::verdict::source_codes_wf(c, r.numeric)
            &&& super::verdict::head_codes_wf(c, r.numeric.head@)
            &&& match r.constraint {
                Some(g) => constraint_wf(g) && super::verdict::constraint_codes_wf(c, g@)
                    && (forall|k: int| 0 <= k < arity::<E>() ==> #[trigger] g@[k] == match r.constants@[k] {
                        Some(v) => implementation::RegisterView::Equals(v as nat),
                        None => implementation::RegisterView::Differs(Set::empty()),
                    })
                    && implementation::constraint_of(g@) == inclusion::head_constraint(pins(r.numeric.head@))
                    && inclusion::satisfiable(ndomains(us), implementation::constraint_of(g@)),
                None => !inclusion::satisfiable(ndomains(us), inclusion::head_constraint(pins(r.numeric.head@))),
            }
        }

        pub(crate) proof fn lemma_store_extends<E: Event>(before: Constants<E>, after: Constants<E>,
            us: Universes, rules: Seq<StoredRule<E>>)
            requires constants_wf(before), constants_wf(after), analyzer_obligations::<E>(),
                enc::extends(constant_book(before), constant_book(after), fl::component_equality::<E>()),
                forall|i: int| 0 <= i < rules.len() ==> stored_rule_wf(before, us, rules[i]),
            ensures forall|i: int| 0 <= i < rules.len() ==> stored_rule_wf(after, us, rules[i]),
        {
            assert forall|i: int| 0 <= i < rules.len() implies stored_rule_wf(after, us, rules[i]) by {
                let r = rules[i];
                enc::lemma_lowering_extends(r.flat@.source, r.numeric, constant_book(before),
                    constant_book(after), fl::component_equality::<E>());
                super::verdict::lemma_lowered_payload(after, r.flat@.source, r.numeric);
                if let Some(g) = r.constraint {
                    assert forall|field: Component, v: nat| field.0 < g@.len()
                        && register_codes(implementation::register_of(g@, field)).contains(v)
                        implies super::reconstruction::code_field(after, field, v) by {
                        let value = before.values@[v as int - 1];
                        lemma_stored_encoded(before, value, v as u32);
                        super::verdict::lemma_encoded_payload(after, field, value, v as u64);
                    }
                }
            }
        }

        pub(crate) open spec fn pins(head: Seq<FlatHead<u64>>) -> encoding::NHead {
            head.map_values(|h: FlatHead<u64>| encoding::head_code(h))
        }

        pub(crate) open spec fn numeric_head_wf(head: Seq<FlatHead<u64>>) -> bool {
            1 <= head.len() <= history_syntax::MAX_ARITY
                && forall|i: int| #![trigger head[i]] 0 <= i < head.len() ==> match head[i] { FlatHead::Constant(v) => v <= u32::MAX, _ => true }
        }

        pub(crate) proof fn lemma_lowered_head_bound<E: Event>(c: Constants<E>, source: FlatPair<E::Component>, target: FlatPair<u64>)
            requires constants_wf(c), 1 <= source.head@.len() <= history_syntax::MAX_ARITY,
                enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
            ensures numeric_head_wf(target.head@),
        {
            assert forall|i: int| 0 <= i < target.head@.len() implies match #[trigger] target.head@[i] { FlatHead::Constant(v) => v <= u32::MAX, _ => true } by {
                if let FlatHead::Constant(id) = target.head@[i] {
                    match source.head@[i] {
                        FlatHead::Constant(value) => {
                            let j = choose|j: int| 0 <= j < constant_book(c)[i].len() && constant_book(c)[i][j].1 == id
                                && fl::component_equality::<E>()(enc::field_at(i), value, constant_book(c)[i][j].0);
                            lemma_field_entry_source::<E>(c.values@, enc::field_at(i), j);
                        },
                        _ => {},
                    }
                }
            }
        }

        pub(crate) open spec fn encoding_head_code(head: FlatHead<u64>) -> Option<nat> { encoding::head_code(head) }

        pub(crate) open spec fn declared_universe<E: Event>(c: Constants<E>, u: Universe, vs: Option<Vec<E::Component>>) -> bool {
            match (u, vs) { (None, None) => true, (Some(ids), Some(values)) => universe_encoded(c, (*ids)@, values@), _ => false }
        }

        pub(crate) open spec fn declared_domains_encoded<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>) -> bool {
            junco_core::spec::questions::domains_wf::<E>(d@) && a.universes@.len() == arity::<E>()
                && forall|i: int| 0 <= i < arity::<E>() ==> declared_universe(a.constants, a.universes[i], d.components@[i])
        }

        pub(crate) open spec fn component_of<E: Event>(values: Set<E::Component>, coordinate: int) -> Set<E::Component> {
            values.filter(|value: E::Component| E::coordinate_spec(value) == coordinate)
        }

        impl<E: Event> View for Domains<E> {
            type V = DomainsView<E::Component>;
            open(crate) spec fn view(&self) -> Self::V {
                self.components@.map_values(|values: Option<Vec<E::Component>>| match values { None => None, Some(vs) => Some(vs@.to_set()) })
            }
        }

        /// The reviewer's view of an analyzer (R6 `AnalyzerView`): the ghost declared domains and
        /// known constants (set by the contracts), and the rule views by index.
        pub open(crate) spec fn analyzer_view<E: Event>(a: PolicyAnalyzer<E>) -> AnalyzerView<E::Component> {
            AnalyzerView {
                domains: a.declared@,
                rules: a.rules@.map_values(|r: StoredRule<E>| encoding::rule_view(r.original@)),
                known: a.known@,
            }
        }

        impl<E: Event> View for PolicyAnalyzer<E> {
            type V = AnalyzerView<E::Component>;
            open(crate) spec fn view(&self) -> Self::V { analyzer_view(*self) }
        }

        /// What the bridge proofs read of the view: arity-many domains and books, and declared
        /// domains that agree with the stored universes up to `eq_spec`.
        pub(crate) open spec fn view_links<E: Event>(a: PolicyAnalyzer<E>) -> bool {
            &&& a@.domains.len() == arity::<E>() && a@.known.len() == arity::<E>()
            &&& forall|k: int, x: E::Component| 0 <= k < arity::<E>()
                ==> #[trigger] in_domain(a@.domains[k], x) == in_domain(selected_values(a.constants, a.universes[k]), x)
        }

        /// Every interned constant is known at its coordinate up to `eq_spec` (R6 clause 3): the
        /// counterexample bridges (`every_instance`, `minimal_in_case`, the refutation clauses) rest
        /// on it. Part of `analyzer_state_wf`; `new` establishes it from the declared values and
        /// `add_rule`/`tail_included` keep it because a lowering interns only the input's constants.
        pub(crate) open spec fn stored_known<E: Event>(a: PolicyAnalyzer<E>) -> bool {
            forall|k: int, j: int| #![trigger a@.known[k], a.constants.values@[j]]
                0 <= k < arity::<E>() && 0 <= j < a.constants.values@.len() && E::coordinate_spec(a.constants.values@[j]) == k
                ==> exists|w: E::Component| #[trigger] a@.known[k].contains(w) && a.constants.values@[j].eq_spec(&w)
        }

        /// Some member of `known[k]` is `eq_spec`-equal to `v`.
        pub(crate) open spec fn known_at<C: PartialEq>(known: Seq<Set<C>>, k: int, v: C) -> bool {
            exists|w: C| #[trigger] known[k].contains(w) && v.eq_spec(&w)
        }

        /// `stored_known` in the one-variable form the prover can establish (the trigger
        /// `values[j]` is ground in a goal, `known[k]` is not): every value is known at its own
        /// coordinate.
        pub(crate) open spec fn values_known<E: Event>(known: Seq<Set<E::Component>>, values: Seq<E::Component>) -> bool {
            forall|j: int| #![trigger values[j]] 0 <= j < values.len()
                ==> known_at(known, E::coordinate_spec(values[j]) as int, values[j])
        }

        pub(crate) proof fn lemma_stored_known_from_values<E: Event>(a: PolicyAnalyzer<E>)
            requires values_known::<E>(a.known@, a.constants.values@),
            ensures stored_known(a),
        {
            assert forall|j: int| #![trigger a.constants.values@[j]] 0 <= j < a.constants.values@.len()
                implies exists|w: E::Component| #[trigger] a@.known[E::coordinate_spec(a.constants.values@[j]) as int].contains(w)
                    && a.constants.values@[j].eq_spec(&w) by {
                let k = E::coordinate_spec(a.constants.values@[j]) as int;
                assert(known_at(a.known@, k, a.constants.values@[j]));
                let w = choose|w: E::Component| #[trigger] a.known@[k].contains(w) && a.constants.values@[j].eq_spec(&w);
                assert(a@.known[k].contains(w));
            }
        }

        /// `stored_known` instantiated at one stored value.
        pub(crate) proof fn lemma_stored_known_at<E: Event>(a: PolicyAnalyzer<E>, j: int)
            requires stored_known(a), constants_wf(a.constants), 0 <= j < a.constants.values@.len(),
            ensures exists|w: E::Component| #[trigger] a@.known[E::coordinate_spec(a.constants.values@[j]) as int].contains(w)
                && a.constants.values@[j].eq_spec(&w),
        {
            let k = E::coordinate_spec(a.constants.values@[j]) as int;
            assert(0 <= k < arity::<E>());
            let w = choose|w: E::Component| #[trigger] a@.known[k].contains(w) && a.constants.values@[j].eq_spec(&w);
            assert(a@.known[k].contains(w));
        }

        /// `stored_known` reads only `known` and the constants.
        pub(crate) proof fn lemma_stored_known_frame<E: Event>(before: PolicyAnalyzer<E>, after: PolicyAnalyzer<E>)
            requires stored_known(before), constants_wf(before.constants),
                after.known == before.known, after.constants == before.constants,
            ensures stored_known(after),
        {
            assert forall|j: int| #![trigger after.constants.values@[j]] 0 <= j < after.constants.values@.len()
                implies exists|w: E::Component| #[trigger] after@.known[E::coordinate_spec(after.constants.values@[j]) as int].contains(w)
                    && after.constants.values@[j].eq_spec(&w) by {
                lemma_stored_known_at(before, j);
                let w = choose|w: E::Component| #[trigger] before@.known[E::coordinate_spec(before.constants.values@[j]) as int].contains(w)
                    && before.constants.values@[j].eq_spec(&w);
                assert(after@.known[E::coordinate_spec(after.constants.values@[j]) as int].contains(w));
            }
        }

        /// Values interned from a declared slice at `index` stay known.
        pub(crate) proof fn lemma_values_known_extend<E: Event>(known: Seq<Set<E::Component>>,
            before: Seq<E::Component>, after: Seq<E::Component>, index: int)
            requires analyzer_obligations::<E>(), values_known::<E>(known, before), before.is_prefix_of(after),
                forall|j: int| before.len() <= j < after.len()
                    ==> E::coordinate_spec(#[trigger] after[j]) == index && known[index].contains(after[j]),
            ensures values_known::<E>(known, after),
        {
            assert forall|j: int| #![trigger after[j]] 0 <= j < after.len()
                implies known_at(known, E::coordinate_spec(after[j]) as int, after[j]) by {
                if j < before.len() {
                    assert(after[j] == before[j]);
                    assert(known_at(known, E::coordinate_spec(before[j]) as int, before[j]));
                } else {
                    let w = after[j];
                    let k = E::coordinate_spec(w) as int;
                    assert(known[k].contains(w));
                    assert(w.eq_spec(&w)) by { assert(junco_core::spec::hypotheses::eq_equivalence::<E::Component>()); }
                    assert(known_at(known, k, w));
                }
            }
        }

        /// Growing `known` pointwise keeps every stored value known.
        pub(crate) proof fn lemma_stored_known_grows<E: Event>(before: PolicyAnalyzer<E>, after: PolicyAnalyzer<E>,
            added: Seq<Set<E::Component>>)
            requires stored_known(before), constants_wf(before.constants), after.constants == before.constants,
                before.known@.len() == arity::<E>(),
                after.known@ == known_with(before.known@, added),
            ensures stored_known(after),
        {
            assert forall|j: int| #![trigger after.constants.values@[j]] 0 <= j < after.constants.values@.len()
                implies exists|w: E::Component| #[trigger] after@.known[E::coordinate_spec(after.constants.values@[j]) as int].contains(w)
                    && after.constants.values@[j].eq_spec(&w) by {
                let k = E::coordinate_spec(after.constants.values@[j]) as int;
                lemma_stored_known_at(before, j);
                let w = choose|w: E::Component| #[trigger] before@.known[k].contains(w)
                    && before.constants.values@[j].eq_spec(&w);
                assert(0 <= k < arity::<E>());
                assert(after@.known[k] == before.known@[k].union(added[k]));
                assert(after@.known[k].contains(w));
            }
        }

        /// Interning `value` at `field` adds nothing else to the book.
        pub(crate) proof fn lemma_constants_grow<E: Event>(before: Constants<E>, after: Constants<E>,
            field: Component, value: E::Component)
            requires after.values@ == before.values@ || after.values@ == before.values@.push(value),
                value_field::<E>(value) == field,
            ensures enc::grows_by(constant_book(before), constant_book(after), enc::only_value(field, value)),
        {
            let a = constant_book(after);
            let b = constant_book(before);
            assert forall|f: int, i: int| #![trigger a[f][i]] 0 <= f < a.len() && 0 <= i < a[f].len()
                implies (exists|j: int| 0 <= j < b[f].len() && (#[trigger] b[f][j]).0 == a[f][i].0)
                    || enc::only_value(field, value)(enc::field_at(f), a[f][i].0) by {
                let component = Component(f as u8);
                assert(a[f] == field_entries::<E>(after.values@, component));
                assert(b[f] == field_entries::<E>(before.values@, component));
                lemma_field_entry_source::<E>(after.values@, component, i);
                let j = choose|j: int| 0 <= j < after.values@.len() && a[f][i] == (after.values@[j], (j + 1) as u64);
                if j < before.values@.len() {
                    assert(after.values@[j] == before.values@[j]);
                    lemma_field_entry_at::<E>(before.values@, component, j);
                    let k = choose|k: int| 0 <= k < b[f].len() && b[f][k] == (before.values@[j], (j + 1) as u64);
                    assert(b[f][k].0 == a[f][i].0);
                } else {
                    assert(after.values@[j] == value);
                    assert(component == field);
                }
            }
        }

        /// The values a book gained are old values or ones `added` admits at their coordinate.
        pub(crate) proof fn lemma_values_grow<E: Event>(before: Constants<E>, after: Constants<E>,
            added: spec_fn(Component, E::Component) -> bool)
            requires constants_wf(after), constants_frame(before, after),
                enc::grows_by(constant_book(before), constant_book(after), added),
            ensures forall|j: int| before.values@.len() <= j < after.values@.len()
                ==> (exists|k: int| 0 <= k < before.values@.len() && before.values@[k] == #[trigger] after.values@[j])
                    || added(value_field::<E>(after.values@[j]), after.values@[j]),
        {
            let a = constant_book(after);
            let b = constant_book(before);
            assert forall|j: int| before.values@.len() <= j < after.values@.len()
                implies (exists|k: int| 0 <= k < before.values@.len() && before.values@[k] == #[trigger] after.values@[j])
                    || added(value_field::<E>(after.values@[j]), after.values@[j]) by {
                let v = after.values@[j];
                let f = E::coordinate_spec(v) as int;
                let component = Component(f as u8);
                assert(component == value_field::<E>(v) && component == enc::field_at(f));
                assert(a[f] == field_entries::<E>(after.values@, component));
                assert(b[f] == field_entries::<E>(before.values@, component));
                lemma_field_entry_at::<E>(after.values@, component, j);
                let i = choose|i: int| 0 <= i < a[f].len() && a[f][i] == (v, (j + 1) as u64);
                if exists|k: int| 0 <= k < b[f].len() && (#[trigger] b[f][k]).0 == a[f][i].0 {
                    let k = choose|k: int| 0 <= k < b[f].len() && (#[trigger] b[f][k]).0 == a[f][i].0;
                    lemma_field_entry_source::<E>(before.values@, component, k);
                    let l = choose|l: int| 0 <= l < before.values@.len() && b[f][k] == (before.values@[l], (l + 1) as u64);
                    assert(before.values@[l] == v);
                }
            }
        }

        /// Interning only constants that `known` already holds keeps every stored value known.
        pub(crate) proof fn lemma_stored_known_interned<E: Event>(before: PolicyAnalyzer<E>, after: PolicyAnalyzer<E>,
            added: spec_fn(Component, E::Component) -> bool)
            requires stored_known(before), analyzer_obligations::<E>(), constants_wf(before.constants),
                constants_wf(after.constants), constants_frame(before.constants, after.constants),
                after.known == before.known,
                enc::grows_by(constant_book(before.constants), constant_book(after.constants), added),
                forall|v: E::Component| #[trigger] added(value_field::<E>(v), v) && E::coordinate_spec(v) < arity::<E>()
                    ==> before@.known[E::coordinate_spec(v) as int].contains(v),
            ensures stored_known(after),
        {
            assert(junco_core::spec::hypotheses::eq_equivalence::<E::Component>());
            assert(after@.known == before@.known);
            lemma_values_grow(before.constants, after.constants, added);
            assert forall|j: int| #![trigger after.constants.values@[j]] 0 <= j < after.constants.values@.len()
                implies exists|w: E::Component| #[trigger] after@.known[E::coordinate_spec(after.constants.values@[j]) as int].contains(w)
                    && after.constants.values@[j].eq_spec(&w) by {
                let v = after.constants.values@[j];
                let k = E::coordinate_spec(v) as int;
                if j < before.constants.values@.len() {
                    assert(v == before.constants.values@[j]);
                    lemma_stored_known_at(before, j);
                    let w = choose|w: E::Component| #[trigger] before@.known[k].contains(w)
                        && before.constants.values@[j].eq_spec(&w);
                    assert(after@.known[k].contains(w) && v.eq_spec(&w));
                } else if exists|l: int| 0 <= l < before.constants.values@.len() && before.constants.values@[l] == v {
                    let l = choose|l: int| 0 <= l < before.constants.values@.len() && before.constants.values@[l] == v;
                    lemma_stored_known_at(before, l);
                    let w = choose|w: E::Component| #[trigger] before@.known[k].contains(w)
                        && before.constants.values@[l].eq_spec(&w);
                    assert(after@.known[k].contains(w) && v.eq_spec(&w));
                } else {
                    assert(added(value_field::<E>(v), v));
                    assert(after@.known[k].contains(v) && v.eq_spec(&v));
                }
            }
        }

        /// Lowering a rule interns only its constants, which `known` holds after the contract's
        /// `known_with` step: every stored value stays known.
        pub(crate) proof fn lemma_stored_known_lowered<E: Event>(before: PolicyAnalyzer<E>, after: PolicyAnalyzer<E>,
            rule: Rule<E>, flat: junco_core::flat::FlatRule<E::Component>)
            requires analyzer_state_wf(before), analyzer_obligations::<E>(), fl::flattened(rule, flat),
                constants_wf(after.constants), constants_frame(before.constants, after.constants),
                after.known == before.known,
                enc::grows_by(constant_book(before.constants), constant_book(after.constants), enc::source_constants(flat.source)),
                forall|k: int| 0 <= k < arity::<E>()
                    ==> junco_core::spec::questions::rule_constants(rule@)[k].subset_of(#[trigger] before.known@[k]),
            ensures stored_known(after),
        {
            fl::lemma_flattened_constants(rule, flat);
            assert forall|v: E::Component| #[trigger] enc::source_constants(flat.source)(value_field::<E>(v), v)
                && E::coordinate_spec(v) < arity::<E>()
                implies before@.known[E::coordinate_spec(v) as int].contains(v) by {
                let k = E::coordinate_spec(v) as int;
                assert(enc::source_constant(flat.source, value_field::<E>(v), v));
                assert(value_field::<E>(v).0 as int == k);
                assert(junco_core::spec::questions::rule_constants(rule@)[k].contains(v));
            }
            lemma_stored_known_interned(before, after, enc::source_constants(flat.source));
        }

        /// Interning constants keeps the view links: the ghost fields and the universes are unchanged.
        pub(crate) proof fn lemma_view_links_frame<E: Event>(before: PolicyAnalyzer<E>, after: PolicyAnalyzer<E>)
            requires view_links(before),
                constants_frame(before.constants, after.constants), universes_wf(before.constants, before.universes),
                after.universes == before.universes, after.declared == before.declared, after.known == before.known,
            ensures view_links(after),
        {
            lemma_universes_frame(before.constants, after.constants, before.universes);
        }

        pub(crate) open spec fn universes_wf<E: Event>(c: Constants<E>, us: Universes) -> bool {
    us@.len() == arity::<E>() && forall|f: int| #![trigger us[f]] 0 <= f < us@.len() ==> match us[f] {
        None => true, Some(ids) => (*ids)@.no_duplicates() && forall|j: int| #![trigger (*ids)@[j]] 0 <= j < (*ids)@.len()
                    ==> 0 < (*ids)@[j] <= c.values@.len() && E::coordinate_spec(c.values@[(*ids)@[j] as int - 1]) == f,
            }
        }

        /// Constant books, declared coordinate domains and stored rules remain well formed across
        /// queries, and the ghost view stays linked to the interned universes.
        pub(crate) open spec fn analyzer_books_wf<E: Event>(a: PolicyAnalyzer<E>) -> bool {
            constants_wf(a.constants) && universes_wf(a.constants, a.universes)
                && (forall|i: int| 0 <= i < a.rules@.len() ==> stored_rule_wf(a.constants, a.universes, a.rules@[i]))
                && domains_linked(a)
        }

        /// `analyzer_books_wf` plus clause 3: every interned constant is known (`stored_known`).
        pub open(crate) spec fn analyzer_state_wf<E: Event>(a: PolicyAnalyzer<E>) -> bool {
            analyzer_books_wf(a) && stored_known(a)
        }

        pub(crate) proof fn lemma_universes_frame<E: Event>(a: Constants<E>, b: Constants<E>, us: Universes)
            requires constants_frame(a, b), universes_wf(a, us),
            ensures universes_wf(b, us), forall|i: int| 0 <= i < us@.len() ==> selected_values(a, us[i]) == selected_values(b, us[i]),
        {
            assert forall|i: int| 0 <= i < us@.len() implies selected_values(a, us[i]) == selected_values(b, us[i]) by {
                if let Some(ids) = us[i] {
                    super::lemma_set_map_equal((*ids)@.to_set(), |id: u32| a.values@[id as int - 1], |id: u32| b.values@[id as int - 1]);
                }
            }
        }

        /// `domains_linked` gives the bridge proofs' `view_links` (the view reads the same ghost fields).
        pub(crate) proof fn lemma_view_links<E: Event>(a: PolicyAnalyzer<E>)
            requires domains_linked(a),
            ensures view_links(a),
        {
        }
        pub(crate) proof fn lemma_declared_frame<E: Event>(a: Constants<E>, b: Constants<E>, u: Universe, vs: Option<Vec<E::Component>>)
            requires constants_frame(a, b), declared_universe(a, u, vs),
            ensures declared_universe(b, u, vs),
        {
            if let (Some(ids), Some(values)) = (u, vs) { lemma_universe_frame(a, b, (*ids)@, values@); }
        }

        pub(crate) proof fn lemma_declared_wf<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>)
            requires constants_wf(a.constants), declared_domains_encoded(a, d),
            ensures universes_wf(a.constants, a.universes),
        {
            assert forall|f: int| 0 <= f < a.universes@.len() implies match #[trigger] a.universes[f] {
                None => true, Some(ids) => (*ids)@.no_duplicates() && forall|j: int| 0 <= j < (*ids)@.len()
                    ==> 0 < (*ids)@[j] <= a.constants.values@.len() && E::coordinate_spec(a.constants.values@[(*ids)@[j] as int - 1]) == f,
            } by {
    assert(0 <= f < arity::<E>());
    assert(declared_universe(a.constants, a.universes[f], d.components@[f]));
    if d.components@[f] is Some { lemma_declared_values_tagged(d, f); }
    assert(match d.components@[f] {
        None => true,
        Some(values) => forall|k: int| 0 <= k < values@.len() ==> E::coordinate_spec(values@[k]) == f,
    });
    if let (Some(ids), Some(vs)) = (a.universes[f], d.components@[f]) {
        assert(universe_encoded(a.constants, (*ids)@, vs@));
        assert forall|j: int| #![trigger (*ids)@[j]] 0 <= j < (*ids)@.len() implies 0 < (*ids)@[j] <= a.constants.values@.len()
            && E::coordinate_spec(a.constants.values@[(*ids)@[j] as int - 1]) == f by {
            assert(universe_id(a.constants, vs@, (*ids)@[j]));
            let k = choose|k: int| 0 <= k < vs@.len() && stored_code(a.constants, vs@[k], (*ids)@[j]);
            assert(E::coordinate_spec(vs@[k]) == f);
            let position = (*ids)@[j] as int - 1;
            assert(0 <= position < a.constants.values@.len());
            assert(E::coordinate_spec(a.constants.values@[position]) < arity::<E>());
            assert(value_field::<E>(a.constants.values@[position]) == value_field::<E>(vs@[k]));
            assert(E::coordinate_spec(a.constants.values@[position]) as u8 == f as u8);
            assert(E::coordinate_spec(a.constants.values@[position]) == f);
                    }
                }
            }
        }

        pub(crate) proof fn lemma_empty_constants<E: Event>(c: Constants<E>)
            requires 1 <= arity::<E>() <= history_syntax::MAX_ARITY,
                c.values@.len() == 0, c.ids@.len() == arity::<E>(),
                forall|i: int| 0 <= i < c.ids@.len() ==> crate::native::representatives(c.ids@[i]).len() == 0,
            ensures constants_wf(c),
        {
            assert forall|i: int| 0 <= i < c.ids@.len() implies crate::native::representatives(c.ids@[i]) == native_entries::<E>(c.values@, Component(i as u8)) by {
                assert(c.values@ =~= Seq::<E::Component>::empty());
                reveal(Seq::filter);
                assert(crate::native::representatives(c.ids@[i]) =~= Seq::<(E::Component,u32)>::empty());
            }
        }

        pub(crate) open spec fn book_entries_count<C>(book: Seq<Seq<(C, u64)>>) -> nat
            decreases book.len(),
        {
            if book.len() == 0 { 0 } else { book_entries_count(book.drop_last()) + book.last().len() }
        }

        proof fn lemma_book_push<E: Event>(values: Seq<E::Component>, value: E::Component, n: nat)
            requires n <= history_syntax::MAX_ARITY,
            ensures book_entries_count(Seq::new(n, |i: int| field_entries::<E>(values.push(value), Component(i as u8))))
                == book_entries_count(Seq::new(n, |i: int| field_entries::<E>(values, Component(i as u8))))
                    + if value_field::<E>(value).0 < n { 1nat } else { 0nat },
            decreases n,
        {
            if n > 0 {
                lemma_book_push::<E>(values, value, (n - 1) as nat);
                let entry = (value, (values.len() + 1) as u64);
                assert(entries::<E>(values.push(value)) =~= entries::<E>(values).push(entry));
                entries::<E>(values).lemma_filter_len_push(|p: (E::Component, u64)| value_field::<E>(p.0) == Component((n - 1) as u8), entry);
                assert(Seq::new(n, |i: int| field_entries::<E>(values, Component(i as u8))).drop_last()
                    =~= Seq::new((n - 1) as nat, |i: int| field_entries::<E>(values, Component(i as u8))));
                assert(Seq::new(n, |i: int| field_entries::<E>(values.push(value), Component(i as u8))).drop_last()
                    =~= Seq::new((n - 1) as nat, |i: int| field_entries::<E>(values.push(value), Component(i as u8))));
            }
        }

        proof fn lemma_book_length<E: Event>(values: Seq<E::Component>)
    requires arity::<E>() <= history_syntax::MAX_ARITY,
        forall|i: int| 0 <= i < values.len() ==> E::coordinate_spec(values[i]) < arity::<E>(),
            ensures book_entries_count(Seq::new(arity::<E>(), |i: int| field_entries::<E>(values, Component(i as u8)))) == values.len(),
            decreases values.len(),
        {
            if values.len() > 0 {
                lemma_book_length::<E>(values.drop_last());
                lemma_book_push::<E>(values.drop_last(), values.last(), arity::<E>());
                assert(values.drop_last().push(values.last()) =~= values);
            } else {
                let book = Seq::new(arity::<E>(), |i: int| field_entries::<E>(values, Component(i as u8)));
                assert(forall|i: int| 0 <= i < book.len() ==> book[i].len() == 0) by { reveal(Seq::filter); }
                lemma_empty_book_length(book);
            }
        }

        proof fn lemma_empty_book_length<C>(book: Seq<Seq<(C,u64)>>)
            requires forall|i: int| 0 <= i < book.len() ==> book[i].len() == 0,
            ensures book_entries_count(book) == 0,
            decreases book.len(),
        { if book.len() > 0 { lemma_empty_book_length(book.drop_last()); } }

        pub(crate) proof fn lemma_constant_book_length<E: Event>(c: Constants<E>)
            requires constants_wf(c), ensures book_entries_count(constant_book(c)) == c.values@.len(),
        { lemma_book_length::<E>(c.values@); }

        /// The declared domains and the interned universes agree on membership (up to `eq_spec`)
        /// and on which coordinates are declared; `known` has one set per coordinate.
        pub(crate) open spec fn domains_linked<E: Event>(a: PolicyAnalyzer<E>) -> bool {
            &&& a.declared@.len() == arity::<E>() && a.known@.len() == arity::<E>()
            &&& forall|k: int, x: E::Component| 0 <= k < arity::<E>()
                ==> #[trigger] in_domain(selected_values(a.constants, a.universes[k]), x) == in_domain(a.declared@[k], x)
            &&& forall|k: int| 0 <= k < arity::<E>() ==> ((#[trigger] a.universes[k]) is None) == (a.declared@[k] is None)
        }

        /// What `new` establishes about the view: no rules, the declared domains, and the declared
        /// values as the known constants (R6).
        pub open spec fn constructed_from<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>) -> bool {
            &&& a@.rules == Seq::<RuleView<E::Component>>::empty()
            &&& a@.domains == d@
            &&& a@.known == declared_sets(d@)
        }

        pub(crate) proof fn lemma_constructor_domains<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>)
            requires analyzer_obligations::<E>(), declared_domains_encoded(a, d), universes_wf(a.constants, a.universes),
                a.declared@ == d@, a.known@ == declared_sets(d@), a.rules@.len() == 0,
            ensures domains_linked(a), constructed_from(a, d),
        {
            assert forall|k: int, x: E::Component| 0 <= k < arity::<E>() implies
                #[trigger] in_domain(selected_values(a.constants, a.universes[k]), x) == in_domain(a.declared@[k], x) by {
                lemma_declared_domain(a.constants, a.universes[k], d.components@[k]);
            }
            assert(analyzer_view(a).rules =~= Seq::<RuleView<E::Component>>::empty());
        }

        proof fn lemma_declared_domain<E: Event>(c: Constants<E>, u: Universe, raw: Option<Vec<E::Component>>)
            requires analyzer_obligations::<E>(), declared_universe(c, u, raw),
            ensures forall|x: E::Component| #[trigger] in_domain(selected_values(c, u), x)
                == in_domain(match raw { None => None, Some(vs) => Some(vs@.to_set()) }, x),
        {
    if let (Some(ids), Some(vs)) = (u, raw) {
        assert(universe_encoded(c, (*ids)@, vs@));
        lemma_selected_members(c, (*ids)@);
        let values = selected_code_values(c, (*ids)@);
        assert(selected_values(c, u) == Some(values));
        assert forall|x: E::Component| in_domain(Some(values), x)
            implies in_domain(Some(vs@.to_set()), x) by {
            let y = choose|y: E::Component| values.contains(y) && x.eq_spec(&y);
            assert(selected_code_values(c, (*ids)@).contains(y));
            let i = choose|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == y;
            assert(universe_id(c, vs@, (*ids)@[i]));
            let j = choose|j: int| 0 <= j < vs@.len() && stored_code(c, vs@[j], (*ids)@[i]);
            assert(vs@[j].eq_spec(&c.values@[(*ids)@[i] as int - 1]));
            assert(vs@[j].eq_spec(&y));
            assert(y.eq_spec(&vs@[j]));
            assert(x.eq_spec(&vs@[j]));
            assert(vs@.to_set().contains(vs@[j]));
        }
        assert forall|x: E::Component| in_domain(Some(vs@.to_set()), x)
            implies in_domain(Some(values), x) by {
            let y = choose|y: E::Component| vs@.to_set().contains(y) && x.eq_spec(&y);
            let j = choose|j: int| 0 <= j < vs@.len() && vs@[j] == y;
            assert(universe_value(c, (*ids)@, vs@[j]));
            let i = choose|i: int| 0 <= i < (*ids)@.len() && stored_code(c, y, (*ids)@[i]);
            let z = c.values@[(*ids)@[i] as int - 1];
            assert((*ids)@.to_set().contains((*ids)@[i]));
            assert(selected_code_values(c, (*ids)@).contains(z));
            assert(values.contains(z));
            assert(y.eq_spec(&z));
            assert(x.eq_spec(&z));
        }
            }
        }



        }
}
