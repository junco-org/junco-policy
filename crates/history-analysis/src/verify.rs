//! Ghost views and contracts linking the executable analyzer to the frozen refinement layers.

pub(crate) mod constraint_unique;
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
use alloc::vec::Vec;
use history_semantics::verify::refinement::*;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::syntax::Component;
use junco_core::ComponentValue;
use junco_core::kernel::verify as model;
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::history_specs::{self as language, EventView, Subst};
use vstd::prelude::*;

verus! {
pub(crate) open spec fn constant_book<E: Event>(c: Constants<E>)
    -> junco_core::verify::encoding::Codebook<ComponentValue<E>>
{
    let entries = c.values@.map(|i: int, value: ComponentValue<E>| (value, (i + 1) as u64));
    seq![
        entries.filter(|entry: (ComponentValue<E>, u64)| entry.0 is Principal),
        entries.filter(|entry: (ComponentValue<E>, u64)| entry.0 is Action),
        entries.filter(|entry: (ComponentValue<E>, u64)| entry.0 is Resource),
    ]
}
pub(crate) open spec fn component_of(index: usize) -> Component {
    if index == 0 { Component::Principal } else if index == 1 { Component::Action }
    else { Component::Resource }
}

pub(crate) open spec fn component_index(component: Component) -> usize {
    match component { Component::Principal => 0, Component::Action => 1,
        Component::Resource => 2 }
}

pub(crate) open spec fn codes(values: Seq<u32>) -> Set<nat> {
    values.to_set().map(|value: u32| value as nat)
}

pub(crate) open spec fn canonical(values: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] < values[j]
}

impl View for Atom {
    type V = model::Primitive;
    open(crate) spec fn view(&self) -> model::Primitive {
        let c = component_of(self.component);
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
        implementation::ConstraintView {
            principal: self.0[0]@, action: self.0[1]@, resource: self.0[2]@,
        }
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
            principal: class_option(self.classes[0]), action: class_option(self.classes[1]),
            resource: class_option(self.classes[2]), reg_principal: self.registers[0]@,
            reg_action: self.registers[1]@, reg_resource: self.registers[2]@,
        }
    }
}

pub(crate) open spec fn domain_view(universe: Universe) -> Option<Set<nat>> {
    match universe { None => None, Some(values) => Some(codes((*values)@)) }
}

pub(crate) open spec fn ndomains(universes: Universes) -> encoding::NDomains {
    encoding::NDomains { principal: domain_view(universes[0]),
        action: domain_view(universes[1]), resource: domain_view(universes[2]) }
}

pub(crate) open spec fn atom_set(atoms: Seq<Atom>) -> Set<model::Primitive> {
    atoms.to_set().map(|a: Atom| a@)
}

pub(crate) open spec fn atoms_wf(atoms: Seq<Atom>) -> bool {
    forall|i: int| 0 <= i < atoms.len() ==> atoms[i].component < 3
}

pub(crate) open spec fn register_wf(register: RegisterConstraint) -> bool {
    match register { RegisterConstraint::Equals(_) => true,
        RegisterConstraint::Differs(vs) => canonical(vs.view()) }
}

pub(crate) open spec fn constraint_wf(constraint: Constraint) -> bool {
    forall|i: int| 0 <= i < 3 ==> register_wf(constraint.0[i])
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


pub(crate) open spec fn head_view(constants: [Option<u32>; 3]) -> encoding::NHead {
    encoding::NHead {
        principal: option_code(constants[0]),
        action: option_code(constants[1]),
        resource: option_code(constants[2]),
    }
}

pub(crate) struct Scope {
    pub register: bool,
    pub constants: Seq<u32>,
}

impl View for Operands {
    type V = Seq<Scope>;
    open(crate) spec fn view(&self) -> Seq<Scope> {
        Seq::new(3, |i: int| Scope { register: self.register[i],
            constants: self.constants[i].view() })
    }
}

pub(crate) open spec fn operands_wf(operands: Operands) -> bool {
    forall|i: int| 0 <= i < 3 ==> canonical(operands.constants[i].view())
}

pub(crate) open spec fn operands_of(operands: Operands, atoms: Seq<Atom>) -> bool {
    operands_wf(operands) && operands_members(operands, atoms)
}

pub(crate) open spec fn operands_members(operands: Operands, atoms: Seq<Atom>) -> bool {
    &&& forall|i: int| #![trigger operands.register[i]] 0 <= i < 3
        ==> operands.register[i] == (exists|j: int| 0 <= j < atoms.len()
            && atoms[j].component == i && atoms[j].operand == Operand::Register)
    &&& forall|i: int, v: u32| #![trigger operands.constants[i].view().contains(v)]
        0 <= i < 3 ==> operands.constants[i].view().contains(v)
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
        == match implementation::register_of(g, l.component) {
            implementation::RegisterView::Equals(v) => l.equal && l.value == v,
            implementation::RegisterView::Differs(vs) => !l.equal && vs.contains(l.value),
        },
{
    let f = |l: inclusion::Literal| match implementation::register_of(g, l.component) {
        implementation::RegisterView::Equals(v) => l.equal && l.value == v,
        implementation::RegisterView::Differs(vs) => !l.equal && vs.contains(l.value),
    };
    let bound = register_literals(Component::Principal, g.principal)
        .union(register_literals(Component::Action, g.action))
        .union(register_literals(Component::Resource, g.resource));
    assert forall|l: inclusion::Literal| f(l) implies bound.contains(l) by {
        match l.component { Component::Principal => {}, Component::Action => {},
            Component::Resource => {} }
        match implementation::register_of(g, l.component) {
            implementation::RegisterView::Equals(v) => {
                assert(l == inclusion::eq_literal(l.component, v));
            },
            implementation::RegisterView::Differs(vs) => {
                assert(l == inclusion::ne_literal(l.component, l.value));
            },
        }
    }
    inclusion::lemma_set_new_bounded(f, bound.to_iset());
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
    ensures inclusion::sat_by(theta, implementation::constraint_of(g)) == (
        register_sat(g.principal, theta.principal) && register_sat(g.action, theta.action)
            && register_sat(g.resource, theta.resource)),
{
    lemma_constraint_view(g);
    if inclusion::sat_by(theta, implementation::constraint_of(g)) {
        assert forall|c: Component| register_sat(implementation::register_of(g, c),
            language::field_value(theta, c)) by {
            match implementation::register_of(g, c) {
                implementation::RegisterView::Equals(v) => {
                    let l = inclusion::eq_literal(c, v);
                    assert(implementation::constraint_of(g).contains(l));
                },
                implementation::RegisterView::Differs(vs) => {
                    if vs.contains(language::field_value(theta, c)) {
                        let l = inclusion::ne_literal(c, language::field_value(theta, c));
                        assert(implementation::constraint_of(g).contains(l));
                    }
                },
            }
        }
        assert(register_sat(implementation::register_of(g, Component::Principal),
            language::field_value(theta, Component::Principal)));
        assert(register_sat(implementation::register_of(g, Component::Action),
            language::field_value(theta, Component::Action)));
        assert(register_sat(implementation::register_of(g, Component::Resource),
            language::field_value(theta, Component::Resource)));
    } else if register_sat(g.principal, theta.principal) && register_sat(g.action, theta.action)
        && register_sat(g.resource, theta.resource) {
        assert forall|l: inclusion::Literal| #[trigger] implementation::constraint_of(g).contains(l)
            implies inclusion::literal_holds(theta, l) by {
            match l.component { Component::Principal => {}, Component::Action => {},
                Component::Resource => {} }
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
    ensures inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@))
        == (register_possible(g.0[0], universes[0])
            && register_possible(g.0[1], universes[1]) && register_possible(g.0[2], universes[2])),
{
    let d = ndomains(universes);
    if register_possible(g.0[0], universes[0]) && register_possible(g.0[1], universes[1])
        && register_possible(g.0[2], universes[2]) {
        let p = lemma_register_witness(g.0[0], universes[0]);
        let a = lemma_register_witness(g.0[1], universes[1]);
        let r = lemma_register_witness(g.0[2], universes[2]);
        let theta = EventView { principal: p, action: a, resource: r };
        lemma_constraint_sat(g@, theta);
        assert(encoding::n_event_in(d, theta)) by {
            assert forall|c: Component| encoding::n_domain(d, c) is Some
                implies encoding::n_domain(d, c)->Some_0.contains(language::field_value(theta, c)) by { match c {
                    Component::Principal => {}, Component::Action => {}, Component::Resource => {} } }
        }
        assert(encoding::n_theta_ok(d, theta));
        assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
    } else if inclusion::satisfiable(d, implementation::constraint_of(g@)) {
        let theta = choose|theta: Subst| encoding::n_theta_ok(d, theta)
            && inclusion::sat_by(theta, implementation::constraint_of(g@));
        lemma_constraint_sat(g@, theta);
        assert forall|i: int| 0 <= i < 3 implies register_possible(g.0[i], universes[i]) by {
            let c = component_of(i as usize);
            let v = language::field_value(theta, c);
            assert(encoding::n_domain(d, c) == domain_view(universes[i]));
            assert(register_sat(g.0[i]@, v));
        }
    }
}
pub(crate) proof fn lemma_head_view(g: Constraint, constants: [Option<u32>; 3])
    requires forall|i: int| 0 <= i < 3 ==> g.0[i]@ == match constants[i] {
        Some(v) => implementation::RegisterView::Equals(v as nat),
        None => implementation::RegisterView::Differs(Set::empty()),
    },
    ensures implementation::constraint_of(g@) == inclusion::head_constraint(head_view(constants)),
{
    lemma_constraint_view(g@);
    inclusion::lemma_head_constraint(head_view(constants));
    assert forall|l: inclusion::Literal|
        implementation::constraint_of(g@).contains(l)
            == inclusion::head_constraint(head_view(constants)).contains(l) by {
        let i = component_index(l.component) as int;
        assert(implementation::register_of(g@, l.component) == g.0[i]@);
        match l.component { Component::Principal => {}, Component::Action => {},
            Component::Resource => {} }
    }
    assert(implementation::constraint_of(g@) =~= inclusion::head_constraint(head_view(constants)));
}

pub(crate) proof fn lemma_constraint_entails(a: implementation::ConstraintView,
    b: implementation::ConstraintView)
    requires register_entails(a.principal, b.principal), register_entails(a.action, b.action),
        register_entails(a.resource, b.resource),
    ensures forall|d: encoding::NDomains|
        inclusion::entails(d, implementation::constraint_of(a), implementation::constraint_of(b)),
{
    assert forall|d: encoding::NDomains, theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, implementation::constraint_of(a))
        implies inclusion::sat_by(theta, implementation::constraint_of(b)) by {
        lemma_constraint_sat(a, theta);
        lemma_constraint_sat(b, theta);
        assert forall|c: Component| register_sat(implementation::register_of(b, c),
            language::field_value(theta, c)) by {
            match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
            match implementation::register_of(b, c) {
                implementation::RegisterView::Equals(v) => {},
                implementation::RegisterView::Differs(vs) => {
                    if vs.contains(language::field_value(theta, c)) {
                        assert(!register_sat(implementation::register_of(a, c),
                            language::field_value(theta, c)));
                    }
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
    requires atom.component < 3, operands_members(before, atoms),
        forall|i: int| #![trigger after.register[i]] 0 <= i < 3
            ==> after.register[i] == (before.register[i]
                || i == atom.component && atom.operand == Operand::Register),
        forall|i: int| #![trigger after.constants[i].view()] 0 <= i < 3
            ==> after.constants[i].view() == match atom.operand {
                Operand::Constant(v) => if i == atom.component { before.constants[i].view().push(v) }
                    else { before.constants[i].view() },
                Operand::Register => before.constants[i].view(),
            },
    ensures operands_members(after, atoms.push(atom)),
{
    assert forall|i: int| 0 <= i < 3 implies after.register[i]
        == (exists|j: int| 0 <= j < atoms.push(atom).len()
            && atoms.push(atom)[j].component == i
            && atoms.push(atom)[j].operand == Operand::Register) by {
        lemma_exists_push(atoms, atom, |a: Atom| a.component == i && a.operand == Operand::Register);
    }
    assert forall|i: int, v: u32| 0 <= i < 3 implies after.constants[i].view().contains(v)
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
    requires operands_members(before, atoms), after.register == before.register,
        forall|i: int| 0 <= i < 3 ==> after.constants[i].view().to_set()
            == before.constants[i].view().to_set(),
    ensures operands_members(after, atoms),
{
    assert forall|i: int, v: u32| 0 <= i < 3 implies
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
    -> Set<implementation::ConstraintView> {
    let p = register_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0]));
    let a = register_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1]));
    let r = register_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2]));
    register_product(p, a, r)
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
    let n0 = register_count(g.0[0]@, operands.register[0], operands.constants[0].view(), universes[0]);
    let n1 = register_count(g.0[1]@, operands.register[1], operands.constants[1].view(), universes[1]);
    let n2 = register_count(g.0[2]@, operands.register[2], operands.constants[2].view(), universes[2]);
    n0 <= usize::MAX && n1 <= usize::MAX && n2 <= usize::MAX
        && n0 * n1 <= usize::MAX && n0 * n1 * n2 <= usize::MAX
}
}

verus! {
pub(crate) open spec fn register_product(a: Set<implementation::RegisterView>,
    b: Set<implementation::RegisterView>, c: Set<implementation::RegisterView>)
    -> Set<implementation::ConstraintView> {
    a.map(|p: implementation::RegisterView| b.map(|q: implementation::RegisterView|
        c.map(|r: implementation::RegisterView| implementation::ConstraintView {
            principal: p, action: q, resource: r })).flatten()).flatten()
}

pub(crate) open spec fn choice_view(axes: [Seq<RegisterConstraint>; 3], i: int, j: int, k: int)
    -> implementation::ConstraintView {
    implementation::ConstraintView { principal: axes[0][i]@, action: axes[1][j]@, resource: axes[2][k]@ }
}

pub(crate) open spec fn product_done(axes: [Seq<RegisterConstraint>; 3],
    result: Set<implementation::ConstraintView>, first: int, second: int, third: int) -> bool {
    forall|i: int, j: int, k: int| #![trigger choice_view(axes, i, j, k)]
        0 <= i < axes[0].len() && 0 <= j < axes[1].len() && 0 <= k < axes[2].len()
        && (i < first || i == first && j < second || i == first && j == second && k < third)
            ==> result.contains(choice_view(axes, i, j, k))
}

pub(crate) proof fn lemma_constraint_views_push(values: Seq<Constraint>, value: Constraint)
    ensures constraint_views(values.push(value)) == constraint_views(values).insert(value@),
{
    values.lemma_push_to_set_commute(value);
    values.to_set().lemma_set_map_insert_commute(value, |g: Constraint| g@);
}

pub(crate) proof fn lemma_register_product_members(a: Set<implementation::RegisterView>,
    b: Set<implementation::RegisterView>, c: Set<implementation::RegisterView>)
    ensures forall|g: implementation::ConstraintView| #[trigger] register_product(a, b, c).contains(g)
        == (a.contains(g.principal) && b.contains(g.action) && c.contains(g.resource)),
{
    broadcast use vstd::set::Set::lemma_flatten_contains;
    let f = |p: implementation::RegisterView| b.map(|q: implementation::RegisterView|
        c.map(|r: implementation::RegisterView| implementation::ConstraintView {
            principal: p, action: q, resource: r })).flatten();
    assert forall|g: implementation::ConstraintView| register_product(a, b, c).contains(g)
        implies a.contains(g.principal) && b.contains(g.action) && c.contains(g.resource) by {
        let s = choose|s: Set<implementation::ConstraintView>| a.map(f).contains(s) && s.contains(g);
        let p = choose|p: implementation::RegisterView| a.contains(p) && f(p) == s;
        let h = |q: implementation::RegisterView| c.map(|r: implementation::RegisterView|
            implementation::ConstraintView { principal: p, action: q, resource: r });
        let t = choose|t: Set<implementation::ConstraintView>| b.map(h).contains(t) && t.contains(g);
        let q = choose|q: implementation::RegisterView| b.contains(q) && h(q) == t;
        let r = choose|r: implementation::RegisterView| c.contains(r)
            && implementation::ConstraintView { principal: p, action: q, resource: r } == g;
    }
    assert forall|g: implementation::ConstraintView| a.contains(g.principal) && b.contains(g.action)
        && c.contains(g.resource) implies register_product(a, b, c).contains(g) by {
        let h = |q: implementation::RegisterView| c.map(|r: implementation::RegisterView|
            implementation::ConstraintView { principal: g.principal, action: q, resource: r });
        assert(h(g.action).contains(g));
        assert(b.map(h).contains(h(g.action)));
        assert(f(g.principal).contains(g));
        assert(a.map(f).contains(f(g.principal)));
    }
}

pub(crate) proof fn lemma_product_step(axes: [Seq<RegisterConstraint>; 3],
    before: Set<implementation::ConstraintView>, after: Set<implementation::ConstraintView>,
    first: int, second: int, third: int)
    requires 0 <= first < axes[0].len(), 0 <= second < axes[1].len(), 0 <= third < axes[2].len(),
        product_done(axes, before, first, second, third),
        after == before.insert(choice_view(axes, first, second, third)),
    ensures product_done(axes, after, first, second, third + 1),
{
    assert forall|i: int, j: int, k: int| 0 <= i < axes[0].len() && 0 <= j < axes[1].len()
        && 0 <= k < axes[2].len()
        && (i < first || i == first && j < second || i == first && j == second && k < third + 1)
        implies after.contains(choice_view(axes, i, j, k)) by {
        if i == first && j == second && k == third {} else {
            assert(before.contains(choice_view(axes, i, j, k)));
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
    requires atoms_wf(atoms), operands_of(operands, atoms),
    ensures search::atoms_local(atom_set(atoms)),
        forall|c: Component| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c)))
            == operands.register[component_index(c) as int],
        forall|c: Component, v: nat| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
            == codes(operands.constants[component_index(c) as int].view()).contains(v),
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
    assert forall|c: Component, c2: Component| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c2)))
        implies c == c2 by {
        let i = choose|i: int| 0 <= i < atoms.len()
            && atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Variable(c2));
        match atoms[i].operand { Operand::Register => {}, Operand::Constant(_) => {} }
    }
    assert forall|c: Component| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c)))
        == operands.register[component_index(c) as int] by {
        let k = component_index(c) as int;
        assert(component_of(k as usize) == c);
        if atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Variable(c))) {
            let i = choose|i: int| 0 <= i < atoms.len()
                && atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Variable(c));
            assert(atoms[i].component == k && atoms[i].operand == Operand::Register);
        } else if operands.register[k] {
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i].component == k && atoms[i].operand == Operand::Register;
            assert(atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Variable(c)));
        }
    }
    assert forall|c: Component, v: nat| atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v)))
        == codes(operands.constants[component_index(c) as int].view()).contains(v) by {
        let k = component_index(c) as int;
        lemma_codes(operands.constants[k].view());
        if atom_set(atoms).contains(model::Primitive::Eq(c, model::GTerm::Constant(v))) {
            let i = choose|i: int| 0 <= i < atoms.len()
                && atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Constant(v));
            match atoms[i].operand {
                Operand::Constant(w) => {
                    assert(atoms[i].component == k && w as nat == v);
                    assert(operands.constants[k].view().contains(w));
                },
                Operand::Register => {},
            }
        } else if codes(operands.constants[k].view()).contains(v) {
            let j = choose|j: int| 0 <= j < operands.constants[k].view().len()
                && operands.constants[k].view()[j] as nat == v;
            let w = operands.constants[k].view()[j];
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i].component == k
                && atoms[i].operand == Operand::Constant(w);
            assert(atoms[i]@ == model::Primitive::Eq(c, model::GTerm::Constant(v)));
        }
    }
}

pub(crate) proof fn lemma_operand_pairs(operands: Operands, atoms: Seq<Atom>, universes: Universes)
    requires atoms_wf(atoms), operands_of(operands, atoms),
    ensures forall|p: (Component, nat)| #[trigger] search::domain_pairs(ndomains(universes), atom_set(atoms)).contains(p)
        == (operands.register[component_index(p.0) as int]
            && (codes(operands.constants[component_index(p.0) as int].view()).contains(p.1)
                || match domain_view(universes[component_index(p.0) as int]) {
                    None => false, Some(vs) => vs.contains(p.1) })),
{
    lemma_operand_atoms(operands, atoms);
    search::lemma_atom_pairs_members(atom_set(atoms));
    search::lemma_domain_pairs_members(ndomains(universes), atom_set(atoms));
    assert forall|c: Component| encoding::n_domain(ndomains(universes), c)
        == domain_view(universes[component_index(c) as int]) by { match c {
            Component::Principal => {}, Component::Action => {}, Component::Resource => {} } }
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
pub(crate) proof fn lemma_constraint_decides(d: encoding::NDomains, g: implementation::ConstraintView,
    c: Component, value: nat)
    requires implementation::register_of(g, c) is Equals
        || !register_sat(implementation::register_of(g, c), value),
    ensures inclusion::decides(d, implementation::constraint_of(g), c, value),
{
    let equal = match implementation::register_of(g, c) {
        implementation::RegisterView::Equals(v) => v == value,
        implementation::RegisterView::Differs(_) => false,
    };
    let l = inclusion::Literal { component: c, value, equal };
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, implementation::constraint_of(g))
        implies inclusion::sat_by(theta, Set::empty().insert(l)) by {
        lemma_constraint_sat(g, theta);
        assert(register_sat(implementation::register_of(g, c), language::field_value(theta, c))) by {
            match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
        match implementation::register_of(g, c) {
            implementation::RegisterView::Equals(v) => {},
            implementation::RegisterView::Differs(vs) => {},
        }
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

pub(crate) proof fn lemma_split_options_sound(g: Constraint, operands: Operands, universes: Universes,
    target: implementation::ConstraintView)
    requires inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
        split_views(g, operands, universes).contains(target),
    ensures inclusion::satisfiable(ndomains(universes), implementation::constraint_of(target)),
        inclusion::entails(ndomains(universes), implementation::constraint_of(target), implementation::constraint_of(g@)),
{
    let d = ndomains(universes);
    let theta0 = choose|theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, implementation::constraint_of(g@));
    lemma_theta_allowed(universes, theta0);
    lemma_constraint_sat(g@, theta0);
    lemma_register_product_members(
        register_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0])),
        register_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1])),
        register_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2])));
    lemma_register_bounded(g.0[0]); lemma_register_bounded(g.0[1]); lemma_register_bounded(g.0[2]);
    lemma_domain_bounded(universes[0]); lemma_domain_bounded(universes[1]); lemma_domain_bounded(universes[2]);
    lemma_codes(operands.constants[0].view()); lemma_codes(operands.constants[1].view()); lemma_codes(operands.constants[2].view());
    lemma_register_options_sound(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0]), target.principal);
    lemma_register_options_sound(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1]), target.action);
    lemma_register_options_sound(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2]), target.resource);
    let p = choose|v: nat| register_allowed(domain_view(universes[0]), v) && register_sat(target.principal, v);
    let a = choose|v: nat| register_allowed(domain_view(universes[1]), v) && register_sat(target.action, v);
    let r = choose|v: nat| register_allowed(domain_view(universes[2]), v) && register_sat(target.resource, v);
    let theta = EventView { principal: p, action: a, resource: r };
    lemma_constraint_sat(target, theta);
    assert(encoding::n_theta_ok(d, theta)) by {
        assert forall|c: Component| encoding::n_domain(d, c) is Some
            implies encoding::n_domain(d, c)->Some_0.contains(language::field_value(theta, c)) by {
            match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
    }
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, implementation::constraint_of(target))
        implies inclusion::sat_by(theta, implementation::constraint_of(g@)) by {
        lemma_constraint_sat(target, theta); lemma_constraint_sat(g@, theta);
    }
}

pub(crate) proof fn lemma_split_views_ok(g: Constraint, operands: Operands, universes: Universes, atoms: Seq<Atom>)
    requires atoms_wf(atoms), operands_of(operands, atoms),
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
    lemma_register_product_members(
        register_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0])),
        register_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1])),
        register_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2])));
    assert forall|gamma: inclusion::Constraint| #[trigger] cases.contains(gamma) implies
        inclusion::satisfiable(d, gamma) && inclusion::entails(d, gamma, implementation::constraint_of(g@))
        && forall|pair: (Component, nat)| pi.contains(pair) ==> #[trigger] inclusion::decides(d, gamma, pair.0, pair.1) by {
        let target = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma;
        lemma_split_options_sound(g, operands, universes, target);
        assert forall|pair: (Component, nat)| pi.contains(pair) implies inclusion::decides(d, gamma, pair.0, pair.1) by {
            let k = component_index(pair.0) as int;
            let t = implementation::register_of(target, pair.0);
            match pair.0 { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
            lemma_register_option_decision(g.0[k]@, codes(operands.constants[k].view()), domain_view(universes[k]), t, pair.1);
            lemma_constraint_decides(d, target, pair.0, pair.1);
        }
    }
    assert forall|theta: Subst| encoding::n_theta_ok(d, theta)
        && #[trigger] inclusion::sat_by(theta, implementation::constraint_of(g@))
        implies exists|gamma: inclusion::Constraint| #[trigger] cases.contains(gamma) && inclusion::sat_by(theta, gamma) by {
        lemma_constraint_sat(g@, theta);
        lemma_theta_allowed(universes, theta);
        let p = lemma_register_options_cover(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0]), theta.principal);
        let a = lemma_register_options_cover(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1]), theta.action);
        let r = lemma_register_options_cover(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2]), theta.resource);
        let target = implementation::ConstraintView { principal: p, action: a, resource: r };
        assert(options.contains(target));
        lemma_constraint_sat(target, theta);
        assert(cases.contains(implementation::constraint_of(target)));
    }
    assert forall|theta: Subst, gamma1: inclusion::Constraint, gamma2: inclusion::Constraint|
        encoding::n_theta_ok(d, theta) && cases.contains(gamma1) && cases.contains(gamma2)
        && #[trigger] inclusion::sat_by(theta, gamma1) && #[trigger] inclusion::sat_by(theta, gamma2) implies gamma1 == gamma2 by {
        let a = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma1;
        let b = choose|v: implementation::ConstraintView| options.contains(v) && implementation::constraint_of(v) == gamma2;
        lemma_constraint_sat(a, theta); lemma_constraint_sat(b, theta);
        lemma_register_options_unique(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0]), a.principal, b.principal, theta.principal);
        lemma_register_options_unique(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1]), a.action, b.action, theta.action);
        lemma_register_options_unique(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2]), a.resource, b.resource, theta.resource);
        assert(a == b);
    }
    assert(inclusion::split_ok(d, implementation::constraint_of(g@), pi, cases));
    assert(cases == split_views(g, operands, universes)
        .map(|v: implementation::ConstraintView| implementation::constraint_of(v)));
}
}

verus! {
pub(crate) proof fn lemma_theta_allowed(universes: Universes, theta: Subst)
    requires encoding::n_theta_ok(ndomains(universes), theta),
    ensures register_allowed(domain_view(universes[0]), theta.principal),
        register_allowed(domain_view(universes[1]), theta.action),
        register_allowed(domain_view(universes[2]), theta.resource),
{
    let d = ndomains(universes);
    assert(encoding::n_domain(d, Component::Principal) == domain_view(universes[0]));
    assert(encoding::n_domain(d, Component::Action) == domain_view(universes[1]));
    assert(encoding::n_domain(d, Component::Resource) == domain_view(universes[2]));
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
    let n0 = class_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), universes[0]).len();
    let n1 = class_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), universes[1]).len();
    let n2 = class_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), universes[2]).len();
    n0 <= usize::MAX && n1 <= usize::MAX && n2 <= usize::MAX
        && n0 * n1 <= usize::MAX && n0 * n1 * n2 <= usize::MAX
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

pub(crate) open spec fn letter_product(a: Set<Option<implementation::ClassView>>,
    b: Set<Option<implementation::ClassView>>, c: Set<Option<implementation::ClassView>>, registers: [Class; 3])
    -> Set<implementation::LetterView> {
    a.map(|p: Option<implementation::ClassView>| b.map(|q: Option<implementation::ClassView>|
        c.map(|r: Option<implementation::ClassView>| implementation::LetterView {
            principal: p, action: q, resource: r, reg_principal: registers[0]@,
            reg_action: registers[1]@, reg_resource: registers[2]@ })).flatten()).flatten()
}

pub(crate) open spec fn letters_views(g: Constraint, operands: Operands, universes: Universes)
    -> Set<implementation::LetterView> {
    letter_product(
        class_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), universes[0]),
        class_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), universes[1]),
        class_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), universes[2]),
        [raw_register_class(g.0[0]), raw_register_class(g.0[1]), raw_register_class(g.0[2])])
}

pub(crate) open spec fn letter_views(values: Seq<Letter>) -> Set<implementation::LetterView> {
    values.to_set().map(|l: Letter| l@)
}

pub(crate) open spec fn letter_choice_view(axes: [Seq<Option<Class>>; 3], registers: [Class; 3],
    i: int, j: int, k: int) -> implementation::LetterView {
    implementation::LetterView { principal: class_option(axes[0][i]), action: class_option(axes[1][j]),
        resource: class_option(axes[2][k]), reg_principal: registers[0]@, reg_action: registers[1]@, reg_resource: registers[2]@ }
}

pub(crate) open spec fn letter_product_done(axes: [Seq<Option<Class>>; 3], registers: [Class; 3],
    result: Set<implementation::LetterView>, first: int, second: int, third: int) -> bool {
    forall|i: int, j: int, k: int| #![trigger letter_choice_view(axes, registers, i, j, k)]
        0 <= i < axes[0].len() && 0 <= j < axes[1].len() && 0 <= k < axes[2].len()
        && (i < first || i == first && j < second || i == first && j == second && k < third)
            ==> result.contains(letter_choice_view(axes, registers, i, j, k))
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

pub(crate) proof fn lemma_letter_product_members(a: Set<Option<implementation::ClassView>>,
    b: Set<Option<implementation::ClassView>>, c: Set<Option<implementation::ClassView>>, registers: [Class; 3])
    ensures forall|l: implementation::LetterView| #[trigger] letter_product(a, b, c, registers).contains(l)
        == (a.contains(l.principal) && b.contains(l.action) && c.contains(l.resource)
            && l.reg_principal == registers[0]@ && l.reg_action == registers[1]@ && l.reg_resource == registers[2]@),
{
    broadcast use vstd::set::Set::lemma_flatten_contains;
    let f = |p: Option<implementation::ClassView>| b.map(|q: Option<implementation::ClassView>|
        c.map(|r: Option<implementation::ClassView>| implementation::LetterView { principal: p, action: q, resource: r,
            reg_principal: registers[0]@, reg_action: registers[1]@, reg_resource: registers[2]@ })).flatten();
    assert forall|l: implementation::LetterView| letter_product(a, b, c, registers).contains(l)
        implies a.contains(l.principal) && b.contains(l.action) && c.contains(l.resource)
            && l.reg_principal == registers[0]@ && l.reg_action == registers[1]@ && l.reg_resource == registers[2]@ by {
        let s = choose|s: Set<implementation::LetterView>| a.map(f).contains(s) && s.contains(l);
        let p = choose|p: Option<implementation::ClassView>| a.contains(p) && f(p) == s;
        let h = |q: Option<implementation::ClassView>| c.map(|r: Option<implementation::ClassView>|
            implementation::LetterView { principal: p, action: q, resource: r,
                reg_principal: registers[0]@, reg_action: registers[1]@, reg_resource: registers[2]@ });
        let t = choose|t: Set<implementation::LetterView>| b.map(h).contains(t) && t.contains(l);
        let q = choose|q: Option<implementation::ClassView>| b.contains(q) && h(q) == t;
        let r = choose|r: Option<implementation::ClassView>| c.contains(r)
            && implementation::LetterView { principal: p, action: q, resource: r,
                reg_principal: registers[0]@, reg_action: registers[1]@, reg_resource: registers[2]@ } == l;
    }
    assert forall|l: implementation::LetterView| a.contains(l.principal) && b.contains(l.action) && c.contains(l.resource)
        && l.reg_principal == registers[0]@ && l.reg_action == registers[1]@ && l.reg_resource == registers[2]@
        implies letter_product(a, b, c, registers).contains(l) by {
        let h = |q: Option<implementation::ClassView>| c.map(|r: Option<implementation::ClassView>|
            implementation::LetterView { principal: l.principal, action: q, resource: r,
                reg_principal: registers[0]@, reg_action: registers[1]@, reg_resource: registers[2]@ });
        assert(h(l.action).contains(l));
        assert(b.map(h).contains(h(l.action)));
        assert(f(l.principal).contains(l));
        assert(a.map(f).contains(f(l.principal)));
    }
}

pub(crate) proof fn lemma_letter_product_step(axes: [Seq<Option<Class>>; 3], registers: [Class; 3],
    before: Set<implementation::LetterView>, after: Set<implementation::LetterView>,
    first: int, second: int, third: int)
    requires 0 <= first < axes[0].len(), 0 <= second < axes[1].len(), 0 <= third < axes[2].len(),
        letter_product_done(axes, registers, before, first, second, third),
        after == before.insert(letter_choice_view(axes, registers, first, second, third)),
    ensures letter_product_done(axes, registers, after, first, second, third + 1),
{
    assert forall|i: int, j: int, k: int| 0 <= i < axes[0].len() && 0 <= j < axes[1].len()
        && 0 <= k < axes[2].len()
        && (i < first || i == first && j < second || i == first && j == second && k < third + 1)
        implies after.contains(letter_choice_view(axes, registers, i, j, k)) by {
        if i == first && j == second && k == third {} else {
            assert(before.contains(letter_choice_view(axes, registers, i, j, k)));
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

pub(crate) proof fn lemma_refined_ready(g: Constraint, operands: Operands, universes: Universes,
    refined: implementation::ConstraintView)
    requires split_views(g, operands, universes).contains(refined),
    ensures forall|c: Component| field_ready(implementation::register_of(refined, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        domain_view(universes[component_index(c) as int])),
{
    lemma_register_product_members(
        register_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0])),
        register_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1])),
        register_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2])));
    assert forall|c: Component| field_ready(implementation::register_of(refined, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        domain_view(universes[component_index(c) as int])) by {
        let k = component_index(c) as int;
        let r = implementation::register_of(refined, c);
        match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        lemma_register_options_members(g.0[k]@, operands.register[k], codes(operands.constants[k].view()), domain_view(universes[k]), r);
        if operands.register[k] {
            assert forall|v: nat| codes(operands.constants[k].view()).contains(v)
                implies r is Equals || !register_sat(r, v) by {
                lemma_register_option_decision(g.0[k]@, codes(operands.constants[k].view()), domain_view(universes[k]), r, v);
            }
        }
    }
}
}

verus! {
pub(crate) proof fn lemma_letters_members(g: Constraint, operands: Operands, universes: Universes)
    ensures forall|l: implementation::LetterView| #[trigger] letters_views(g, operands, universes).contains(l)
        == (forall|c: Component| class_options(implementation::register_of(g@, c),
                operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
                universes[component_index(c) as int]).contains(implementation::letter_class(l, c))
            && implementation::letter_register(l, c) == register_class(implementation::register_of(g@, c))),
{
    lemma_letter_product_members(
        class_options(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), universes[0]),
        class_options(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), universes[1]),
        class_options(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), universes[2]),
        [raw_register_class(g.0[0]), raw_register_class(g.0[1]), raw_register_class(g.0[2])]);
    assert forall|r: RegisterConstraint| raw_register_class(r)@ == register_class(r@) by {
        match r { RegisterConstraint::Equals(_) => {}, RegisterConstraint::Differs(_) => {} }
    }
    assert forall|l: implementation::LetterView| letters_views(g, operands, universes).contains(l)
        implies forall|c: Component| class_options(implementation::register_of(g@, c),
            operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
            universes[component_index(c) as int]).contains(implementation::letter_class(l, c))
            && implementation::letter_register(l, c) == register_class(implementation::register_of(g@, c)) by {
        assert forall|c: Component| class_options(implementation::register_of(g@, c),
            operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
            universes[component_index(c) as int]).contains(implementation::letter_class(l, c))
            && implementation::letter_register(l, c) == register_class(implementation::register_of(g@, c)) by {
            match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
    }
    assert forall|l: implementation::LetterView| (forall|c: Component| class_options(implementation::register_of(g@, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        universes[component_index(c) as int]).contains(implementation::letter_class(l, c))
        && implementation::letter_register(l, c) == register_class(implementation::register_of(g@, c)))
        implies letters_views(g, operands, universes).contains(l) by {
        assert(class_options(implementation::register_of(g@, Component::Principal), operands.register[0], codes(operands.constants[0].view()), universes[0])
            .contains(implementation::letter_class(l, Component::Principal)));
        assert(class_options(implementation::register_of(g@, Component::Action), operands.register[1], codes(operands.constants[1].view()), universes[1])
            .contains(implementation::letter_class(l, Component::Action)));
        assert(class_options(implementation::register_of(g@, Component::Resource), operands.register[2], codes(operands.constants[2].view()), universes[2])
            .contains(implementation::letter_class(l, Component::Resource)));
        assert(implementation::letter_register(l, Component::Principal) == register_class(implementation::register_of(g@, Component::Principal)));
        assert(implementation::letter_register(l, Component::Action) == register_class(implementation::register_of(g@, Component::Action)));
        assert(implementation::letter_register(l, Component::Resource) == register_class(implementation::register_of(g@, Component::Resource)));
    }
}

pub(crate) proof fn lemma_field_realizes(g: Constraint, operands: Operands, atoms: Seq<Atom>,
    letter: implementation::LetterView, theta: Subst, event: EventView)
    requires atoms_wf(atoms), operands_of(operands, atoms),
        forall|c: Component| implementation::letter_register(letter, c) == register_class(implementation::register_of(g@, c)),
        forall|c: Component| field_letter(implementation::register_of(g@, c),
            operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
            implementation::letter_class(letter, c), language::field_value(theta, c), language::field_value(event, c)),
    ensures search::realizes(theta, event, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_operand_atoms(operands, atoms);
    let alpha = implementation::letter_assignment(letter, atom_set(atoms));
    assert(alpha.dom() == atom_set(atoms));
    assert forall|p: model::Primitive| alpha.dom().contains(p)
        implies alpha[p] == model::primitive_holds(theta, p, event) by {
        match p {
            model::Primitive::Eq(c, model::GTerm::Constant(v)) => {
                assert(codes(operands.constants[component_index(c) as int].view()).contains(v));
            },
            model::Primitive::Eq(c, model::GTerm::Variable(c2)) => {
                assert(c == c2);
                assert(operands.register[component_index(c) as int]);
            },
        }
    }
}

pub(crate) proof fn lemma_letters_realize(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes,
    letter: implementation::LetterView, theta: Subst)
    requires atoms_wf(atoms), operands_of(operands, atoms), encoding::n_theta_ok(ndomains(universes), theta),
        inclusion::sat_by(theta, implementation::constraint_of(g@)), letters_views(g, operands, universes).contains(letter),
        letters_ready(g@, operands, universes),
    ensures exists|e: EventView| encoding::n_event_in(ndomains(universes), e)
        && search::realizes(theta, e, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_letters_members(g, operands, universes);
    lemma_constraint_sat(g@, theta); lemma_theta_allowed(universes, theta);
    let p = lemma_field_letter_sound(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), universes[0], letter.principal, theta.principal);
    let a = lemma_field_letter_sound(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), universes[1], letter.action, theta.action);
    let r = lemma_field_letter_sound(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), universes[2], letter.resource, theta.resource);
    let event = EventView { principal: p, action: a, resource: r };
    assert forall|c: Component| field_letter(implementation::register_of(g@, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        implementation::letter_class(letter, c), language::field_value(theta, c), language::field_value(event, c)) by {
        match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
    }
    lemma_field_realizes(g, operands, atoms, letter, theta, event);
    assert(encoding::n_event_in(ndomains(universes), event)) by {
        assert forall|c: Component| encoding::n_domain(ndomains(universes), c) is Some
            implies encoding::n_domain(ndomains(universes), c)->Some_0.contains(language::field_value(event, c)) by {
            match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
    }
}

pub(crate) proof fn lemma_letters_complete(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes,
    theta: Subst, event: EventView) -> (letter: implementation::LetterView)
    requires atoms_wf(atoms), operands_of(operands, atoms), encoding::n_theta_ok(ndomains(universes), theta),
        inclusion::sat_by(theta, implementation::constraint_of(g@)), encoding::n_event_in(ndomains(universes), event),
        letters_ready(g@, operands, universes),
    ensures letters_views(g, operands, universes).contains(letter),
        search::realizes(theta, event, implementation::letter_assignment(letter, atom_set(atoms))),
{
    lemma_constraint_sat(g@, theta); lemma_theta_allowed(universes, theta);
    lemma_event_domains(universes, event);
    let p = lemma_field_letter_complete(g.0[0]@, operands.register[0], codes(operands.constants[0].view()), universes[0], theta.principal, event.principal);
    let a = lemma_field_letter_complete(g.0[1]@, operands.register[1], codes(operands.constants[1].view()), universes[1], theta.action, event.action);
    let r = lemma_field_letter_complete(g.0[2]@, operands.register[2], codes(operands.constants[2].view()), universes[2], theta.resource, event.resource);
    let letter = implementation::LetterView { principal: p, action: a, resource: r,
        reg_principal: register_class(g.0[0]@), reg_action: register_class(g.0[1]@), reg_resource: register_class(g.0[2]@) };
    lemma_letters_members(g, operands, universes);
    assert forall|c: Component| class_options(implementation::register_of(g@, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        universes[component_index(c) as int]).contains(implementation::letter_class(letter, c))
        && implementation::letter_register(letter, c) == register_class(implementation::register_of(g@, c)) by {
        match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
    }
    assert forall|c: Component| field_letter(implementation::register_of(g@, c),
        operands.register[component_index(c) as int], codes(operands.constants[component_index(c) as int].view()),
        implementation::letter_class(letter, c), language::field_value(theta, c), language::field_value(event, c)) by {
        match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
    }
    lemma_field_realizes(g, operands, atoms, letter, theta, event);
    letter
}

pub(crate) proof fn lemma_letters_are_realizable(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes)
    requires atoms_wf(atoms), operands_of(operands, atoms),
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
    field_ready(g.principal, operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0]))
        && field_ready(g.action, operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1]))
        && field_ready(g.resource, operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2]))
}

pub(crate) proof fn lemma_event_domains(universes: Universes, event: EventView)
    requires encoding::n_event_in(ndomains(universes), event),
    ensures domain_view(universes[0]) matches Some(vs) ==> vs.contains(event.principal),
        domain_view(universes[1]) matches Some(vs) ==> vs.contains(event.action),
        domain_view(universes[2]) matches Some(vs) ==> vs.contains(event.resource),
{
    let d = ndomains(universes);
    assert(encoding::n_domain(d, Component::Principal) == domain_view(universes[0]));
    assert(encoding::n_domain(d, Component::Action) == domain_view(universes[1]));
    assert(encoding::n_domain(d, Component::Resource) == domain_view(universes[2]));
}
}

verus! {
pub(crate) open spec fn group_constraints(groups: Seq<(Constraint, Vec<Letter>)>) -> Seq<Constraint> {
    groups.map(|i: int, group: (Constraint, Vec<Letter>)| group.0)
}

pub(crate) open spec fn steps_result(g: Constraint, atoms: Seq<Atom>, universes: Universes,
    groups: Seq<(Constraint, Vec<Letter>)>) -> bool {
    exists|operands: Operands| operands_of(operands, atoms)
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes)
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
    requires split_views(g, operands, universes).contains(refined@),
    ensures letters_ready(refined@, operands, universes),
{
    lemma_refined_ready(g, operands, universes, refined@);
    assert(field_ready(implementation::register_of(refined@, Component::Principal), operands.register[0], codes(operands.constants[0].view()), domain_view(universes[0])));
    assert(field_ready(implementation::register_of(refined@, Component::Action), operands.register[1], codes(operands.constants[1].view()), domain_view(universes[1])));
    assert(field_ready(implementation::register_of(refined@, Component::Resource), operands.register[2], codes(operands.constants[2].view()), domain_view(universes[2])));
}

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
    requires atoms_wf(atoms), steps_result(g, atoms, universes, groups),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
    ensures implemented_cases(groups, atom_set(atoms), next).to_iset() == search::paper_steps(ndomains(universes),
        search::Item { constraint: implementation::constraint_of(g@), state }, atom_set(atoms),
        constraint_views(group_constraints(groups)).map(|v: implementation::ConstraintView| implementation::constraint_of(v)), next),
{
    let operands = choose|operands: Operands| operands_of(operands, atoms)
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes);
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
    requires atoms_wf(atoms), steps_result(g, atoms, universes, groups),
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
    hide(language::lang);
    hide(class_options);
    hide(register_options);
    let operands = choose|operands: Operands| operands_of(operands, atoms)
        && constraint_views(group_constraints(groups)) == split_views(g, operands, universes)
        && forall|i: int| 0 <= i < groups.len() ==> constraint_wf(groups[i].0)
            && letter_views(groups[i].1@) == letters_views(groups[i].0, operands, universes);
    lemma_operand_atoms(operands, atoms); lemma_split_views_ok(g, operands, universes, atoms);
    lemma_steps_are_paper_steps(g, atoms, universes, groups, state, next);
    search::theorem_successor_cases_finite_domains();
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
    lemma_register_view_injective(a.0[0], b.0[0]);
    lemma_register_view_injective(a.0[1], b.0[1]);
    lemma_register_view_injective(a.0[2], b.0[2]);
    assert forall|i: int| 0 <= i < 3 implies constraint_key(a)[i] == constraint_key(b)[i] by {
        if i == 0 {} else if i == 1 {} else { assert(i == 2); }
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
    requires constraint_key(a) == constraint_key(b),
    ensures a@ == b@,
{
    assert(constraint_key(a)[0] == constraint_key(b)[0]);
    assert(constraint_key(a)[1] == constraint_key(b)[1]);
    assert(constraint_key(a)[2] == constraint_key(b)[2]);
    lemma_register_key_view(a.0[0], b.0[0]);
    lemma_register_key_view(a.0[1], b.0[1]);
    lemma_register_key_view(a.0[2], b.0[2]);
}

pub(crate) proof fn lemma_constraint_literals_injective(a: implementation::ConstraintView, b: implementation::ConstraintView)
    requires implementation::constraint_of(a) == implementation::constraint_of(b),
    ensures a == b,
{
    lemma_constraint_view(a); lemma_constraint_view(b);
    assert forall|c: Component| implementation::register_of(a, c) == implementation::register_of(b, c) by {
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
    assert(implementation::register_of(a, Component::Principal) == implementation::register_of(b, Component::Principal));
    assert(implementation::register_of(a, Component::Action) == implementation::register_of(b, Component::Action));
    assert(implementation::register_of(a, Component::Resource) == implementation::register_of(b, Component::Resource));
    assert(a.principal == b.principal); assert(a.action == b.action); assert(a.resource == b.resource);
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
        ==> forall|atoms: Seq<Atom>| atoms_wf(atoms) && operands_of(operands, atoms)
            ==> inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
                search::domain_pairs(ndomains(universes), atom_set(atoms)),
                constraint_views(result).map(|v: implementation::ConstraintView| implementation::constraint_of(v)))
}

pub(crate) open spec fn letters_contract(g: Constraint, operands: Operands, universes: Universes,
    result: Seq<Letter>) -> bool {
    inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) && letters_ready(g@, operands, universes)
        ==> forall|atoms: Seq<Atom>, alpha: search::Assignment| atoms_wf(atoms) && operands_of(operands, atoms) ==>
            letter_views(result).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(alpha)
                == (alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
                    encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
                    && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha))
}

pub(crate) proof fn lemma_split_contract(g: Constraint, operands: Operands, universes: Universes, result: Seq<Constraint>)
    requires constraint_views(result) == split_views(g, operands, universes),
    ensures split_contract(g, operands, universes, result),
{
    if inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) {
        assert forall|atoms: Seq<Atom>| atoms_wf(atoms) && operands_of(operands, atoms) implies
            inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
                search::domain_pairs(ndomains(universes), atom_set(atoms)),
                constraint_views(result).map(|v: implementation::ConstraintView| implementation::constraint_of(v))) by {
            lemma_split_views_ok(g, operands, universes, atoms);
        }
    }
}

pub(crate) proof fn lemma_letters_contract(g: Constraint, operands: Operands, universes: Universes, result: Seq<Letter>)
    requires letter_views(result) == letters_views(g, operands, universes),
    ensures letters_contract(g, operands, universes, result),
{
    if inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)) && letters_ready(g@, operands, universes) {
        assert forall|atoms: Seq<Atom>, alpha: search::Assignment| atoms_wf(atoms) && operands_of(operands, atoms) implies
            letter_views(result).map(|l: implementation::LetterView| implementation::letter_assignment(l, atom_set(atoms))).contains(alpha)
                == (alpha.dom() == atom_set(atoms) && exists|theta: Subst, event: EventView|
                    encoding::n_theta_ok(ndomains(universes), theta) && encoding::n_event_in(ndomains(universes), event)
                    && inclusion::sat_by(theta, implementation::constraint_of(g@)) && search::realizes(theta, event, alpha)) by {
            lemma_letters_are_realizable(g, operands, atoms, universes);
        }
    }
}

pub(crate) proof fn lemma_constraint_key_obligations()
    requires crate::native::hash_coherent::<Constraint>(),
    ensures crate::native::key_obligations::<Constraint>(),
{}
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
            FlatPair { head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
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
        before.tests@.len() <= after.tests@.len()
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
/// Native Eq/hash correspondence and event projection laws required by analyzer proofs.
pub open(crate) spec fn analyzer_obligations<E: Event>() -> bool {
    E::obeys_projection_spec() && crate::native::key_obligations::<ComponentValue<E>>()
        && search_exec::search_obligations()
}
}

pub use frontend::{analyzer_state_wf, constructor_capacity, query_capacity};

pub(crate) mod frontend {
    use super::*;
    use crate::analyzer::{Domains, PolicyAnalyzer};
    use junco_core::flat::{FlatHead, FlatPair};
    use junco_core::verify::{encoding as enc, flatten as fl};
    use vstd::std_specs::cmp::PartialEqSpec;

    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

    pub(crate) open spec fn value_field<E: Event>(v: ComponentValue<E>) -> Component {
        match v { ComponentValue::Principal(_) => Component::Principal,
            ComponentValue::Action(_) => Component::Action,
            ComponentValue::Resource(_) => Component::Resource }
    }

    pub(crate) open spec fn entries<E: Event>(values: Seq<ComponentValue<E>>) -> Seq<(ComponentValue<E>, u64)> {
        values.map(|i: int, v: ComponentValue<E>| (v, (i + 1) as u64))
    }

    pub(crate) open spec fn field_entries<E: Event>(values: Seq<ComponentValue<E>>, field: Component)
        -> Seq<(ComponentValue<E>, u64)> {
        entries(values).filter(|p: (ComponentValue<E>, u64)| value_field(p.0) == field)
    }

    pub(crate) open spec fn constants_wf<E: Event>(c: Constants<E>) -> bool {
        &&& c.values@.len() <= u32::MAX
        &&& crate::native::representatives(c.ids)
            == c.values@.map(|i: int, v: ComponentValue<E>| (v, (i + 1) as u32))
        &&& forall|i: int, j: int| 0 <= i < j < c.values@.len()
            ==> !c.values@[i].eq_spec(&c.values@[j])
    }

    pub(crate) open spec fn constants_frame<E: Event>(a: Constants<E>, b: Constants<E>) -> bool {
        a.values@.is_prefix_of(b.values@)
    }

    pub(crate) open spec fn stored_code<E: Event>(c: Constants<E>, v: ComponentValue<E>, id: u32) -> bool {
        id > 0 && id <= c.values@.len() && v.eq_spec(&c.values@[id as int - 1])
    }

    pub(crate) proof fn lemma_field_book<E: Event>(c: Constants<E>, field: Component)
        ensures constant_book(c)[junco_core::flat::verify::field_index(field)] == field_entries(c.values@, field),
    {
        let p = |entry: (ComponentValue<E>, u64)| value_field(entry.0) == field;
        let q = match field {
            Component::Principal => |entry: (ComponentValue<E>, u64)| entry.0 is Principal,
            Component::Action => |entry: (ComponentValue<E>, u64)| entry.0 is Action,
            Component::Resource => |entry: (ComponentValue<E>, u64)| entry.0 is Resource,
        };
        assert forall|x: (ComponentValue<E>, u64)| #[trigger] p(x) == q(x) by { match x.0 { ComponentValue::Principal(_) => {}, ComponentValue::Action(_) => {}, ComponentValue::Resource(_) => {} } }
        assert(entries(c.values@).filter(p) == entries(c.values@).filter(q)) by {
            reveal(Seq::filter);
            lemma_filter_ext(entries(c.values@), p, q);
        }
    }

    proof fn lemma_filter_ext<T>(s: Seq<T>, p: spec_fn(T) -> bool, q: spec_fn(T) -> bool)
        requires forall|x: T| #[trigger] p(x) == q(x),
        ensures s.filter(p) == s.filter(q),
        decreases s.len(),
    {
        reveal(Seq::filter);
        if s.len() > 0 { lemma_filter_ext(s.drop_last(), p, q); }
    }

    pub(crate) proof fn lemma_field_entry_source<E: Event>(values: Seq<ComponentValue<E>>, field: Component, i: int)
        requires 0 <= i < field_entries(values, field).len(),
        ensures exists|j: int| 0 <= j < values.len() && field_entries(values, field)[i]
            == (values[j], (j + 1) as u64),
            value_field(field_entries(values, field)[i].0) == field,
    {
        let p = |x: (ComponentValue<E>, u64)| value_field(x.0) == field;
        entries(values).lemma_filter_pred(p, i);
        entries(values).lemma_filter_contains_rev(p, field_entries(values, field)[i]);
        let j = choose|j: int| 0 <= j < entries(values).len()
            && entries(values)[j] == field_entries(values, field)[i];
        assert(entries(values)[j] == (values[j], (j + 1) as u64));
    }

    proof fn lemma_component_eq<E: Event>(f: Component, a: ComponentValue<E>, b: ComponentValue<E>)
        requires fl::component_domain::<E>()(f, a), fl::component_domain::<E>()(f, b),
        ensures fl::component_equality::<E>()(f, a, b) == a.eq_spec(&b),
    {
        match (f, a, b) {
            (Component::Principal, ComponentValue::Principal(_), ComponentValue::Principal(_)) => {},
            (Component::Action, ComponentValue::Action(_), ComponentValue::Action(_)) => {},
            (Component::Resource, ComponentValue::Resource(_), ComponentValue::Resource(_)) => {},
            _ => {},
        }
    }

    pub(crate) proof fn lemma_constants_maps<E: Event>(c: Constants<E>)
        requires constants_wf(c), analyzer_obligations::<E>(),
        ensures enc::maps_wf(constant_book(c), fl::component_equality::<E>(), fl::component_domain::<E>()),
    {
        assert forall|f: Component, a: ComponentValue<E>| #[trigger] fl::component_domain::<E>()(f, a) implies fl::component_equality::<E>()(f, a, a) by {
            lemma_component_eq(f, a, a); assert(a.eq_spec(&a));
        }
        assert forall|f: Component, a: ComponentValue<E>, b: ComponentValue<E>| fl::component_domain::<E>()(f, a) && fl::component_domain::<E>()(f, b)
            implies #[trigger] fl::component_equality::<E>()(f, a, b) == fl::component_equality::<E>()(f, b, a) by {
            lemma_component_eq(f, a, b); lemma_component_eq(f, b, a); assert(a.eq_spec(&b) == b.eq_spec(&a));
        }
        assert forall|f: Component, a: ComponentValue<E>, b: ComponentValue<E>, d: ComponentValue<E>|
            fl::component_domain::<E>()(f, a) && fl::component_domain::<E>()(f, b) && fl::component_domain::<E>()(f, d)
                && #[trigger] fl::component_equality::<E>()(f, a, b) && #[trigger] fl::component_equality::<E>()(f, b, d)
            implies fl::component_equality::<E>()(f, a, d) by {
            lemma_component_eq(f, a, b); lemma_component_eq(f, b, d); lemma_component_eq(f, a, d);
            assert(a.eq_spec(&b)); assert(b.eq_spec(&d)); assert(a.eq_spec(&d));
        }
        assert(enc::equality_laws(fl::component_equality::<E>(), fl::component_domain::<E>()));
        assert forall|f: int, i: int| 0 <= f < 3 && 0 <= i < constant_book(c)[f].len()
            implies fl::component_domain::<E>()(enc::field_at(f), constant_book(c)[f][i].0)
                && constant_book(c)[f][i].1 > 0 by {
            let field = enc::field_at(f);
            assert(junco_core::flat::verify::field_index(field) == f);
            lemma_field_book(c, field);
            lemma_field_entry_source(c.values@, field, i);
            let j = choose|j: int| 0 <= j < c.values@.len()
                && field_entries(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
            match constant_book(c)[f][i].0 { ComponentValue::Principal(_) => {}, ComponentValue::Action(_) => {}, ComponentValue::Resource(_) => {} }
        }
        assert forall|f: int, i: int, k: int| 0 <= f < 3 && 0 <= i < constant_book(c)[f].len()
            && 0 <= k < constant_book(c)[f].len() implies
            fl::component_equality::<E>()(enc::field_at(f), constant_book(c)[f][i].0, constant_book(c)[f][k].0)
                == (constant_book(c)[f][i].1 == constant_book(c)[f][k].1) by {
            let field = enc::field_at(f);
            assert(junco_core::flat::verify::field_index(field) == f);
            lemma_field_book(c, field);
            lemma_field_entry_source(c.values@, field, i);
            lemma_field_entry_source(c.values@, field, k);
            let j = choose|j: int| 0 <= j < c.values@.len() && field_entries(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
            let l = choose|l: int| 0 <= l < c.values@.len() && field_entries(c.values@, field)[k] == (c.values@[l], (l + 1) as u64);
            if j < l { assert(!c.values@[j].eq_spec(&c.values@[l])); }
            if l < j { assert(!c.values@[l].eq_spec(&c.values@[j])); }
            match (c.values@[j], c.values@[l]) { (ComponentValue::Principal(_), ComponentValue::Principal(_)) => {}, (ComponentValue::Action(_), ComponentValue::Action(_)) => {}, (ComponentValue::Resource(_), ComponentValue::Resource(_)) => {}, _ => {} }
        }
    }

    pub(crate) proof fn lemma_stored_encoded<E: Event>(c: Constants<E>, v: ComponentValue<E>, id: u32)
        requires constants_wf(c), stored_code(c, v, id),
        ensures enc::encoded(constant_book(c), fl::component_equality::<E>(), value_field(v), v, id as u64),
    {
        let field = value_field(v);
        let j = id as int - 1;
        assert(value_field(c.values@[j]) == field) by { match (v, c.values@[j]) { (ComponentValue::Principal(_), ComponentValue::Principal(_)) => {}, (ComponentValue::Action(_), ComponentValue::Action(_)) => {}, (ComponentValue::Resource(_), ComponentValue::Resource(_)) => {}, _ => {} } }
        lemma_field_book(c, field);
        entries(c.values@).lemma_filter_contains(|p: (ComponentValue<E>, u64)| value_field(p.0) == field, j);
        let i = choose|i: int| 0 <= i < field_entries(c.values@, field).len()
            && field_entries(c.values@, field)[i] == entries(c.values@)[j];
        assert(enc::encoded(constant_book(c), fl::component_equality::<E>(), field, v, id as u64));
    }

    pub(crate) proof fn lemma_constants_extend<E: Event>(a: Constants<E>, b: Constants<E>)
        requires constants_wf(a), constants_wf(b), constants_frame(a, b),
        ensures enc::extends(constant_book(a), constant_book(b), fl::component_equality::<E>()),
    {
        assert forall|field: Component, v: ComponentValue<E>, id: u64|
            enc::encoded(constant_book(a), fl::component_equality::<E>(), field, v, id)
            implies enc::encoded(constant_book(b), fl::component_equality::<E>(), field, v, id) by {
            lemma_field_book(a, field);
            let f = junco_core::flat::verify::field_index(field);
            let i = choose|i: int| 0 <= i < constant_book(a)[f].len() && constant_book(a)[f][i].1 == id
                && fl::component_equality::<E>()(field, v, constant_book(a)[f][i].0);
            lemma_field_entry_source(a.values@, field, i);
            let j = choose|j: int| 0 <= j < a.values@.len() && field_entries(a.values@, field)[i] == (a.values@[j], (j + 1) as u64);
            assert(b.values@[j] == a.values@[j]);
            assert(stored_code(b, v, id as u32));
            assert(value_field(v) == field);
            lemma_stored_encoded(b, v, id as u32);
        }
    }

    pub(crate) open spec fn universe_id<E: Event>(c: Constants<E>, values: Seq<ComponentValue<E>>, id: u32) -> bool {
        exists|j: int| 0 <= j < values.len() && stored_code(c, values[j], id)
    }

    pub(crate) open spec fn universe_value<E: Event>(c: Constants<E>, ids: Seq<u32>, value: ComponentValue<E>) -> bool {
        exists|i: int| 0 <= i < ids.len() && stored_code(c, value, ids[i])
    }

    pub(crate) open spec fn universe_encoded<E: Event>(c: Constants<E>, ids: Seq<u32>, values: Seq<ComponentValue<E>>) -> bool {
        &&& ids.no_duplicates()
        &&& forall|i: int| 0 <= i < ids.len() ==> #[trigger] universe_id(c, values, ids[i])
        &&& forall|j: int| 0 <= j < values.len() ==> #[trigger] universe_value(c, ids, values[j])
    }

    pub(crate) proof fn lemma_stored_frame<E: Event>(a: Constants<E>, b: Constants<E>, v: ComponentValue<E>, id: u32)
        requires constants_frame(a, b), stored_code(a, v, id),
        ensures stored_code(b, v, id),
    {}

    pub(crate) proof fn lemma_universe_frame<E: Event>(a: Constants<E>, b: Constants<E>, ids: Seq<u32>, values: Seq<ComponentValue<E>>)
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

    /// Sufficient constructor capacity: the total number of declared values fits the u32 code space.
    pub closed spec fn constructor_capacity<E: Event>(domains: Domains<E>) -> bool {
        option_len(domains.principals) + option_len(domains.actions) + option_len(domains.resources) <= u32::MAX
    }

    pub(crate) open spec fn encode_capacity<E: Event>(a: PolicyAnalyzer<E>, source: FlatPair<ComponentValue<E>>) -> bool {
        a.constants.values@.len() + 3 + source.tests@.len() <= u32::MAX
    }

    /// Sufficient capacities for constant ids and the per-state split and letter products.
    /// Constraint-id and fresh-value exhaustion are runtime errors, not preconditions.
    pub open(crate) spec fn query_capacity<E: Event>(a: PolicyAnalyzer<E>, left: history_syntax::RegexExpr<E>, right: history_syntax::RegexExpr<E>) -> bool {
        // Traversal costs overbound the query's vocabulary.
        let count = a.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@);
        count <= u32::MAX && (count + 2) * (count + 2) * (count + 2) <= usize::MAX
    }

    pub(crate) open spec fn pins(head: Seq<FlatHead<u64>>) -> encoding::NHead {
        encoding::NHead { principal: encoding::head_code(head[0]), action: encoding::head_code(head[1]), resource: encoding::head_code(head[2]) }
    }

    pub(crate) open spec fn numeric_head_wf(head: Seq<FlatHead<u64>>) -> bool {
        head.len() == 3 && forall|i: int| #![trigger head[i]] 0 <= i < 3 ==> match head[i] { FlatHead::Constant(v) => v <= u32::MAX, _ => true }
    }

    pub(crate) proof fn lemma_lowered_head_bound<E: Event>(c: Constants<E>, source: FlatPair<ComponentValue<E>>, target: FlatPair<u64>)
        requires constants_wf(c), enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        ensures numeric_head_wf(target.head@),
    {
        assert forall|i: int| #![trigger target.head@[i]] 0 <= i < 3 implies match target.head@[i] { FlatHead::Constant(v) => v <= u32::MAX, _ => true } by {
            if let FlatHead::Constant(id) = target.head@[i] {
                let field = enc::field_at(i);
                lemma_field_book(c, field);
                let value = match source.head@[i] { FlatHead::Constant(v) => v, _ => arbitrary() };
                let j = choose|j: int| 0 <= j < constant_book(c)[i].len() && constant_book(c)[i][j].1 == id && fl::component_equality::<E>()(field, value, constant_book(c)[i][j].0);
                lemma_field_entry_source(c.values@, field, j);
            }
        }
    }

    pub(crate) open spec fn encoding_head_code(head: FlatHead<u64>) -> Option<nat> { encoding::head_code(head) }

    pub(crate) open spec fn declared_universe<E: Event, T>(c: Constants<E>, u: Universe, vs: Option<Vec<T>>, f: spec_fn(T) -> ComponentValue<E>) -> bool {
        match (u, vs) { (None, None) => true, (Some(ids), Some(values)) => universe_encoded(c, (*ids)@, values@.map_values(f)), _ => false }
    }

    pub(crate) open spec fn declared_domains_encoded<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>) -> bool {
        declared_universe(a.constants, a.universes[0], d.principals, |v: E::Principal| ComponentValue::<E>::Principal(v))
            && declared_universe(a.constants, a.universes[1], d.actions, |v: E::Action| ComponentValue::<E>::Action(v))
            && declared_universe(a.constants, a.universes[2], d.resources, |v: E::Resource| ComponentValue::<E>::Resource(v))
    }

    pub(crate) open spec fn selected_values<E: Event>(c: Constants<E>, u: Universe) -> Option<Set<ComponentValue<E>>> {
        match u { None => None, Some(ids) => Some((*ids)@.to_set().map(|id: u32| c.values@[id as int - 1])) }
    }

    pub(crate) open spec fn principal_of<E: Event>(v: ComponentValue<E>) -> E::Principal {
        match v { ComponentValue::Principal(x) => x, _ => arbitrary() }
    }
    pub(crate) open spec fn action_of<E: Event>(v: ComponentValue<E>) -> E::Action {
        match v { ComponentValue::Action(x) => x, _ => arbitrary() }
    }
    pub(crate) open spec fn resource_of<E: Event>(v: ComponentValue<E>) -> E::Resource {
        match v { ComponentValue::Resource(x) => x, _ => arbitrary() }
    }

    pub(crate) open spec fn principal_values<E: Event>(values: Set<ComponentValue<E>>) -> Set<E::Principal> {
        values.filter(|v: ComponentValue<E>| v is Principal).map(|v: ComponentValue<E>| principal_of::<E>(v))
    }
    pub(crate) open spec fn action_values<E: Event>(values: Set<ComponentValue<E>>) -> Set<E::Action> {
        values.filter(|v: ComponentValue<E>| v is Action).map(|v: ComponentValue<E>| action_of::<E>(v))
    }
    pub(crate) open spec fn resource_values<E: Event>(values: Set<ComponentValue<E>>) -> Set<E::Resource> {
        values.filter(|v: ComponentValue<E>| v is Resource).map(|v: ComponentValue<E>| resource_of::<E>(v))
    }

    impl<E: Event> View for PolicyAnalyzer<E> {
        type V = analyzer::AnalyzerView<E::Principal, E::Action, E::Resource>;
        open(crate) spec fn view(&self) -> Self::V {
            analyzer::AnalyzerView {
                domains: semantics::DomainsView {
                    principal: match selected_values(self.constants, self.universes[0]) { None => None, Some(vs) => Some(principal_values::<E>(vs)) },
                    action: match selected_values(self.constants, self.universes[1]) { None => None, Some(vs) => Some(action_values::<E>(vs)) },
                    resource: match selected_values(self.constants, self.universes[2]) { None => None, Some(vs) => Some(resource_values::<E>(vs)) },
                },
                rules: Seq::empty(),
                known_principals: principal_values::<E>(self.constants.values@.to_set()),
                known_actions: action_values::<E>(self.constants.values@.to_set()),
                known_resources: resource_values::<E>(self.constants.values@.to_set()),
            }
        }
    }

    pub(crate) open spec fn universes_wf<E: Event>(c: Constants<E>, us: Universes) -> bool {
        forall|f: int| #![trigger us[f]] 0 <= f < 3 ==> match us[f] { None => true, Some(ids) => (*ids)@.no_duplicates()
            && forall|j: int| 0 <= j < (*ids)@.len() ==> 0 < (*ids)@[j] <= c.values@.len()
                && value_field(c.values@[(*ids)@[j] as int - 1]) == enc::field_at(f) }
    }

    /// Constant-book and declared-universe invariants preserved by analyzer queries.
    pub open(crate) spec fn analyzer_state_wf<E: Event>(a: PolicyAnalyzer<E>) -> bool {
        constants_wf(a.constants) && universes_wf(a.constants, a.universes)
    }

    pub(crate) proof fn lemma_universes_frame<E: Event>(a: Constants<E>, b: Constants<E>, us: Universes)
        requires constants_frame(a, b), universes_wf(a, us),
        ensures universes_wf(b, us), selected_values(a, us[0]) == selected_values(b, us[0]),
            selected_values(a, us[1]) == selected_values(b, us[1]), selected_values(a, us[2]) == selected_values(b, us[2]),
    {
        assert forall|f: int| 0 <= f < 3 implies selected_values(a, us[f]) == selected_values(b, us[f]) by {
            if let Some(ids) = us[f] {
                super::lemma_set_map_equal((*ids)@.to_set(), |id: u32| a.values@[id as int - 1], |id: u32| b.values@[id as int - 1]);
            }
        }
    }


    pub closed spec fn constructor_result<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>) -> bool {
        constants_wf(a.constants) && a.constants.values@.len() <= option_len(d.principals) + option_len(d.actions) + option_len(d.resources)
            && declared_domains_encoded(a, d) && analyzer_state_wf(a) && analyzer::analyzer_wf(a@)
            && declared_domain_equivalence(a, d)
    }


    pub(crate) proof fn lemma_constructor_contract<E: Event>()
        ensures forall|d: Domains<E>| #[trigger] constructor_capacity(d)
            == (option_len(d.principals) + option_len(d.actions) + option_len(d.resources) <= u32::MAX),
            forall|a: PolicyAnalyzer<E>, d: Domains<E>| #[trigger] constructor_result(a, d)
            == (constants_wf(a.constants) && a.constants.values@.len() <= option_len(d.principals) + option_len(d.actions) + option_len(d.resources)
                && declared_domains_encoded(a, d) && analyzer_state_wf(a) && analyzer::analyzer_wf(a@) && declared_domain_equivalence(a, d)),
    {}

    pub(crate) proof fn lemma_declared_frame<E: Event, T>(a: Constants<E>, b: Constants<E>, u: Universe, vs: Option<Vec<T>>, f: spec_fn(T) -> ComponentValue<E>)
        requires constants_frame(a, b), declared_universe(a, u, vs, f),
        ensures declared_universe(b, u, vs, f),
    {
        if let (Some(ids), Some(values)) = (u, vs) { lemma_universe_frame(a, b, (*ids)@, values@.map_values(f)); }
    }

    pub(crate) proof fn lemma_declared_wf<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>)
        requires declared_domains_encoded(a, d),
        ensures universes_wf(a.constants, a.universes), analyzer::analyzer_wf(a@),
    {
        assert forall|f: int| #![trigger a.universes[f]] 0 <= f < 3 implies match a.universes[f] {
            None => true, Some(ids) => (*ids)@.no_duplicates() && forall|j: int| 0 <= j < (*ids)@.len()
                ==> 0 < (*ids)@[j] <= a.constants.values@.len()
                    && value_field(a.constants.values@[(*ids)@[j] as int - 1]) == enc::field_at(f)
        } by {
            if f == 0 {} else if f == 1 {} else {}
            if let Some(ids) = a.universes[f] {
                assert forall|j: int| 0 <= j < (*ids)@.len() implies
                    0 < (*ids)@[j] <= a.constants.values@.len()
                        && value_field(a.constants.values@[(*ids)@[j] as int - 1]) == enc::field_at(f) by {
                    if f == 0 {
                        let values = match d.principals { Some(vs) => vs@, _ => arbitrary() };
                        let tagged = values.map_values(|v: E::Principal| ComponentValue::<E>::Principal(v));
                        assert(universe_id(a.constants, tagged, (*ids)@[j]));
                        let k = choose|k: int| 0 <= k < tagged.len() && stored_code(a.constants, tagged[k], (*ids)@[j]);
                        assert(tagged[k] == ComponentValue::<E>::Principal(values[k]));
                        match a.constants.values@[(*ids)@[j] as int - 1] { ComponentValue::Principal(_) => {}, _ => {} }
                    } else if f == 1 {
                        let values = match d.actions { Some(vs) => vs@, _ => arbitrary() };
                        let tagged = values.map_values(|v: E::Action| ComponentValue::<E>::Action(v));
                        assert(universe_id(a.constants, tagged, (*ids)@[j]));
                        let k = choose|k: int| 0 <= k < tagged.len() && stored_code(a.constants, tagged[k], (*ids)@[j]);
                        assert(tagged[k] == ComponentValue::<E>::Action(values[k]));
                        match a.constants.values@[(*ids)@[j] as int - 1] { ComponentValue::Action(_) => {}, _ => {} }
                    } else {
                        let values = match d.resources { Some(vs) => vs@, _ => arbitrary() };
                        let tagged = values.map_values(|v: E::Resource| ComponentValue::<E>::Resource(v));
                        assert(universe_id(a.constants, tagged, (*ids)@[j]));
                        let k = choose|k: int| 0 <= k < tagged.len() && stored_code(a.constants, tagged[k], (*ids)@[j]);
                        assert(tagged[k] == ComponentValue::<E>::Resource(values[k]));
                        match a.constants.values@[(*ids)@[j] as int - 1] { ComponentValue::Resource(_) => {}, _ => {} }
                    }
                }
            }
        }
    }

    impl<E: Event> View for Domains<E> {
        type V = semantics::DomainsView<E::Principal, E::Action, E::Resource>;
        open(crate) spec fn view(&self) -> Self::V {
            semantics::DomainsView {
                principal: match self.principals { None => None, Some(vs) => Some(vs@.to_set()) },
                action: match self.actions { None => None, Some(vs) => Some(vs@.to_set()) },
                resource: match self.resources { None => None, Some(vs) => Some(vs@.to_set()) },
            }
        }
    }

    pub(crate) proof fn lemma_empty_constants<E: Event>(c: Constants<E>)
        requires c.values@ == Seq::<ComponentValue<E>>::empty(), crate::native::representatives(c.ids) == Seq::<(ComponentValue<E>, u32)>::empty(),
        ensures constants_wf(c),
    {
        assert(c.values@.map(|i: int, v: ComponentValue<E>| (v, (i + 1) as u32)) =~= Seq::<(ComponentValue<E>, u32)>::empty());
    }

    pub(crate) proof fn lemma_universe_empty<E: Event>(c: Constants<E>)
        ensures universe_encoded(c, Seq::<u32>::empty(), Seq::<ComponentValue<E>>::empty()),
    {}

    pub(crate) proof fn lemma_universe_step<E: Event>(c: Constants<E>, ids: Seq<u32>, next: Seq<u32>, vs: Seq<ComponentValue<E>>, v: ComponentValue<E>, id: u32)
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

    proof fn lemma_book_length<E: Event>(values: Seq<ComponentValue<E>>)
        ensures field_entries(values, Component::Principal).len() + field_entries(values, Component::Action).len()
            + field_entries(values, Component::Resource).len() == values.len(),
        decreases values.len(),
    {
        if values.len() > 0 {
            let prior = values.drop_last();
            lemma_book_length(prior);
            let last = values.last();
            let entry = (last, values.len() as u64);
            assert(entries(values) =~= entries(prior).push(entry));
            entries(prior).lemma_filter_len_push(|p: (ComponentValue<E>, u64)| value_field(p.0) == Component::Principal, entry);
            entries(prior).lemma_filter_len_push(|p: (ComponentValue<E>, u64)| value_field(p.0) == Component::Action, entry);
            entries(prior).lemma_filter_len_push(|p: (ComponentValue<E>, u64)| value_field(p.0) == Component::Resource, entry);
            match last { ComponentValue::Principal(_) => {}, ComponentValue::Action(_) => {}, ComponentValue::Resource(_) => {} }
        } else {
            reveal(Seq::filter);
        }
    }

    pub(crate) proof fn lemma_constant_book_length<E: Event>(c: Constants<E>)
        ensures constant_book(c)[0].len() + constant_book(c)[1].len() + constant_book(c)[2].len() == c.values@.len(),
    {
        lemma_field_book(c, Component::Principal);
        lemma_field_book(c, Component::Action);
        lemma_field_book(c, Component::Resource);
        lemma_book_length(c.values@);
    }

    pub(crate) open spec fn tagged_codes<E: Event, T>(c: Constants<E>, u: Universe, domain: Option<Set<T>>, tag: spec_fn(T) -> ComponentValue<E>) -> bool {
        match (u, domain) {
            (None, None) => true,
            (Some(ids), Some(values)) => {
                &&& forall|x: T| #[trigger] values.contains(x)
                    == (exists|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == tag(x))
            },
            _ => false,
        }
    }

    proof fn lemma_native_sym<E: Event>(a: ComponentValue<E>, b: ComponentValue<E>)
        requires analyzer_obligations::<E>(),
        ensures a.eq_spec(&b) == b.eq_spec(&a),
    {}

    proof fn lemma_native_trans<E: Event>(a: ComponentValue<E>, b: ComponentValue<E>, c: ComponentValue<E>)
        requires analyzer_obligations::<E>(), a.eq_spec(&b), b.eq_spec(&c),
        ensures a.eq_spec(&c),
    {}

    proof fn lemma_declared_domain<E: Event, T: PartialEq>(c: Constants<E>, u: Universe, raw: Option<Vec<T>>, domain: Option<Set<T>>, tag: spec_fn(T) -> ComponentValue<E>, project: spec_fn(ComponentValue<E>) -> T)
        requires analyzer_obligations::<E>(), declared_universe(c, u, raw, tag), tagged_codes(c, u, domain, tag),
            forall|x: T, y: T| #[trigger] tag(x).eq_spec(&tag(y)) == x.eq_spec(&y),
            u matches Some(ids) ==> forall|i: int| #![trigger (*ids)@[i]] 0 <= i < (*ids)@.len()
                ==> tag(project(c.values@[(*ids)@[i] as int - 1])) == c.values@[(*ids)@[i] as int - 1],
        ensures forall|x: T| #[trigger] semantics::in_domain(domain, x)
            == semantics::in_domain(match raw { None => None, Some(vs) => Some(vs@.to_set()) }, x),
    {
        hide(analyzer_obligations);
        if let (Some(ids), Some(vs), Some(values)) = (u, raw, domain) {
            assert forall|x: T| semantics::in_domain(domain, x) implies semantics::in_domain(Some(vs@.to_set()), x) by {
                let y = choose|y: T| values.contains(y) && x.eq_spec(&y);
                let i = choose|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == tag(y);
                assert(universe_id(c, vs@.map_values(tag), (*ids)@[i]));
                let j = choose|j: int| 0 <= j < vs@.map_values(tag).len() && stored_code(c, vs@.map_values(tag)[j], (*ids)@[i]);
                assert(vs@.map_values(tag)[j] == tag(vs@[j]));
                assert(tag(x).eq_spec(&tag(y)));
                assert(tag(vs@[j]).eq_spec(&tag(y)));
                lemma_native_sym(tag(y), tag(vs@[j]));
                lemma_native_trans(tag(x), tag(y), tag(vs@[j]));
                assert(x.eq_spec(&vs@[j]));
                assert(vs@.to_set().contains(vs@[j]));
            }
            assert forall|x: T| semantics::in_domain(Some(vs@.to_set()), x) implies semantics::in_domain(domain, x) by {
                let y = choose|y: T| vs@.to_set().contains(y) && x.eq_spec(&y);
                let j = choose|j: int| 0 <= j < vs@.len() && vs@[j] == y;
                assert(vs@.map_values(tag)[j] == tag(y));
                assert(universe_value(c, (*ids)@, tag(y)));
                let i = choose|i: int| 0 <= i < (*ids)@.len() && stored_code(c, tag(y), (*ids)@[i]);
                let rep = c.values@[(*ids)@[i] as int - 1];
                let z = project(rep);
                assert(values.contains(z));
                assert(tag(y).eq_spec(&tag(z)));
                assert(tag(x).eq_spec(&tag(y)));
                lemma_native_trans(tag(x), tag(y), tag(z));
                assert(x.eq_spec(&z));
            }
        }
    }

    pub(crate) open spec fn declared_domain_equivalence<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>) -> bool {
        &&& forall|x: E::Principal| #[trigger] semantics::in_domain(a@.domains.principal, x) == semantics::in_domain(d@.principal, x)
        &&& forall|x: E::Action| #[trigger] semantics::in_domain(a@.domains.action, x) == semantics::in_domain(d@.action, x)
        &&& forall|x: E::Resource| #[trigger] semantics::in_domain(a@.domains.resource, x) == semantics::in_domain(d@.resource, x)
    }

    proof fn lemma_tag_projection<E: Event, T>(values: Set<ComponentValue<E>>, tag: spec_fn(T) -> ComponentValue<E>, project: spec_fn(ComponentValue<E>) -> T, pred: spec_fn(ComponentValue<E>) -> bool)
        requires forall|x: T| #[trigger] project(tag(x)) == x && pred(tag(x)),
            forall|v: ComponentValue<E>| #[trigger] pred(v) ==> tag(project(v)) == v,
        ensures forall|x: T| #[trigger] values.filter(pred).map(project).contains(x) == values.contains(tag(x)),
    {
        assert forall|x: T| values.filter(pred).map(project).contains(x) implies values.contains(tag(x)) by {
            let v = choose|v: ComponentValue<E>| values.filter(pred).contains(v) && project(v) == x;
            assert(tag(x) == v);
        }
        assert forall|x: T| values.contains(tag(x)) implies values.filter(pred).map(project).contains(x) by {
            assert(project(tag(x)) == x);
            assert(pred(tag(x)));
            vstd::set::lemma_set_filter(values, pred, tag(x));
            assert(values.filter(pred).contains(tag(x)));
        }
    }

    pub(crate) open spec fn selected_code_values<E: Event>(c: Constants<E>, ids: Seq<u32>) -> Set<ComponentValue<E>> {
        ids.to_set().map(|id: u32| c.values@[id as int - 1])
    }

    proof fn lemma_selected_members<E: Event>(c: Constants<E>, ids: Seq<u32>)
        ensures forall|v: ComponentValue<E>| #[trigger] selected_code_values(c, ids).contains(v)
            == (exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v),
    {
        let selected = ids.to_set().map(|id: u32| c.values@[id as int - 1]);
        assert forall|v: ComponentValue<E>| selected.contains(v) implies exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v by {
            let id = choose|id: u32| ids.to_set().contains(id) && c.values@[id as int - 1] == v;
            let i = choose|i: int| 0 <= i < ids.len() && ids[i] == id;
            assert(c.values@[ids[i] as int - 1] == v);
        }
        assert forall|v: ComponentValue<E>| (exists|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v) implies selected.contains(v) by {
            let i = choose|i: int| 0 <= i < ids.len() && c.values@[ids[i] as int - 1] == v;
            assert(ids.to_set().contains(ids[i]));
            assert(selected.contains(c.values@[ids[i] as int - 1]));
        }
    }


    pub(crate) proof fn lemma_constructor_domains<E: Event>(a: PolicyAnalyzer<E>, d: Domains<E>)
        requires analyzer_obligations::<E>(), declared_domains_encoded(a, d), universes_wf(a.constants, a.universes),
        ensures declared_domain_equivalence(a, d),
    {
        if let Some(ids) = a.universes[0] {
            let values = (*ids)@.to_set().map(|id: u32| a.constants.values@[id as int - 1]);
            lemma_selected_members(a.constants, (*ids)@);
            lemma_tag_projection(values, |x: E::Principal| ComponentValue::<E>::Principal(x), |v: ComponentValue<E>| principal_of::<E>(v), |v: ComponentValue<E>| v is Principal);
            assert(a@.domains.principal == Some(principal_values::<E>(values)));
            assert(values == selected_code_values(a.constants, (*ids)@));
            assert forall|x: E::Principal| #[trigger] principal_values::<E>(values).contains(x) == values.contains(ComponentValue::<E>::Principal(x)) by {}
            assert forall|x: E::Principal| #[trigger] principal_values::<E>(values).contains(x)
                == (exists|i: int| 0 <= i < (*ids)@.len() && a.constants.values@[(*ids)@[i] as int - 1] == ComponentValue::<E>::Principal(x)) by {}
            assert(tagged_codes(a.constants, a.universes[0], a@.domains.principal, |x: E::Principal| ComponentValue::<E>::Principal(x)));
        }
        if let Some(ids) = a.universes[1] {
            let values = (*ids)@.to_set().map(|id: u32| a.constants.values@[id as int - 1]);
            lemma_selected_members(a.constants, (*ids)@);
            lemma_tag_projection(values, |x: E::Action| ComponentValue::<E>::Action(x), |v: ComponentValue<E>| action_of::<E>(v), |v: ComponentValue<E>| v is Action);
            assert(a@.domains.action == Some(action_values::<E>(values)));
            assert(values == selected_code_values(a.constants, (*ids)@));
            assert forall|x: E::Action| #[trigger] action_values::<E>(values).contains(x) == values.contains(ComponentValue::<E>::Action(x)) by {}
            assert forall|x: E::Action| #[trigger] action_values::<E>(values).contains(x)
                == (exists|i: int| 0 <= i < (*ids)@.len() && a.constants.values@[(*ids)@[i] as int - 1] == ComponentValue::<E>::Action(x)) by {}
            assert(tagged_codes(a.constants, a.universes[1], a@.domains.action, |x: E::Action| ComponentValue::<E>::Action(x)));
        }
        if let Some(ids) = a.universes[2] {
            let values = (*ids)@.to_set().map(|id: u32| a.constants.values@[id as int - 1]);
            lemma_selected_members(a.constants, (*ids)@);
            lemma_tag_projection(values, |x: E::Resource| ComponentValue::<E>::Resource(x), |v: ComponentValue<E>| resource_of::<E>(v), |v: ComponentValue<E>| v is Resource);
            assert(a@.domains.resource == Some(resource_values::<E>(values)));
            assert(values == selected_code_values(a.constants, (*ids)@));
            assert forall|x: E::Resource| #[trigger] resource_values::<E>(values).contains(x) == values.contains(ComponentValue::<E>::Resource(x)) by {}
            assert forall|x: E::Resource| #[trigger] resource_values::<E>(values).contains(x)
                == (exists|i: int| 0 <= i < (*ids)@.len() && a.constants.values@[(*ids)@[i] as int - 1] == ComponentValue::<E>::Resource(x)) by {}
            assert(tagged_codes(a.constants, a.universes[2], a@.domains.resource, |x: E::Resource| ComponentValue::<E>::Resource(x)));
        }
        assert(tagged_codes(a.constants, a.universes[0], a@.domains.principal, |x: E::Principal| ComponentValue::<E>::Principal(x)));
        assert(tagged_codes(a.constants, a.universes[1], a@.domains.action, |x: E::Action| ComponentValue::<E>::Action(x)));
        assert(tagged_codes(a.constants, a.universes[2], a@.domains.resource, |x: E::Resource| ComponentValue::<E>::Resource(x)));
        lemma_declared_domain(a.constants, a.universes[0], d.principals, a@.domains.principal, |x: E::Principal| ComponentValue::<E>::Principal(x), |v: ComponentValue<E>| principal_of::<E>(v));
        lemma_declared_domain(a.constants, a.universes[1], d.actions, a@.domains.action, |x: E::Action| ComponentValue::<E>::Action(x), |v: ComponentValue<E>| action_of::<E>(v));
        lemma_declared_domain(a.constants, a.universes[2], d.resources, a@.domains.resource, |x: E::Resource| ComponentValue::<E>::Resource(x), |v: ComponentValue<E>| resource_of::<E>(v));
    }

    pub(crate) proof fn lemma_empty_constructor_capacity<E: Event>()
        ensures constructor_capacity(Domains::<E> { principals: None, actions: None, resources: None }),
    {}

    pub(crate) proof fn lemma_query_capacity<E: Event>(a: PolicyAnalyzer<E>, left: history_syntax::RegexExpr<E>, right: history_syntax::RegexExpr<E>)
        requires query_capacity(a, left, right),
        ensures ({
            let count = a.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@);
            count <= u32::MAX && forall|v: [Set<nat>; 3]|
                v[0].len() <= count && v[1].len() <= count && v[2].len() <= count
                    ==> #[trigger] super::search_exec::resource_capacity(v)
        }),
    {
        let count = a.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@);
        let m = count + 2;
        assert forall|v: [Set<nat>; 3]| v[0].len() <= count && v[1].len() <= count && v[2].len() <= count
            implies #[trigger] super::search_exec::resource_capacity(v) by {
            let x = v[0].len() + 2; let y = v[1].len() + 2; let z = v[2].len() + 2;
            assert(m <= m * m * m && x * y <= m * m * m && x * y * z <= m * m * m) by(nonlinear_arith)
                requires x <= m, y <= m, z <= m, 2 <= x, 2 <= y, 2 <= z;
        }
    }

    /// `query_capacity` is not vacuous: on every word size it holds whenever the vocabulary bound is
    /// at most 1000 (the paper's running example needs about 40).
    pub(crate) proof fn lemma_query_capacity_nonvacuous<E: Event>(a: PolicyAnalyzer<E>,
        left: history_syntax::RegexExpr<E>, right: history_syntax::RegexExpr<E>)
        requires a.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@) <= 1000,
        ensures query_capacity(a, left, right),
    {
        let m = a.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@) + 2;
        assert(m * m * m <= 1002 * 1002 * 1002) by(nonlinear_arith)
            requires m <= 1002;
        assert(1002nat * 1002nat * 1002nat <= u32::MAX as nat) by(compute_only);
        assert(u32::MAX as nat <= usize::MAX as nat);
    }
    }
}
