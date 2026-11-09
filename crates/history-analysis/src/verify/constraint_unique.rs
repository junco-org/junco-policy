//! Ordered multiplicity facts for the executable constraint and letter generators.
use super::*;
use crate::constraint::{ClassChoices, RegisterChoices};

verus! {
pub(crate) open spec fn register_sequence(values: Seq<RegisterConstraint>) -> Seq<implementation::RegisterView> {
    values.map_values(|r: RegisterConstraint| r@)
}
pub(crate) open spec fn constraint_sequence(values: Seq<Constraint>) -> Seq<implementation::ConstraintView> {
    values.map_values(|g: Constraint| g@)
}
pub(crate) open spec fn letter_sequence(values: Seq<Letter>) -> Seq<implementation::LetterView> {
    values.map_values(|l: Letter| l@)
}
pub(crate) open spec fn class_sequence(values: Seq<Option<Class>>) -> Seq<Option<implementation::ClassView>> {
    values.map_values(|c: Option<Class>| class_option(c))
}
pub(crate) open spec fn universe_distinct(universe: Universe) -> bool {
    match universe { None => true, Some(values) => (*values)@.no_duplicates() }
}
pub(crate) open spec fn universes_distinct(universes: Universes) -> bool {
    universe_distinct(universes[0]) && universe_distinct(universes[1]) && universe_distinct(universes[2])
}

pub(crate) proof fn lemma_filter_distinct(values: Seq<u32>, p: spec_fn(u32) -> bool)
    requires values.no_duplicates(),
    ensures values.filter(p).no_duplicates(),
    decreases values.len(),
{
    if values.len() > 0 {
        let prior = values.drop_last();
        assert(prior.no_duplicates());
        lemma_filter_distinct(prior, p);
        assert(prior.push(values.last()) =~= values);
        prior.lemma_filter_push(values.last(), p);
        if p(values.last()) {
            if prior.filter(p).contains(values.last()) {
                prior.lemma_filter_contains_rev(p, values.last());
                assert(prior.contains(values.last()));
            }
            assert(!prior.filter(p).contains(values.last()));
        }
    }
}
pub(crate) proof fn lemma_register_choices_distinct(c: RegisterChoices)
    requires c.equals.view().no_duplicates(),
        c.last matches Some(RegisterConstraint::Equals(v)) ==> !c.equals.view().contains(v),
    ensures register_sequence(c@).no_duplicates(),
{
    let ids = c.equals.view();
    assert forall|i: int, j: int| 0 <= i < j < c@.len()
        implies register_sequence(c@)[i] != register_sequence(c@)[j] by {
        if j < ids.len() { assert(ids[i] != ids[j]); }
        else {
            assert(c@[j] == c.last->Some_0);
            match c.last->Some_0 {
                RegisterConstraint::Equals(v) => { assert(ids.contains(ids[i])); assert(ids[i] != v); },
                RegisterConstraint::Differs(_) => {},
            }
        }
    }
}
pub(crate) proof fn lemma_class_option_injective(a: Option<Class>, b: Option<Class>)
    requires class_option(a) == class_option(b), ensures a == b,
{
    match (a, b) {
        (Some(Class::Constant(v)), Some(Class::Constant(w))) => {},
        (Some(Class::Register), Some(Class::Register)) => {},
        (None, None) => {}, _ => {},
    }
}
pub(crate) proof fn lemma_class_choices_distinct(c: ClassChoices)
    requires class_choices_wf(c), ensures class_sequence(c@).no_duplicates(),
{
    lemma_class_choices(c);
    assert forall|i: int, j: int| 0 <= i < j < c@.len()
        implies class_sequence(c@)[i] != class_sequence(c@)[j] by {
        if class_sequence(c@)[i] == class_sequence(c@)[j] {
            lemma_class_option_injective(c@[i], c@[j]);
            assert(c@[i] != c@[j]);
        }
    }
}

pub(crate) open spec fn row_position(n0: nat, n1: nat, n2: nat, n: int, p: (int, int, int)) -> bool {
    0 <= p.0 < n0 && 0 <= p.1 < n1 && 0 <= p.2 < n2
        && n == (p.0 * n1 + p.1) * n2 + p.2
}

pub(crate) open spec fn constraint_position(axes: [Seq<RegisterConstraint>; 3], g: implementation::ConstraintView, n: int) -> bool {
    exists|p: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, p)
        && g == choice_view(axes, p.0, p.1, p.2)
}

pub(crate) open spec fn letter_position(axes: [Seq<Option<Class>>; 3], registers: [Class; 3], l: implementation::LetterView, n: int) -> bool {
    exists|p: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, p)
        && l == letter_choice_view(axes, registers, p.0, p.1, p.2)
}

pub(crate) open spec fn constraint_positions(axes: [Seq<RegisterConstraint>; 3], values: Seq<Constraint>) -> bool {
    forall|n: int| #![trigger values[n]] 0 <= n < values.len() ==> constraint_position(axes, values[n]@, n)
}

pub(crate) open spec fn letter_positions(axes: [Seq<Option<Class>>; 3], registers: [Class; 3], values: Seq<Letter>) -> bool {
    forall|n: int| #![trigger values[n]] 0 <= n < values.len() ==> letter_position(axes, registers, values[n]@, n)
}

pub(crate) proof fn lemma_constraint_position_push(axes: [Seq<RegisterConstraint>; 3], before: Seq<Constraint>,
    added: Constraint, i: int, j: int, k: int)
    requires constraint_positions(axes, before),
        row_position(axes[0].len(), axes[1].len(), axes[2].len(), before.len() as int, (i, j, k)),
        added@ == choice_view(axes, i, j, k),
    ensures constraint_positions(axes, before.push(added)),
{
    let values = before.push(added);
    assert forall|n: int| #![trigger values[n]] 0 <= n < values.len() implies constraint_position(axes, values[n]@, n) by {
        if n < before.len() {
            assert(values[n] == before[n]);
            assert(constraint_position(axes, before[n]@, n));
        } else {
            assert(n == before.len());
            assert(row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, (i, j, k)));
            assert(constraint_position(axes, values[n]@, n));
        }
    }
}

pub(crate) proof fn lemma_letter_position_push(axes: [Seq<Option<Class>>; 3], registers: [Class; 3], before: Seq<Letter>,
    added: Letter, i: int, j: int, k: int)
    requires letter_positions(axes, registers, before),
        row_position(axes[0].len(), axes[1].len(), axes[2].len(), before.len() as int, (i, j, k)),
        added@ == letter_choice_view(axes, registers, i, j, k),
    ensures letter_positions(axes, registers, before.push(added)),
{
    let values = before.push(added);
    assert forall|n: int| #![trigger values[n]] 0 <= n < values.len() implies letter_position(axes, registers, values[n]@, n) by {
        if n < before.len() {
            assert(values[n] == before[n]);
            assert(letter_position(axes, registers, before[n]@, n));
        } else {
            assert(n == before.len());
            assert(row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, (i, j, k)));
            assert(letter_position(axes, registers, values[n]@, n));
        }
    }
}

pub(crate) proof fn lemma_constraint_product_distinct(axes: [Seq<RegisterConstraint>; 3], values: Seq<Constraint>)
    requires constraint_positions(axes, values),
        register_sequence(axes[0]).no_duplicates(), register_sequence(axes[1]).no_duplicates(), register_sequence(axes[2]).no_duplicates(),
    ensures constraint_sequence(values).no_duplicates(),
{
    assert forall|n: int, m: int| 0 <= n < m < values.len() implies values[n]@ != values[m]@ by {
        let p = choose|p: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, p)
            && values[n]@ == choice_view(axes, p.0, p.1, p.2);
        let q = choose|q: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), m, q)
            && values[m]@ == choice_view(axes, q.0, q.1, q.2);
        if values[n]@ == values[m]@ {
            assert(register_sequence(axes[0])[p.0] == register_sequence(axes[0])[q.0]);
            assert(register_sequence(axes[1])[p.1] == register_sequence(axes[1])[q.1]);
            assert(register_sequence(axes[2])[p.2] == register_sequence(axes[2])[q.2]);
            assert(p.0 == q.0); assert(p.1 == q.1); assert(p.2 == q.2);
        }
    }
}

pub(crate) proof fn lemma_letter_product_distinct(axes: [Seq<Option<Class>>; 3], registers: [Class; 3], values: Seq<Letter>)
    requires letter_positions(axes, registers, values),
        class_sequence(axes[0]).no_duplicates(), class_sequence(axes[1]).no_duplicates(), class_sequence(axes[2]).no_duplicates(),
    ensures letter_sequence(values).no_duplicates(),
{
    assert forall|n: int, m: int| 0 <= n < m < values.len() implies values[n]@ != values[m]@ by {
        let p = choose|p: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), n, p)
            && values[n]@ == letter_choice_view(axes, registers, p.0, p.1, p.2);
        let q = choose|q: (int, int, int)| row_position(axes[0].len(), axes[1].len(), axes[2].len(), m, q)
            && values[m]@ == letter_choice_view(axes, registers, q.0, q.1, q.2);
        if values[n]@ == values[m]@ {
            assert(class_sequence(axes[0])[p.0] == class_sequence(axes[0])[q.0]);
            assert(class_sequence(axes[1])[p.1] == class_sequence(axes[1])[q.1]);
            assert(class_sequence(axes[2])[p.2] == class_sequence(axes[2])[q.2]);
            assert(p.0 == q.0); assert(p.1 == q.1); assert(p.2 == q.2);
        }
    }
}

pub(crate) proof fn lemma_field_class_injective(r: implementation::RegisterView, register: bool, constants: Set<nat>,
    universe: Universe, a: Option<implementation::ClassView>, b: Option<implementation::ClassView>)
    requires class_options(r, register, constants, universe).contains(a), class_options(r, register, constants, universe).contains(b),
        forall|v: nat| constants.contains(v) ==> (a == Some(implementation::ClassView::Constant(v))) == (b == Some(implementation::ClassView::Constant(v))),
        register ==> (a == Some(register_class(r))) == (b == Some(register_class(r))),
    ensures a == b,
{
    lemma_class_options_members(r, register, constants, universe, a);
    lemma_class_options_members(r, register, constants, universe, b);
    let names = named_codes(r, register, constants, domain_view(universe));
    assert forall|v: nat| names.contains(v) implies
        (a == Some(implementation::ClassView::Constant(v))) == (b == Some(implementation::ClassView::Constant(v))) by {
        match r { implementation::RegisterView::Equals(w) => {}, implementation::RegisterView::Differs(_) => {} }
    }
    if a != b {
        match (a, b) {
            (Some(implementation::ClassView::Constant(v)), _) => {
                if names.contains(v) { assert(b == Some(implementation::ClassView::Constant(v))); }
                else { match b {
                    Some(implementation::ClassView::Constant(w)) => {
                        if names.contains(w) { assert(a == Some(implementation::ClassView::Constant(w))); }
                    },
                    Some(implementation::ClassView::Register) => {
                        assert(register && r is Differs);
                        assert(b == Some(register_class(r)));
                    },
                    None => { assert(universe is None); },
                } }
            },
            (_, Some(implementation::ClassView::Constant(w))) => {
                if names.contains(w) { assert(a == Some(implementation::ClassView::Constant(w))); }
                else { match a {
                    Some(implementation::ClassView::Register) => { assert(register && r is Differs); },
                    None => { assert(universe is None); }, _ => {},
                } }
            },
            (Some(implementation::ClassView::Register), None) => { assert(register && r is Differs); },
            (None, Some(implementation::ClassView::Register)) => { assert(register && r is Differs); },
            _ => {},
        }
    }
}

pub(crate) proof fn lemma_letter_assignment_injective(g: Constraint, operands: Operands, atoms: Seq<Atom>, universes: Universes,
    a: implementation::LetterView, b: implementation::LetterView)
    requires atoms_wf(atoms), operands_of(operands, atoms),
        letters_views(g, operands, universes).contains(a), letters_views(g, operands, universes).contains(b),
        implementation::letter_assignment(a, atom_set(atoms)) == implementation::letter_assignment(b, atom_set(atoms)),
    ensures a == b,
{
    lemma_letters_members(g, operands, universes); lemma_operand_atoms(operands, atoms);
    assert forall|c: Component| implementation::letter_class(a, c) == implementation::letter_class(b, c) by {
        let k = component_index(c) as int;
        let av = implementation::letter_class(a, c); let bv = implementation::letter_class(b, c);
        assert(implementation::letter_register(a, c) == register_class(implementation::register_of(g@, c)));
        assert(implementation::letter_register(b, c) == register_class(implementation::register_of(g@, c)));
        assert forall|v: nat| codes(operands.constants[k].view()).contains(v) implies
            (av == Some(implementation::ClassView::Constant(v))) == (bv == Some(implementation::ClassView::Constant(v))) by {
            let p = model::Primitive::Eq(c, model::GTerm::Constant(v));
            assert(atom_set(atoms).contains(p));
            assert(implementation::letter_assignment(a, atom_set(atoms))[p] == implementation::letter_assignment(b, atom_set(atoms))[p]);
            assert(implementation::letter_assignment(a, atom_set(atoms)).dom().contains(p));
            assert(implementation::letter_assignment(a, atom_set(atoms))[p] == implementation::letter_holds(a, p));
            assert(implementation::letter_assignment(b, atom_set(atoms))[p] == implementation::letter_holds(b, p));
        }
        if operands.register[k] {
            let p = model::Primitive::Eq(c, model::GTerm::Variable(c));
            assert(atom_set(atoms).contains(p));
            assert(implementation::letter_assignment(a, atom_set(atoms))[p] == implementation::letter_assignment(b, atom_set(atoms))[p]);
            assert(implementation::letter_assignment(a, atom_set(atoms)).dom().contains(p));
            assert(implementation::letter_assignment(a, atom_set(atoms))[p] == implementation::letter_holds(a, p));
            assert(implementation::letter_assignment(b, atom_set(atoms))[p] == implementation::letter_holds(b, p));
        }
        lemma_field_class_injective(implementation::register_of(g@, c), operands.register[k], codes(operands.constants[k].view()), universes[k], av, bv);
    }
    assert(implementation::letter_class(a, Component::Principal) == implementation::letter_class(b, Component::Principal));
    assert(implementation::letter_class(a, Component::Action) == implementation::letter_class(b, Component::Action));
    assert(implementation::letter_class(a, Component::Resource) == implementation::letter_class(b, Component::Resource));
    assert(implementation::letter_register(a, Component::Principal) == implementation::letter_register(b, Component::Principal));
    assert(implementation::letter_register(a, Component::Action) == implementation::letter_register(b, Component::Action));
    assert(implementation::letter_register(a, Component::Resource) == implementation::letter_register(b, Component::Resource));
}

pub(crate) open spec fn letter_alpha_unique(g: Constraint, operands: Operands, universes: Universes, values: Seq<Letter>) -> bool {
    forall|atoms: Seq<Atom>| atoms_wf(atoms) && operands_of(operands, atoms) ==>
        values.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates()
}
pub(crate) proof fn lemma_letter_alpha_unique(g: Constraint, operands: Operands, universes: Universes, values: Seq<Letter>)
    requires letter_sequence(values).no_duplicates(), letter_views(values) == letters_views(g, operands, universes),
    ensures letter_alpha_unique(g, operands, universes, values),
{
    assert forall|atoms: Seq<Atom>| atoms_wf(atoms) && operands_of(operands, atoms) implies
        values.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates() by {
        assert forall|i: int, j: int| 0 <= i < j < values.len() implies
            implementation::letter_assignment(values[i]@, atom_set(atoms)) != implementation::letter_assignment(values[j]@, atom_set(atoms)) by {
            lemma_letter_view_at(values, i); lemma_letter_view_at(values, j);
            if implementation::letter_assignment(values[i]@, atom_set(atoms)) == implementation::letter_assignment(values[j]@, atom_set(atoms)) {
                lemma_letter_assignment_injective(g, operands, atoms, universes, values[i]@, values[j]@);
                assert(letter_sequence(values)[i] != letter_sequence(values)[j]);
            }
        }
    }
}
pub(crate) proof fn lemma_letter_view_at(values: Seq<Letter>, index: int)
    requires 0 <= index < values.len(), ensures letter_views(values).contains(values[index]@), decreases values.len(),
{
    let prior = values.drop_last();
    assert(prior.push(values.last()) =~= values);
    lemma_letter_views_push(prior, values.last());
    if index < prior.len() { lemma_letter_view_at(prior, index); assert(prior[index] == values[index]); }
    else { assert(values[index] == values.last()); }
}
pub(crate) open spec fn steps_alphas_unique(g: Constraint, atoms: Seq<Atom>, universes: Universes, groups: Seq<(Constraint, Vec<Letter>)>) -> bool {
    forall|i: int| 0 <= i < groups.len() ==>
        groups[i].1@.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates()
}
pub(crate) proof fn lemma_steps_alphas_unique(g: Constraint, atoms: Seq<Atom>, universes: Universes, operands: Operands,
    groups: Seq<(Constraint, Vec<Letter>)>)
    requires atoms_wf(atoms), operands_of(operands, atoms),
        forall|i: int| 0 <= i < groups.len() ==> letter_alpha_unique(groups[i].0, operands, universes, groups[i].1@),
    ensures steps_alphas_unique(g, atoms, universes, groups),
{
    assert forall|i: int| 0 <= i < groups.len() implies
        groups[i].1@.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates() by {
        assert(letter_alpha_unique(groups[i].0, operands, universes, groups[i].1@));
    }
}
}
