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
    forall|i: int| 0 <= i < universes@.len() ==> universe_distinct(universes[i])
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

/// Prefix product; the last coordinate is the least-significant digit.
pub(crate) open spec fn product_size(sizes: Seq<nat>) -> nat
    decreases sizes.len(),
{
    if sizes.len() == 0 { 1 } else { product_size(sizes.drop_last()) * sizes.last() }
}

pub(crate) open spec fn row_valid(sizes: Seq<nat>, p: Seq<usize>) -> bool {
    p.len() == sizes.len() && forall|i: int| 0 <= i < sizes.len() ==> p[i] < sizes[i]
}

pub(crate) open spec fn row_rank(sizes: Seq<nat>, p: Seq<usize>) -> nat
    decreases sizes.len(),
{
    if sizes.len() == 0 { 0 } else {
        row_rank(sizes.drop_last(), p.drop_last()) * sizes.last() + p.last() as nat
    }
}

pub(crate) open spec fn row_position(sizes: Seq<nat>, n: int, p: Seq<usize>) -> bool {
    row_valid(sizes, p) && n == row_rank(sizes, p)
}

pub(crate) proof fn lemma_row_bound(sizes: Seq<nat>, p: Seq<usize>)
    requires row_valid(sizes, p),
    ensures row_rank(sizes, p) < product_size(sizes),
    decreases sizes.len(),
{
    if sizes.len() > 0 {
        lemma_row_bound(sizes.drop_last(), p.drop_last());
        assert(row_rank(sizes, p) < product_size(sizes)) by(nonlinear_arith)
            requires row_rank(sizes.drop_last(), p.drop_last()) < product_size(sizes.drop_last()),
                p.last() < sizes.last();
    }
}

pub(crate) proof fn lemma_row_zero(sizes: Seq<nat>, p: Seq<usize>)
    requires p.len() == sizes.len(), forall|i: int| 0 <= i < p.len() ==> p[i] == 0,
    ensures row_rank(sizes, p) == 0,
    decreases sizes.len(),
{
if sizes.len() > 0 {
    lemma_row_zero(sizes.drop_last(), p.drop_last());
    assert(p.last() == p[p.len() as int - 1]);
    assert(p.last() == 0);
    assert(row_rank(sizes, p) == 0 * sizes.last() + 0);
}
}

pub(crate) proof fn lemma_product_positive(sizes: Seq<nat>)
    ensures (product_size(sizes) > 0) == (forall|i: int| 0 <= i < sizes.len() ==> sizes[i] > 0),
    decreases sizes.len(),
{
    if sizes.len() > 0 {
let prior = sizes.drop_last();
let prefix_product = product_size(prior);
let last = sizes.last();
lemma_product_positive(prior);
assert(product_size(sizes) == prefix_product * last);
assert((prefix_product * last > 0) == (prefix_product > 0 && last > 0)) by(nonlinear_arith);
assert(last == sizes[sizes.len() as int - 1]);
if product_size(sizes) > 0 {
    assert forall|i: int| 0 <= i < sizes.len() implies sizes[i] > 0 by {
        if i < prior.len() { assert(prior[i] == sizes[i]); }
        else { assert(i == sizes.len() - 1); }
    }
} else if forall|i: int| 0 <= i < sizes.len() ==> sizes[i] > 0 {
    assert forall|i: int| 0 <= i < prior.len() implies prior[i] > 0 by {
        assert(prior[i] == sizes[i]);
    }
    assert(prefix_product > 0);
}
    }
}

pub(crate) proof fn lemma_row_max(sizes: Seq<nat>, p: Seq<usize>)
    requires row_valid(sizes, p), forall|i: int| 0 <= i < sizes.len() ==> p[i] + 1 == sizes[i],
    ensures row_rank(sizes, p) + 1 == product_size(sizes),
    decreases sizes.len(),
{
    if sizes.len() > 0 {
        lemma_row_max(sizes.drop_last(), p.drop_last());
        assert(row_rank(sizes, p) + 1 == product_size(sizes)) by(nonlinear_arith)
            requires row_rank(sizes.drop_last(), p.drop_last()) + 1 == product_size(sizes.drop_last()),
                p.last() + 1 == sizes.last();
    }
}

pub(crate) proof fn lemma_row_rank_injective(sizes: Seq<nat>, p: Seq<usize>, q: Seq<usize>)
    requires row_valid(sizes, p), row_valid(sizes, q), row_rank(sizes, p) == row_rank(sizes, q),
    ensures p == q,
    decreases sizes.len(),
{
    if sizes.len() > 0 {
        let pr = row_rank(sizes.drop_last(), p.drop_last());
        let qr = row_rank(sizes.drop_last(), q.drop_last());
        assert(pr == qr && p.last() == q.last()) by(nonlinear_arith)
            requires pr * sizes.last() + p.last() == qr * sizes.last() + q.last(),
                p.last() < sizes.last(), q.last() < sizes.last(), sizes.last() > 0;
        lemma_row_rank_injective(sizes.drop_last(), p.drop_last(), q.drop_last());
assert forall|i: int| 0 <= i < p.len() implies p[i] == q[i] by {
    if i < p.len() - 1 {
        assert(p[i] == p.drop_last()[i]);
        assert(q[i] == q.drop_last()[i]);
    } else {
        assert(p[i] == p.last());
        assert(q[i] == q.last());
    }
}
assert(p =~= q);
    } else { assert(p =~= q); }
}

pub(crate) proof fn lemma_row_successor(sizes: Seq<nat>, before: Seq<usize>, after: Seq<usize>, pivot: int)
    requires row_valid(sizes, before), after.len() == sizes.len(), 0 <= pivot < sizes.len(),
        before[pivot] + 1 < sizes[pivot], after[pivot] == before[pivot] + 1,
        forall|i: int| 0 <= i < pivot ==> after[i] == before[i],
        forall|i: int| pivot < i < sizes.len() ==> before[i] + 1 == sizes[i] && after[i] == 0,
    ensures row_valid(sizes, after), row_rank(sizes, after) == row_rank(sizes, before) + 1,
    decreases sizes.len(),
{
let last = sizes.len() as int - 1;
let base = sizes[last];
let before_prefix = row_rank(sizes.drop_last(), before.drop_last());
let after_prefix = row_rank(sizes.drop_last(), after.drop_last());
assert(sizes.last() == base);
assert(before.last() == before[last]);
assert(after.last() == after[last]);
assert(row_rank(sizes, before) == before_prefix * base + before[last]);
assert(row_rank(sizes, after) == after_prefix * base + after[last]);
if pivot == last {
    assert(after.drop_last() =~= before.drop_last());
    assert(after_prefix == before_prefix);
    assert(after[last] == before[last] + 1);
} else {
    lemma_row_successor(sizes.drop_last(), before.drop_last(), after.drop_last(), pivot);
    assert(after_prefix == before_prefix + 1);
    assert(after[last] == 0 && before[last] + 1 == base);
    assert(after_prefix * base + after[last] == before_prefix * base + before[last] + 1) by(nonlinear_arith)
        requires after_prefix == before_prefix + 1, after[last] == 0, before[last] + 1 == base;
}
assert forall|i: int| 0 <= i < sizes.len() implies after[i] < sizes[i] by {
    if i < pivot { assert(after[i] == before[i]); }
    else if i > pivot { assert(after[i] == 0 && before[i] + 1 == sizes[i]); }
}
}

pub(crate) open spec fn constraint_position(axes: Seq<Seq<RegisterConstraint>>, g: implementation::ConstraintView, n: int) -> bool {
    exists|p: Seq<usize>| row_position(axis_sizes(axes), n, p) && g == choice_view(axes, p)
}

pub(crate) open spec fn letter_position(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, l: implementation::LetterView, n: int) -> bool {
    exists|p: Seq<usize>| row_position(axis_sizes(axes), n, p) && l == letter_choice_view(axes, registers, p)
}

pub(crate) open spec fn constraint_positions(axes: Seq<Seq<RegisterConstraint>>, values: Seq<Constraint>) -> bool {
    forall|n: int| #![trigger values[n]] 0 <= n < values.len() ==> constraint_position(axes, values[n]@, n)
}

pub(crate) open spec fn letter_positions(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, values: Seq<Letter>) -> bool {
    forall|n: int| #![trigger values[n]] 0 <= n < values.len() ==> letter_position(axes, registers, values[n]@, n)
}

pub(crate) proof fn lemma_constraint_position_push(axes: Seq<Seq<RegisterConstraint>>, before: Seq<Constraint>, added: Constraint, p: Seq<usize>)
    requires constraint_positions(axes, before), row_position(axis_sizes(axes), before.len() as int, p), added@ == choice_view(axes, p),
    ensures constraint_positions(axes, before.push(added)),
{
    assert forall|n: int| 0 <= n < before.push(added).len() implies constraint_position(axes, before.push(added)[n]@, n) by {
        if n < before.len() { assert(before.push(added)[n] == before[n]); }
        else { assert(constraint_position(axes, added@, n)); }
    }
}

pub(crate) proof fn lemma_letter_position_push(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, before: Seq<Letter>, added: Letter, p: Seq<usize>)
    requires letter_positions(axes, registers, before), row_position(axis_sizes(axes), before.len() as int, p), added@ == letter_choice_view(axes, registers, p),
    ensures letter_positions(axes, registers, before.push(added)),
{
    assert forall|n: int| 0 <= n < before.push(added).len() implies letter_position(axes, registers, before.push(added)[n]@, n) by {
        if n < before.len() { assert(before.push(added)[n] == before[n]); }
        else { assert(letter_position(axes, registers, added@, n)); }
    }
}

pub(crate) proof fn lemma_constraint_product_distinct(axes: Seq<Seq<RegisterConstraint>>, values: Seq<Constraint>)
    requires constraint_positions(axes, values), forall|i: int| 0 <= i < axes.len() ==> register_sequence(axes[i]).no_duplicates(),
    ensures constraint_sequence(values).no_duplicates(),
{
    assert forall|n: int, m: int| 0 <= n < m < values.len() implies values[n]@ != values[m]@ by {
        let p = choose|p: Seq<usize>| row_position(axis_sizes(axes), n, p) && values[n]@ == choice_view(axes, p);
        let q = choose|q: Seq<usize>| row_position(axis_sizes(axes), m, q) && values[m]@ == choice_view(axes, q);
        if values[n]@ == values[m]@ {
            assert forall|i: int| 0 <= i < axes.len() implies p[i] == q[i] by {
assert(p[i] < axes[i].len() && q[i] < axes[i].len());
assert(choice_view(axes, p)[i] == axes[i][p[i] as int]@);
assert(choice_view(axes, q)[i] == axes[i][q[i] as int]@);
assert(values[n]@[i] == choice_view(axes, p)[i]);
assert(values[m]@[i] == choice_view(axes, q)[i]);
assert(register_sequence(axes[i])[p[i] as int] == axes[i][p[i] as int]@);
assert(register_sequence(axes[i])[q[i] as int] == axes[i][q[i] as int]@);
assert(register_sequence(axes[i])[p[i] as int] == register_sequence(axes[i])[q[i] as int]);
            }
            assert(p =~= q);
        }
    }
}

pub(crate) proof fn lemma_letter_product_distinct(axes: Seq<Seq<Option<Class>>>, registers: Seq<Class>, values: Seq<Letter>)
    requires letter_positions(axes, registers, values), forall|i: int| 0 <= i < axes.len() ==> class_sequence(axes[i]).no_duplicates(),
    ensures letter_sequence(values).no_duplicates(),
{
    assert forall|n: int, m: int| 0 <= n < m < values.len() implies values[n]@ != values[m]@ by {
        let p = choose|p: Seq<usize>| row_position(axis_sizes(axes), n, p) && values[n]@ == letter_choice_view(axes, registers, p);
        let q = choose|q: Seq<usize>| row_position(axis_sizes(axes), m, q) && values[m]@ == letter_choice_view(axes, registers, q);
        if values[n]@ == values[m]@ {
            assert forall|i: int| 0 <= i < axes.len() implies p[i] == q[i] by {
assert(p[i] < axes[i].len() && q[i] < axes[i].len());
assert(letter_choice_view(axes, registers, p).classes[i] == class_option(axes[i][p[i] as int]));
assert(letter_choice_view(axes, registers, q).classes[i] == class_option(axes[i][q[i] as int]));
assert(values[n]@.classes[i] == letter_choice_view(axes, registers, p).classes[i]);
assert(values[m]@.classes[i] == letter_choice_view(axes, registers, q).classes[i]);
assert(class_sequence(axes[i])[p[i] as int] == class_option(axes[i][p[i] as int]));
assert(class_sequence(axes[i])[q[i] as int] == class_option(axes[i][q[i] as int]));
assert(class_sequence(axes[i])[p[i] as int] == class_sequence(axes[i])[q[i] as int]);
            }
            assert(p =~= q);
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
    requires shape_wf(g, operands, universes), operands_of(operands, atoms),
        letters_views(g, operands, universes).contains(a), letters_views(g, operands, universes).contains(b),
        implementation::letter_assignment(a, atom_set(atoms)) == implementation::letter_assignment(b, atom_set(atoms)),
    ensures a == b,
{
    lemma_letters_members(g, operands, universes); lemma_operand_atoms(operands, atoms);
    assert forall|i: int| 0 <= i < g@.len() implies a.classes[i] == b.classes[i] by {
        let c = Component(i as u8);
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
    assert(a.classes =~= b.classes);
    assert(a.registers =~= b.registers);
}

pub(crate) open spec fn letter_alpha_unique(g: Constraint, operands: Operands, universes: Universes, values: Seq<Letter>) -> bool {
    forall|atoms: Seq<Atom>| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms) ==>
        values.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates()
}
pub(crate) proof fn lemma_letter_alpha_unique(g: Constraint, operands: Operands, universes: Universes, values: Seq<Letter>)
    requires shape_wf(g, operands, universes), letter_sequence(values).no_duplicates(), letter_views(values) == letters_views(g, operands, universes),
    ensures letter_alpha_unique(g, operands, universes, values),
{
    assert forall|atoms: Seq<Atom>| atoms_wf(atoms, universes@.len()) && operands_of(operands, atoms) implies
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
    requires atoms_wf(atoms, universes@.len()), operands_of(operands, atoms), operands.register@.len() == universes@.len(),
        forall|i: int| 0 <= i < groups.len() ==> letter_alpha_unique(groups[i].0, operands, universes, groups[i].1@),
    ensures steps_alphas_unique(g, atoms, universes, groups),
{
    assert forall|i: int| 0 <= i < groups.len() implies
        groups[i].1@.map_values(|l: Letter| implementation::letter_assignment(l@, atom_set(atoms))).no_duplicates() by {
        assert(letter_alpha_unique(groups[i].0, operands, universes, groups[i].1@));
    }
}
}
