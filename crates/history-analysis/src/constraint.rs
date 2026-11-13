//! Constraints on the candidate, their splits, and letters: the finite alphabet of the search.
//!
//! A constraint records what is known about each register `κ_c`, the candidate's value of
//! component `c`. Splitting refines a constraint until it decides every comparison between a
//! register and a constant that a set of atoms makes; a register of a finite domain is fixed to
//! one value instead. Relative to such a constraint, a letter names one class of events that no
//! atom of the set can tell apart: for each component, the operand it equals, or none of them.

#[cfg(verus_keep_ghost)]
use self::equality::{constraint_key, register_key};
use crate::native::NativeMap;
#[cfg(verus_keep_ghost)]
use crate::verify::constraint_unique::*;
#[cfg(verus_keep_ghost)]
use crate::verify::*;
use alloc::rc::Rc;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::{encoding, implementation, inclusion};
use junco_core::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
use smallvec::SmallVec;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
// `ConstId` (`u32`) is sorted and binary-searched; vstd proves its order laws.
#[cfg(verus_keep_ghost)]
verus! { broadcast use vstd::laws_cmp::group_laws_cmp; }

/// Number of event components, and so of registers.
#[verus_verify]
pub(crate) const COMPONENTS: usize = 3;

/// Identity of an interned constant; constants of different components never share one.
pub(crate) type ConstId = u32;

/// The declared values of one component, in declaration order, or `None` if it is infinite.
pub(crate) type Universe = Option<Rc<Vec<ConstId>>>;

/// The universe of each component.
pub(crate) type Universes = [Universe; COMPONENTS];

/// Operand an atom compares its component with.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Operand {
    /// The candidate's value of the same component.
    Register,
    /// A constant of the component.
    Constant(ConstId),
}

/// Equality between one component of an event and an operand.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Atom {
    /// Index of the compared component.
    pub(crate) component: usize,
    /// The operand it is compared with.
    pub(crate) operand: Operand,
}

/// What a constraint states about one register.
// The verified `eq` compares the variant and its ids in order, exactly what the derived `Hash`
// hashes, so the two agree.
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, Eq, Hash)]
pub(crate) enum RegisterConstraint {
    /// The register equals this constant.
    Equals(ConstId),
    /// The register differs from every listed constant (sorted and deduplicated).
    Differs(SmallVec<[ConstId; 2]>),
}

#[verus_verify]
impl RegisterConstraint {
    #[verus_spec(result => ensures register_wf(result), result@ == match constant {
        Some(v) => implementation::RegisterView::Equals(v as nat),
        None => implementation::RegisterView::Differs(Set::empty()),
    })]
    fn head(constant: Option<ConstId>) -> Self {
        match constant {
            Some(v) => Self::Equals(v),
            None => {
                let empty = SmallVec::new();
                proof! { lemma_codes(empty.view()); assert(codes(empty.view()) =~= Set::<nat>::empty()); }
                Self::Differs(empty)
            }
        }
    }
    #[verus_spec(result => ensures result == (self@ == implementation::RegisterView::Equals(value as nat)))]
    fn entails_equal(&self, value: ConstId) -> bool {
        matches!(self, Self::Equals(equal) if *equal == value)
    }

    #[verus_spec(result => requires register_wf(*self),
        ensures result == !register_sat(self@, value as nat))]
    fn entails_differ(&self, value: ConstId) -> bool {
        match self {
            Self::Equals(equal) => *equal != value,
            Self::Differs(differs) => {
                proof! {
                    assert(junco_core::verify::history_assumptions::strictly_sorted(differs.view()));
                    lemma_codes(differs.view());
                }
                let slice: &[ConstId] = differs;
                let found = slice.binary_search(&value);
                proof! {
                    if found is Ok {
                        assert(differs.view().contains(value));
                    }
                }
                found.is_ok()
            }
        }
    }

    /// Whether the comparison between the register and `value` is settled.
    #[verus_spec(result => requires register_wf(*self),
        ensures result == (self@ is Equals || !register_sat(self@, value as nat)))]
    fn decides(&self, value: ConstId) -> bool {
        matches!(self, Self::Equals(_)) || self.entails_differ(value)
    }

    #[verus_spec(result => requires register_wf(*self), register_wf(*other),
        ensures result == register_entails(self@, other@))]
    fn entails(&self, other: &Self) -> bool {
        match other {
            Self::Equals(value) => self.entails_equal(*value),
            Self::Differs(values) => {
                let slice: &[ConstId] = values;
                proof! { lemma_codes(values.view()); }
                let mut index = 0;
                #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                    index <= slice@.len(), slice@ == values.view(), register_wf(*self),
                    other@ == implementation::RegisterView::Differs(codes(values.view())),
                    forall|i: int| 0 <= i < index ==> !register_sat(self@, slice@[i] as nat),
                    decreases slice@.len() - index))]
                while index < slice.len() {
                    let value = slice[index];
                    if !self.entails_differ(value) {
                        proof! {
                            lemma_codes(values.view());
                            assert(codes(values.view()).contains(value as nat));
                            if register_entails(self@, other@) {
                                lemma_register_entails_point(self@, codes(values.view()), value as nat);
                            }
                        }
                        return false;
                    }
                    index += 1;
                }
                true
            }
        }
    }

    /// Whether some value of `universe` satisfies the constraint.
    #[verus_spec(result => requires register_wf(*self),
        ensures result == match domain_view(*universe) {
            None => true, Some(vs) => exists|v: nat| vs.contains(v) && register_sat(self@, v) })]
    fn satisfiable(&self, universe: &Universe) -> bool {
        match universe {
            None => true,
            Some(values) => {
                let slice: &[ConstId] = values;
                proof! { lemma_codes(slice@); }
                self.witness(slice).is_some()
            }
        }
    }

    /// The first value of a finite `universe` that satisfies the constraint.
    #[verus_spec(result => requires register_wf(*self),
        ensures match result {
            Some(v) => universe@.contains(v) && register_sat(self@, v as nat)
                && exists|i: int| 0 <= i < universe@.len() && universe@[i] == v
                    && forall|j: int| 0 <= j < i ==> !register_sat(self@, universe@[j] as nat),
            None => forall|i: int| 0 <= i < universe@.len()
                ==> !register_sat(self@, universe@[i] as nat),
        })]
    pub(crate) fn witness(&self, universe: &[ConstId]) -> Option<ConstId> {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= universe@.len(), register_wf(*self),
            forall|i: int| 0 <= i < index ==> !register_sat(self@, universe@[i] as nat),
            decreases universe@.len() - index))]
        while index < universe.len() {
            let value = universe[index];
            if !self.entails_differ(value) {
                return Some(value);
            }
            index += 1;
        }
        None
    }

    #[verus_spec(result => ensures result@ == self@, register_key(result) == register_key(*self),
        register_wf(result) == register_wf(*self))]
    pub(crate) fn copy(&self) -> Self {
        match self {
            Self::Equals(value) => Self::Equals(*value),
            Self::Differs(values) => {
                let mut copied = SmallVec::new();
                copied.extend_from_slice(values);
                Self::Differs(copied)
            }
        }
    }
}

/// Satisfiable conjunction of register literals, one entry per component.
// The verified `eq` compares the three registers in order, as the derived `Hash` hashes them.
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, Eq, Hash)]
pub(crate) struct Constraint(pub(crate) [RegisterConstraint; COMPONENTS]);

#[verus_verify]
impl Constraint {
    /// The constraint fixing the registers that head constants pin, or `None` if some register
    /// can take no value of its universe.
    #[verus_spec(result => ensures match result {
        Some(c) => constraint_wf(c)
            && (forall|i: int| 0 <= i < 3 ==> c.0[i]@ == match constants[i] {
                Some(v) => implementation::RegisterView::Equals(v as nat),
                None => implementation::RegisterView::Differs(Set::empty()),
            })
            && implementation::constraint_of(c@) == inclusion::head_constraint(head_view(constants))
            && inclusion::satisfiable(ndomains(*universes), implementation::constraint_of(c@)),
        None => !inclusion::satisfiable(ndomains(*universes), inclusion::head_constraint(head_view(constants))),
    })]
    pub(crate) fn head(
        constants: [Option<ConstId>; COMPONENTS],
        universes: &Universes,
    ) -> Option<Self> {
        let first = RegisterConstraint::head(constants[0]);
        let second = RegisterConstraint::head(constants[1]);
        let third = RegisterConstraint::head(constants[2]);
        let constraint = Self([first, second, third]);
        proof! {
            lemma_head_view(constraint, constants);
            lemma_constraint_possible(constraint, *universes);
        }
        if constraint.0[0].satisfiable(&universes[0])
            && constraint.0[1].satisfiable(&universes[1])
            && constraint.0[2].satisfiable(&universes[2])
        {
            Some(constraint)
        } else {
            None
        }
    }

    /// Whether every valuation satisfying `self` satisfies `other`, read syntactically.
    #[verus_spec(result => requires constraint_wf(*self), constraint_wf(*other),
        ensures result ==> forall|d: encoding::NDomains|
            inclusion::entails(d, implementation::constraint_of(self@), implementation::constraint_of(other@)))]
    pub(crate) fn entails(&self, other: &Self) -> bool {
        let result = self.0[0].entails(&other.0[0])
            && self.0[1].entails(&other.0[1])
            && self.0[2].entails(&other.0[2]);
        proof! { if result { lemma_constraint_entails(self@, other@); } }
        result
    }

    #[verus_spec(result => ensures result@ == self@, constraint_key(result) == constraint_key(*self),
        constraint_wf(result) == constraint_wf(*self))]
    pub(crate) fn copy(&self) -> Self {
        Self([self.0[0].copy(), self.0[1].copy(), self.0[2].copy()])
    }
}

/// Index of an interned constraint.
pub(crate) type ConstraintId = u32;

/// Interned constraints, local to one search.
#[verus_verify]
pub(crate) struct ConstraintTable {
    pub(crate) constraints: Vec<Constraint>,
    pub(crate) ids: NativeMap<Constraint, ConstraintId>,
}

#[verus_verify]
impl ConstraintTable {
    #[verus_spec(result => ensures table_wf(result), result@.len() == 0)]
    pub(crate) fn new() -> Self {
        Self {
            constraints: Vec::new(),
            ids: NativeMap::new(),
        }
    }

    #[verus_spec(result => requires table_wf(*old(self)), constraint_wf(constraint),
        crate::native::key_obligations::<Constraint>(),
        ensures table_wf(*final(self)),
            junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(id) ==> id < final(self).constraints@.len()
                && constraint_key(final(self).constraints@[id as int]) == constraint_key(constraint),
            old(self)@.is_prefix_of(final(self)@),
            final(self)@.len() <= old(self)@.len() + 1,
            forall|i: int| old(self)@.len() <= i < final(self)@.len()
                ==> final(self)@[i] == constraint@,
            forall|i: int| 0 <= i < old(self).constraints@.len()
                ==> final(self).constraints@[i] == old(self).constraints@[i])]
    pub(crate) fn intern(&mut self, constraint: Constraint) -> Result<ConstraintId, HistoryError> {
        if let Some(id) = self.ids.lookup(&constraint) {
            return Ok(id);
        }
        let id = match ConstraintId::try_from(self.constraints.len()) {
            Ok(id) => id,
            Err(_) => {
                return Err(HistoryError::IdExhausted {
                    domain: "constraint",
                });
            }
        };
        self.constraints.push(constraint.copy());
        self.ids.insert_fresh(constraint, id);
        Ok(id)
    }

    #[verus_spec(result => requires table_wf(*self), id < self.constraints@.len(),
        ensures result@ == self@[id as int], constraint_wf(*result))]
    pub(crate) fn get(&self, id: ConstraintId) -> &Constraint {
        proof! { assert(constraint_wf(self.constraints@[id as int])); }
        &self.constraints[id as usize]
    }
}

/// Representative of a class of operands that a constraint makes equal.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Class {
    /// The class of a register that the constraint does not pin to a constant.
    Register,
    /// The class of a constant, possibly together with a register pinned to it.
    Constant(ConstId),
}

/// One class of events relative to a constraint and a set of atoms.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Letter {
    /// Class that each component equals, or `None` for any value outside the named classes.
    pub(crate) classes: [Option<Class>; COMPONENTS],
    /// Class of each register under the letter's constraint.
    pub(crate) registers: [Class; COMPONENTS],
}

#[verus_verify]
impl Letter {
    /// Whether events of this letter satisfy `atom`, which must belong to the atom set the letter
    /// was built for.
    #[verus_spec(result => requires atom.component < COMPONENTS,
        ensures result == implementation::letter_holds(self@, atom@))]
    pub(crate) fn holds(&self, atom: Atom) -> bool {
        let class = match atom.operand {
            Operand::Register => self.registers[atom.component],
            Operand::Constant(value) => Class::Constant(value),
        };
        match self.classes[atom.component] {
            None => false,
            Some(own) => match (own, class) {
                (Class::Register, Class::Register) => true,
                (Class::Constant(a), Class::Constant(b)) => a == b,
                _ => false,
            },
        }
    }

    /// Class that component `component` of the letter's events equals, if any.
    #[verus_spec(result => requires component < COMPONENTS,
        ensures class_option(result) == implementation::letter_class(self@, component_of(component)))]
    pub(crate) fn class(&self, component: usize) -> Option<Class> {
        self.classes[component]
    }
}

/// Operands that a set of atoms compares with each component.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Default)]
pub(crate) struct Operands {
    pub(crate) register: [bool; COMPONENTS],
    pub(crate) constants: [SmallVec<[ConstId; 4]>; COMPONENTS],
}

#[verus_verify]
impl Operands {
    /// Collects the operands of `atoms`.
    #[verus_spec(result => requires atoms_wf(atoms@),
        ensures operands_of(result, atoms@))]
    pub(crate) fn of(atoms: &[Atom]) -> Self {
        let mut operands = Self {
            register: [false; 3],
            constants: [SmallVec::new(), SmallVec::new(), SmallVec::new()],
        };
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= atoms@.len(), atoms_wf(atoms@),
            operands_members(operands, atoms@.subrange(0, index as int)),
            decreases atoms@.len() - index))]
        while index < atoms.len() {
            let atom = atoms[index];
            proof_decl! { let ghost previous = operands; }
            match atom.operand {
                Operand::Register => operands.register[atom.component] = true,
                Operand::Constant(value) => operands.constants[atom.component].push(value),
            }
            proof! {
                assert(atoms@.subrange(0, index as int + 1)
                    =~= atoms@.subrange(0, index as int).push(atom));
                lemma_operands_push(previous, operands, atoms@.subrange(0, index as int), atom);
            }
            index += 1;
        }
        proof! { assert(atoms@.subrange(0, atoms@.len() as int) =~= atoms@); }
        proof_decl! { let ghost collected = operands; }
        operands.normalize();
        proof! { lemma_operands_preserved(collected, operands, atoms@); }
        operands
    }

    #[verus_spec(result => ensures operands_wf(*final(self)),
        final(self).register == old(self).register,
        forall|i: int| 0 <= i < 3 ==> final(self).constants[i].view().to_set()
            == old(self).constants[i].view().to_set())]
    fn normalize(&mut self) {
        normalize_ids(&mut self.constants[0]);
        normalize_ids(&mut self.constants[1]);
        normalize_ids(&mut self.constants[2]);
    }
}

/// `Split(Γ, A)`: refinements of `constraint` that decide every register–constant pair of the
/// operands, one per satisfiable choice of literals. A finite register the operands mention is
/// fixed to each of its remaining values instead, so that letters never depend on its value.
#[verus_verify]
#[verus_spec(result => requires constraint_wf(*constraint), operands_wf(*operands),
    split_capacity(*constraint, *operands, *universes),
    ensures constraint_views(result@) == split_views(*constraint, *operands, *universes),
    split_contract(*constraint, *operands, *universes, result@),
    universes_distinct(*universes) ==> constraint_sequence(result@).no_duplicates(),
        forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]))]
pub(crate) fn split(
    constraint: &Constraint,
    operands: &Operands,
    universes: &Universes,
) -> Vec<Constraint> {
    let first = split_register(
        &constraint.0[0],
        operands.register[0],
        &operands.constants[0],
        &universes[0],
    );
    let second = split_register(
        &constraint.0[1],
        operands.register[1],
        &operands.constants[1],
        &universes[1],
    );
    let third = split_register(
        &constraint.0[2],
        operands.register[2],
        &operands.constants[2],
        &universes[2],
    );
    let result = product_constraints([&first, &second, &third]);
    proof! { lemma_split_contract(*constraint, *operands, *universes, result@); }
    result
}

/// `Λ(Γ, A)`: the letters for a constraint that decides the operands. For a finite component,
/// the values outside the named classes form one class, represented by the first of them.
#[verus_verify]
#[verus_spec(result => requires constraint_wf(*constraint), operands_wf(*operands),
    letter_capacity(*constraint, *operands, *universes),
    ensures letter_views(result@) == letters_views(*constraint, *operands, *universes),
        letters_contract(*constraint, *operands, *universes, result@),
        letter_sequence(result@).no_duplicates(),
        letter_alpha_unique(*constraint, *operands, *universes, result@))]
fn letters(constraint: &Constraint, operands: &Operands, universes: &Universes) -> Vec<Letter> {
    let registers = register_classes(constraint);
    let first = class_choices(
        &constraint.0[0],
        operands.register[0],
        &operands.constants[0],
        &universes[0],
    );
    let second = class_choices(
        &constraint.0[1],
        operands.register[1],
        &operands.constants[1],
        &universes[1],
    );
    let third = class_choices(
        &constraint.0[2],
        operands.register[2],
        &operands.constants[2],
        &universes[2],
    );
    let result = product_letters([&first, &second, &third], registers);
    proof! {
        lemma_letters_contract(*constraint, *operands, *universes, result@);
        lemma_letter_alpha_unique(*constraint, *operands, *universes, result@);
    }
    result
}

#[verus_verify]
#[verus_spec(result => ensures forall|i: int| 0 <= i < 3
    ==> result[i] == raw_register_class(constraint.0[i]))]
fn register_classes(constraint: &Constraint) -> [Class; COMPONENTS] {
    [
        class_of(&constraint.0[0]),
        class_of(&constraint.0[1]),
        class_of(&constraint.0[2]),
    ]
}

/// The successor cases `succ(Γ, A)` (`def:successors`), grouped by refined constraint.
#[verus_verify]
#[verus_spec(result => requires atoms_wf(atoms@), constraint_wf(*constraint),
    inclusion::satisfiable(ndomains(*universes), implementation::constraint_of(constraint@)),
    steps_capacity(*constraint, atoms@, *universes),
    ensures steps_result(*constraint, atoms@, *universes, result@),
        universes_distinct(*universes) ==> constraint_sequence(group_constraints(result@)).no_duplicates(),
        forall|i: int| 0 <= i < result@.len() ==> letter_sequence(result@[i].1@).no_duplicates(),
        steps_alphas_unique(*constraint, atoms@, *universes, result@))]
pub(crate) fn steps(
    constraint: &Constraint,
    atoms: &[Atom],
    universes: &Universes,
) -> Vec<(Constraint, Vec<Letter>)> {
    let operands = Operands::of(atoms);
    let refinements = split(constraint, &operands, universes);
    let count = refinements.len();
    proof_decl! { let ghost source = refinements@; }
    let mut iter = refinements.into_iter();
    let mut result: Vec<(Constraint, Vec<Letter>)> = Vec::with_capacity(count);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= count, count == source.len(), result@.len() == index,
        operands_of(operands, atoms@), atoms_wf(atoms@),
        steps_capacity(*constraint, atoms@, *universes),
        constraint_views(source) == split_views(*constraint, operands, *universes),
        forall|i: int| 0 <= i < source.len() ==> constraint_wf(source[i]),
        universes_distinct(*universes) ==> constraint_sequence(source).no_duplicates(),
        iter.obeys_prophetic_iter_laws(), iter.remaining() == source.subrange(index as int, count as int),
        forall|i: int| 0 <= i < index ==> result@[i].0 == source[i]
            && letter_views(result@[i].1@) == letters_views(source[i], operands, *universes)
            && letter_sequence(result@[i].1@).no_duplicates()
            && letter_alpha_unique(source[i], operands, *universes, result@[i].1@),
        decreases count - index))]
    while index < count {
        let refined = match iter.next() {
            Some(value) => value,
            None => unreachable!(),
        };
        proof! {
            assert(refined == source[index as int]);
            lemma_constraint_view_at(source, index as int);
        }
        let letters = letters(&refined, &operands, universes);
        result.push((refined, letters));
        index += 1;
    }
    proof! {
        assert(group_constraints(result@) =~= source);
        assert forall|i: int| 0 <= i < result@.len() implies constraint_wf(result@[i].0)
            && letter_views(result@[i].1@) == letters_views(result@[i].0, operands, *universes) by {
            assert(result@[i].0 == source[i]);
        }
        assert forall|i: int| 0 <= i < result@.len() implies
            letter_sequence(result@[i].1@).no_duplicates()
                && letter_alpha_unique(result@[i].0, operands, *universes, result@[i].1@) by {
            assert(result@[i].0 == source[i]);
        }
        lemma_steps_alphas_unique(*constraint, atoms@, *universes, operands, result@);
        assert(steps_result(*constraint, atoms@, *universes, result@));
    }
    result
}

#[verus_verify]
#[verus_spec(result => ensures canonical(final(values).view()),
    final(values).view().to_set() == old(values).view().to_set())]
fn normalize_ids<A: smallvec::Array<Item = ConstId>>(values: &mut SmallVec<A>) {
    proof_decl! { let ghost before = values.view(); }
    values.as_mut_slice().sort_unstable();
    proof_decl! { let ghost sorted = values.view(); }
    proof! { history_semantics::normalize_verify::lemma_multiset_members(before, sorted); }
    proof! { assert(sorted.to_set() =~= before.to_set()); }
    proof! {
        assert forall|i: int, j: int| 0 <= i < j < sorted.len() implies sorted[i] <= sorted[j] by {
            assert(!(vstd::std_specs::cmp::OrdSpec::cmp_spec(&sorted[i], &sorted[j]) is Greater));
        }
    }
    let count = values.len();
    let mut index = 0;
    let mut write = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= count, write <= index, values.view().len() == count,
        sorted.len() == count,
        sorted.to_set() == before.to_set(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j],
        values.view().subrange(0, write as int)
            == junco_core::verify::history_assumptions::dedup_spec(sorted.subrange(0, index as int)),
        forall|i: int| index <= i < count ==> values.view()[i] == sorted[i],
        decreases count - index))]
    while index < count {
        let slice: &[ConstId] = values;
        let value = slice[index];
        proof! {
            history_semantics::normalize_verify::lemma_dedup_properties(sorted.subrange(0, index as int));
            history_semantics::normalize_verify::lemma_dedup_push(sorted.subrange(0, index as int), value);
            assert(sorted.subrange(0, index as int + 1)
                =~= sorted.subrange(0, index as int).push(value));
        }
        let duplicate = if index == 0 {
            false
        } else {
            proof! { assert(write > 0); }
            let prior = slice[write - 1];
            prior == value
        };
        if !duplicate {
            if write != index {
                values.as_mut_slice()[write] = value;
            }
            write += 1;
        }
        index += 1;
    }
    proof! { assert(sorted.subrange(0, index as int) =~= sorted); }
    values.truncate(write);
    proof! {
        assert(values.view() == junco_core::verify::history_assumptions::dedup_spec(sorted));
        history_semantics::normalize_verify::lemma_dedup_properties(sorted);
        history_semantics::normalize_verify::lemma_dedup_strict(sorted, |v: u32| v as nat);
        assert forall|i: int, j: int| 0 <= i < j < values.view().len()
            implies values.view()[i] < values.view()[j] by {
            assert((|v: u32| v as nat)(values.view()[i]) < (|v: u32| v as nat)(values.view()[j]));
        }
        assert forall|v: u32| values.view().contains(v) == before.contains(v) by {
            assert(values.view() == junco_core::verify::history_assumptions::dedup_spec(sorted));
            assert(junco_core::verify::history_assumptions::dedup_spec(sorted).contains(v) == sorted.contains(v));
            assert(sorted.to_set().contains(v) == before.to_set().contains(v));
        }
        assert(values.view().to_set() =~= before.to_set());
    }
}

pub(crate) mod equality {
    use super::*;

    #[cfg(verus_keep_ghost)]
    verus! {
    /// The exact ordered key used by native register equality, including noncanonical inputs.
    pub open(crate) spec fn register_key(register: RegisterConstraint) -> (Option<u32>, Seq<u32>) {
        match register {
            RegisterConstraint::Equals(v) => (Some(v), Seq::empty()),
            RegisterConstraint::Differs(vs) => (None, vs.view()),
        }
    }

    /// The three exact ordered register keys used by native constraint equality.
    pub open(crate) spec fn constraint_key(constraint: Constraint) -> Seq<(Option<u32>, Seq<u32>)> {
        Seq::new(3, |i: int| register_key(constraint.0[i]))
    }
    impl vstd::std_specs::cmp::PartialEqSpecImpl for RegisterConstraint {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool {
            register_key(*self) == register_key(*other)
        }
    }
    }

    #[verus_verify]
    impl PartialEq for RegisterConstraint {
        #[verus_spec(result => ensures result == (register_key(*self) == register_key(*other)))]
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Self::Equals(a), Self::Equals(b)) => *a == *b,
                (Self::Differs(a), Self::Differs(b)) => {
                    let left: &[ConstId] = a;
                    let right: &[ConstId] = b;
                    if left.len() != right.len() {
                        return false;
                    }
                    let mut index = 0;
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                    index <= left@.len(), left@.len() == right@.len(),
                    register_key(*self) == (None, left@), register_key(*other) == (None, right@),
                    forall|i: int| 0 <= i < index ==> left@[i] == right@[i],
                    decreases left@.len() - index))]
                    while index < left.len() {
                        if left[index] != right[index] {
                            return false;
                        }
                        index += 1;
                    }
                    proof! { assert(left@ =~= right@); }
                    true
                }
                _ => false,
            }
        }
    }

    #[cfg(verus_keep_ghost)]
    verus! {
    impl vstd::std_specs::cmp::PartialEqSpecImpl for Constraint {
        open spec fn obeys_eq_spec() -> bool { true }
        open(crate) spec fn eq_spec(&self, other: &Self) -> bool {
            constraint_key(*self) == constraint_key(*other)
        }
    }
    }

    #[verus_verify]
    impl PartialEq for Constraint {
        #[verus_spec(result => ensures result == (constraint_key(*self) == constraint_key(*other)))]
        fn eq(&self, other: &Self) -> bool {
            let equal =
                self.0[0] == other.0[0] && self.0[1] == other.0[1] && self.0[2] == other.0[2];
            proof! {
                assert(constraint_key(*self).len() == 3);
                assert(constraint_key(*other).len() == 3);
                assert(equal == (constraint_key(*self)[0] == constraint_key(*other)[0]
                    && constraint_key(*self)[1] == constraint_key(*other)[1]
                    && constraint_key(*self)[2] == constraint_key(*other)[2]));
                if equal {
                    assert forall|i: int| 0 <= i < 3 implies
                        constraint_key(*self)[i] == constraint_key(*other)[i] by {
                        if i == 0 {} else if i == 1 {} else { assert(i == 2); }
                    }
                    assert(constraint_key(*self) =~= constraint_key(*other));
                }
            }
            equal
        }
    }
}

#[verus_verify]
#[verus_spec(result => requires register_wf(*current), canonical(constants@),
    register_count(current@, register, constants@, *universe) <= usize::MAX,
    ensures register_views(result@) == register_options(current@, register, codes(constants@), domain_view(*universe)),
        result@.len() == register_count(current@, register, constants@, *universe),
        result@.len() <= usize::MAX,
        universe_distinct(*universe) ==> register_sequence(result@).no_duplicates(),
        forall|i: int| 0 <= i < result@.len() ==> register_wf(result@[i]))]
fn split_register(
    current: &RegisterConstraint,
    register: bool,
    constants: &[ConstId],
    universe: &Universe,
) -> RegisterChoices {
    let mut equals = SmallVec::<[ConstId; 4]>::new();
    if !register || matches!(current, RegisterConstraint::Equals(_)) {
        let result = RegisterChoices {
            equals,
            last: Some(current.copy()),
        };
        proof! { lemma_register_choices(result); lemma_register_choices_distinct(result); }
        return result;
    }
    let RegisterConstraint::Differs(differs) = current else {
        unreachable!()
    };
    proof! { lemma_codes(differs.view()); lemma_codes(constants@); }
    if let Some(values) = universe {
        let slice: &[ConstId] = values;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= slice@.len(), register_wf(*current), register,
            current@ == implementation::RegisterView::Differs(codes(differs.view())),
            universe_distinct(*universe) ==> slice@.no_duplicates(),
            *universe is Some, (*((*universe)->Some_0))@ == slice@,
            equals.view() == remaining(slice@.subrange(0, index as int), codes(differs.view())),
            codes(equals.view()) == codes(slice@.subrange(0, index as int)).difference(codes(differs.view())),
            decreases slice@.len() - index))]
        while index < slice.len() {
            let value = slice[index];
            proof_decl! { let ghost prior = equals.view(); }
            proof! {
                lemma_codes_push(slice@.subrange(0, index as int), value);
                slice@.subrange(0, index as int).lemma_filter_push(value, |v: u32| !codes(differs.view()).contains(v as nat));
            }
            if !current.entails_differ(value) {
                equals.push(value);
                proof! { lemma_codes_push(prior, value); }
            }
            proof! {
                assert(slice@.subrange(0, index as int + 1) =~= slice@.subrange(0, index as int).push(value));
                lemma_register_filter_insert(codes(slice@.subrange(0, index as int)), codes(differs.view()), value as nat);
            }
            index += 1;
        }
        proof! { assert(slice@.subrange(0, index as int) =~= slice@); }
        let result = RegisterChoices { equals, last: None };
        proof! {
            lemma_register_choices(result);
            if universe_distinct(*universe) {
                lemma_filter_distinct(slice@, |v: u32| !codes(differs.view()).contains(v as nat));
                lemma_register_choices_distinct(result);
            }
        }
        return result;
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= constants@.len(), register_wf(*current), register, *universe is None,
        current@ == implementation::RegisterView::Differs(codes(differs.view())),
        canonical(constants@),
        equals.view() == remaining(constants@.subrange(0, index as int), codes(differs.view())),
        codes(equals.view()) == codes(constants@.subrange(0, index as int)).difference(codes(differs.view())),
        decreases constants@.len() - index))]
    while index < constants.len() {
        let value = constants[index];
        proof_decl! { let ghost prior = equals.view(); }
        proof! {
            lemma_codes_push(constants@.subrange(0, index as int), value);
            constants@.subrange(0, index as int).lemma_filter_push(value, |v: u32| !codes(differs.view()).contains(v as nat));
        }
        if !current.decides(value) {
            equals.push(value);
            proof! { lemma_codes_push(prior, value); }
        }
        proof! {
            assert(constants@.subrange(0, index as int + 1) =~= constants@.subrange(0, index as int).push(value));
            lemma_register_filter_insert(codes(constants@.subrange(0, index as int)), codes(differs.view()), value as nat);
        }
        index += 1;
    }
    proof! { assert(constants@.subrange(0, index as int) =~= constants@); lemma_codes(equals.view()); }
    proof! {
        if equals.view().len() == 0 { assert(codes(equals.view()) =~= Set::<nat>::empty()); }
        else { assert(codes(equals.view()).contains(equals.view()[0] as nat)); assert(codes(equals.view()).len() > 0); }
    }
    let last = if equals.is_empty() {
        current.copy()
    } else {
        let mut all_differ = SmallVec::new();
        all_differ.extend_from_slice(differs);
        all_differ.extend_from_slice(&equals);
        proof! { lemma_codes_concat(differs.view(), equals.view()); }
        proof! { assert(codes(all_differ.view()) == codes(differs.view()).union(codes(equals.view()))); }
        normalize_ids(&mut all_differ);
        proof! { assert(codes(all_differ.view()) == codes(differs.view()).union(codes(equals.view()))); }
        RegisterConstraint::Differs(all_differ)
    };
    let result = RegisterChoices {
        equals,
        last: Some(last),
    };
    proof! {
        lemma_register_choices(result);
        assert(constants@.no_duplicates());
        lemma_filter_distinct(constants@, |v: u32| !codes(differs.view()).contains(v as nat));
        lemma_register_choices_distinct(result);
    }
    result
}

#[verus_verify]
#[verus_spec(result => requires
    choices[0]@.len() * choices[1]@.len() <= usize::MAX,
    choices[0]@.len() * choices[1]@.len() * choices[2]@.len() <= usize::MAX,
    forall|a: int, i: int| 0 <= a < 3 && 0 <= i < choices[a]@.len() ==> register_wf(choices[a]@[i]),
    forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
    ensures result@.len() == choices[0]@.len() * choices[1]@.len() * choices[2]@.len(),
        forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]),
        (forall|a: int| 0 <= a < 3 ==> register_sequence(choices[a]@).no_duplicates())
            ==> constraint_sequence(result@).no_duplicates(),
        constraint_views(result@) == register_product(register_views(choices[0]@),
            register_views(choices[1]@), register_views(choices[2]@)))]
fn product_constraints(choices: [&RegisterChoices; COMPONENTS]) -> Vec<Constraint> {
    let n0 = choices[0].len();
    let n1 = choices[1].len();
    let n2 = choices[2].len();
    let capacity = n0 * n1 * n2;
    let mut result = Vec::with_capacity(capacity);
    proof_decl! {
        let ghost axes = [choices[0]@, choices[1]@, choices[2]@];
        let ghost full = register_product(register_views(axes[0]), register_views(axes[1]), register_views(axes[2]));
    }
    proof! { lemma_register_product_members(register_views(axes[0]), register_views(axes[1]), register_views(axes[2])); }
    let mut first: usize = 0;
    proof! { assert(0usize * n1 * n2 == 0) by(nonlinear_arith); }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        first <= n0, n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
        capacity == n0 * n1 * n2,
        result@.len() == first * n1 * n2,
        product_done(axes, constraint_views(result@), first as int, 0, 0),
        constraint_views(result@).subset_of(full),
        full == register_product(register_views(axes[0]), register_views(axes[1]), register_views(axes[2])),
        forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]),
        constraint_positions(axes, result@),
        forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
        forall|a: int, i: int| 0 <= a < 3 && 0 <= i < choices[a]@.len() ==> register_wf(choices[a]@[i]),
        axes == [choices[0]@, choices[1]@, choices[2]@],
        decreases n0 - first))]
    while first < n0 {
        let mut second = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            first < n0, second <= n1, n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
            capacity == n0 * n1 * n2,
            result@.len() == (first * n1 + second) * n2,
            product_done(axes, constraint_views(result@), first as int, second as int, 0),
            constraint_views(result@).subset_of(full),
            full == register_product(register_views(axes[0]), register_views(axes[1]), register_views(axes[2])),
            forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]),
            constraint_positions(axes, result@),
            forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
            forall|a: int, i: int| 0 <= a < 3 && 0 <= i < choices[a]@.len() ==> register_wf(choices[a]@[i]),
            axes == [choices[0]@, choices[1]@, choices[2]@],
            decreases n1 - second))]
        while second < n1 {
            let mut third = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                first < n0, second < n1, third <= n2,
                n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
                capacity == n0 * n1 * n2,
                result@.len() == (first * n1 + second) * n2 + third,
                product_done(axes, constraint_views(result@), first as int, second as int, third as int),
                constraint_views(result@).subset_of(full),
                full == register_product(register_views(axes[0]), register_views(axes[1]), register_views(axes[2])),
                forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]),
                constraint_positions(axes, result@),
                forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
                forall|a: int, i: int| 0 <= a < 3 && 0 <= i < choices[a]@.len() ==> register_wf(choices[a]@[i]),
                axes == [choices[0]@, choices[1]@, choices[2]@],
                decreases n2 - third))]
            while third < n2 {
                let next = Constraint([
                    choices[0].get(first),
                    choices[1].get(second),
                    choices[2].get(third),
                ]);
                proof_decl! { let ghost previous = result@; let ghost copied = next; }
                result.push(next);
                proof! {
                    lemma_constraint_views_push(previous, copied);
                    assert(copied@ == choice_view(axes, first as int, second as int, third as int));
                    lemma_constraint_position_push(axes, previous, copied, first as int, second as int, third as int);
                    lemma_product_step(axes, constraint_views(previous), constraint_views(result@),
                        first as int, second as int, third as int);
                    lemma_register_product_members(register_views(axes[0]), register_views(axes[1]), register_views(axes[2]));
                    lemma_register_view_at(axes[0], first as int);
                    lemma_register_view_at(axes[1], second as int);
                    lemma_register_view_at(axes[2], third as int);
                    assert(register_views(axes[0]).contains(axes[0][first as int]@));
                    assert(register_views(axes[1]).contains(axes[1][second as int]@));
                    assert(register_views(axes[2]).contains(axes[2][third as int]@));
                    assert(full.contains(copied@));
                }
                third += 1;
            }
            proof! { assert(product_done(axes, constraint_views(result@), first as int, second as int + 1, 0)); }
            proof! { assert((first * n1 + second) * n2 + n2 == (first * n1 + second + 1) * n2) by(nonlinear_arith); }
            second += 1;
        }
        proof! { assert(product_done(axes, constraint_views(result@), first as int + 1, 0, 0)); }
        proof! { assert((first * n1 + n1) * n2 == (first + 1) * n1 * n2) by(nonlinear_arith); }
        first += 1;
    }
    proof! {
        if forall|a: int| 0 <= a < 3 ==> register_sequence(choices[a]@).no_duplicates() {
            lemma_constraint_product_distinct(axes, result@);
        }
        lemma_register_product_members(register_views(axes[0]), register_views(axes[1]), register_views(axes[2]));
        assert forall|g: implementation::ConstraintView| full.contains(g)
            implies constraint_views(result@).contains(g) by {
            let i = choose|i: int| 0 <= i < axes[0].len() && axes[0][i]@ == g.principal;
            let j = choose|j: int| 0 <= j < axes[1].len() && axes[1][j]@ == g.action;
            let k = choose|k: int| 0 <= k < axes[2].len() && axes[2][k]@ == g.resource;
            assert(g == choice_view(axes, i, j, k));
        }
        assert(constraint_views(result@) =~= full);
    }
    result
}

#[verus_verify]
#[verus_spec(result => ensures result == match domain_view(*universe) {
    None => true, Some(vs) => vs.contains(value as nat) })]
fn in_universe(universe: &Universe, value: ConstId) -> bool {
    match universe {
        None => true,
        Some(values) => {
            let slice: &[ConstId] = values;
            proof! { lemma_codes(slice@); }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                index <= slice@.len(), domain_view(*universe) == Some(codes(slice@)),
                forall|i: int| 0 <= i < index ==> slice@[i] != value,
                decreases slice@.len() - index))]
            while index < slice.len() {
                if slice[index] == value {
                    proof! { lemma_codes(slice@); }
                    return true;
                }
                index += 1;
            }
            proof! { lemma_codes(slice@); }
            false
        }
    }
}

#[verus_verify]
#[verus_spec(result => ensures result@ == register_class(current@), result == raw_register_class(*current))]
fn class_of(current: &RegisterConstraint) -> Class {
    match current {
        RegisterConstraint::Equals(value) => Class::Constant(*value),
        RegisterConstraint::Differs(_) => Class::Register,
    }
}

#[verus_verify]
#[verus_spec(result => requires class_options(current@, register, codes(constants@), *universe).len() <= usize::MAX,
    ensures option_views(result@) == class_options(current@, register, codes(constants@), *universe),
        class_choices_wf(result), result@.len() == option_views(result@).len(), result@.len() <= usize::MAX,
        class_sequence(result@).no_duplicates())]
// Nested so the proof statements stay inside the `if let` scope; Verus does not take let chains.
#[allow(clippy::collapsible_if)]
fn class_choices(
    current: &RegisterConstraint,
    register: bool,
    constants: &[ConstId],
    universe: &Universe,
) -> ClassChoices {
    let mut names = SmallVec::<[ConstId; 4]>::new();
    let mut index = 0;
    proof_decl! { let ghost domain = domain_view(*universe); }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= constants@.len(), domain == domain_view(*universe),
        class_options(current@, register, codes(constants@), *universe).len() <= usize::MAX,
        names.view() == constants@.subrange(0, index as int).filter(|v: u32| match domain {
            None => true, Some(vs) => vs.contains(v as nat) }),
        decreases constants@.len() - index))]
    while index < constants.len() {
        let value = constants[index];
        proof! { constants@.subrange(0, index as int).lemma_filter_push(value,
        |v: u32| match domain { None => true, Some(vs) => vs.contains(v as nat) }); }
        if in_universe(universe, value) {
            names.push(value);
        }
        proof! { assert(constants@.subrange(0, index as int + 1)
        =~= constants@.subrange(0, index as int).push(value)); }
        index += 1;
    }
    proof! {
        assert(constants@.subrange(0, index as int) =~= constants@);
        lemma_filtered_codes(constants@, domain);
    }
    if register {
        if let RegisterConstraint::Equals(value) = current {
            proof_decl! { let ghost prior = names.view(); }
            names.push(*value);
            proof! { lemma_codes_push(prior, *value); }
        }
    }
    proof! { assert(codes(names.view()) == named_codes(current@, register, codes(constants@), domain)); }
    normalize_ids(&mut names);
    let is_register = register && matches!(class_of(current), Class::Register);
    if let Some(values) = universe {
        let values: &[ConstId] = values;
        let slice: &[ConstId] = &names;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= values@.len(), canonical(slice@), slice@ == names.view(),
            class_options(current@, register, codes(constants@), *universe).len() <= usize::MAX,
            *universe is Some, (*((*universe)->Some_0))@ == values@,
            is_register == (register && current@ is Differs),
            codes(slice@) == named_codes(current@, register, codes(constants@), domain_view(*universe)),
            forall|i: int| 0 <= i < index ==> codes(slice@).contains(values@[i] as nat),
            decreases values@.len() - index))]
        while index < values.len() {
            let value = values[index];
            proof! { lemma_codes(slice@); assert(junco_core::verify::history_assumptions::strictly_sorted(slice@)); }
            if slice.binary_search(&value).is_err() {
                proof! { lemma_first_other_at(values@, codes(slice@), index as int); }
                let result = ClassChoices {
                    names,
                    register: is_register,
                    infinite: false,
                    other: Some(value),
                };
                proof! {
                    lemma_class_choices(result);
                    lemma_class_choices_distinct(result);
                    assert(option_views(result@) == class_options(current@, register, codes(constants@), *universe));
                }
                return result;
            }
            index += 1;
        }
        proof! { lemma_first_other(values@, codes(slice@)); }
    }
    let result = ClassChoices {
        names,
        register: is_register,
        infinite: universe.is_none(),
        other: None,
    };
    proof! {
        lemma_class_choices(result);
        lemma_class_choices_distinct(result);
        assert(option_views(result@) == class_options(current@, register, codes(constants@), *universe));
    }
    result
}

#[verus_verify]
#[verus_spec(result => requires
    choices[0]@.len() * choices[1]@.len() <= usize::MAX,
    choices[0]@.len() * choices[1]@.len() * choices[2]@.len() <= usize::MAX,
    forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
    ensures result@.len() == choices[0]@.len() * choices[1]@.len() * choices[2]@.len(),
        (forall|a: int| 0 <= a < 3 ==> class_sequence(choices[a]@).no_duplicates())
            ==> letter_sequence(result@).no_duplicates(),
        letter_views(result@) == letter_product(option_views(choices[0]@),
            option_views(choices[1]@), option_views(choices[2]@), registers))]
fn product_letters(
    choices: [&ClassChoices; COMPONENTS],
    registers: [Class; COMPONENTS],
) -> Vec<Letter> {
    let n0 = choices[0].len();
    let n1 = choices[1].len();
    let n2 = choices[2].len();
    let capacity = n0 * n1 * n2;
    let mut result = Vec::with_capacity(capacity);
    proof_decl! {
        let ghost axes = [choices[0]@, choices[1]@, choices[2]@];
        let ghost full = letter_product(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers);
    }
    let mut first: usize = 0;
    proof! { assert(0usize * n1 * n2 == 0) by(nonlinear_arith); }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        first <= n0, n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
        capacity == n0 * n1 * n2,
        result@.len() == first * n1 * n2,
        letter_product_done(axes, registers, letter_views(result@), first as int, 0, 0),
        letter_views(result@).subset_of(full),
        full == letter_product(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers),
        forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
        letter_positions(axes, registers, result@),
        axes == [choices[0]@, choices[1]@, choices[2]@],
        decreases n0 - first))]
    while first < n0 {
        let mut second = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            first < n0, second <= n1, n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
            capacity == n0 * n1 * n2,
            result@.len() == (first * n1 + second) * n2,
            letter_product_done(axes, registers, letter_views(result@), first as int, second as int, 0),
            letter_views(result@).subset_of(full),
            full == letter_product(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers),
            forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
            axes == [choices[0]@, choices[1]@, choices[2]@],
            letter_positions(axes, registers, result@),
            decreases n1 - second))]
        while second < n1 {
            let mut third = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                first < n0, second < n1, third <= n2,
                n0 == axes[0].len(), n1 == axes[1].len(), n2 == axes[2].len(),
                capacity == n0 * n1 * n2,
                result@.len() == (first * n1 + second) * n2 + third,
                letter_product_done(axes, registers, letter_views(result@), first as int, second as int, third as int),
                letter_views(result@).subset_of(full),
                full == letter_product(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers),
                forall|a: int| 0 <= a < 3 ==> choices[a]@.len() <= usize::MAX,
                axes == [choices[0]@, choices[1]@, choices[2]@],
                letter_positions(axes, registers, result@),
                decreases n2 - third))]
            while third < n2 {
                let next = Letter {
                    classes: [
                        choices[0].get(first),
                        choices[1].get(second),
                        choices[2].get(third),
                    ],
                    registers,
                };
                proof_decl! { let ghost previous = result@; let ghost copied = next; }
                result.push(next);
                proof! {
                    lemma_letter_views_push(previous, copied);
                    assert(copied@ == letter_choice_view(axes, registers, first as int, second as int, third as int));
                    lemma_letter_product_step(axes, registers, letter_views(previous), letter_views(result@),
                        first as int, second as int, third as int);
                    lemma_letter_position_push(axes, registers, previous, copied, first as int, second as int, third as int);
                    lemma_letter_product_members(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers);
                    lemma_option_view_at(axes[0], first as int);
                    lemma_option_view_at(axes[1], second as int);
                    lemma_option_view_at(axes[2], third as int);
                    assert(full.contains(copied@));
                }
                third += 1;
            }
            proof! {
                assert(letter_product_done(axes, registers, letter_views(result@), first as int, second as int + 1, 0));
                assert((first * n1 + second) * n2 + n2 == (first * n1 + second + 1) * n2) by(nonlinear_arith);
            }
            second += 1;
        }
        proof! {
            assert(letter_product_done(axes, registers, letter_views(result@), first as int + 1, 0, 0));
            assert((first * n1 + n1) * n2 == (first + 1) * n1 * n2) by(nonlinear_arith);
        }
        first += 1;
    }
    proof! {
        if forall|a: int| 0 <= a < 3 ==> class_sequence(choices[a]@).no_duplicates() {
            lemma_letter_product_distinct(axes, registers, result@);
        }
        lemma_letter_product_members(option_views(axes[0]), option_views(axes[1]), option_views(axes[2]), registers);
        assert forall|l: implementation::LetterView| full.contains(l) implies letter_views(result@).contains(l) by {
            let i = choose|i: int| 0 <= i < axes[0].len() && class_option(axes[0][i]) == l.principal;
            let j = choose|j: int| 0 <= j < axes[1].len() && class_option(axes[1][j]) == l.action;
            let k = choose|k: int| 0 <= k < axes[2].len() && class_option(axes[2][k]) == l.resource;
            assert(l == letter_choice_view(axes, registers, i, j, k));
        }
        assert(letter_views(result@) =~= full);
    }
    result
}

#[verus_verify]
pub(crate) struct RegisterChoices {
    pub(crate) equals: SmallVec<[ConstId; 4]>,
    pub(crate) last: Option<RegisterConstraint>,
}

#[verus_verify]
impl RegisterChoices {
    #[verus_spec(result => requires self@.len() <= usize::MAX, ensures result == self@.len())]
    fn len(&self) -> usize {
        self.equals.len() + if self.last.is_some() { 1 } else { 0 }
    }

    #[verus_spec(result => requires index < self@.len(), self@.len() <= usize::MAX,
        forall|i: int| 0 <= i < self@.len() ==> register_wf(self@[i]),
        ensures result@ == self@[index as int]@, register_wf(result))]
    fn get(&self, index: usize) -> RegisterConstraint {
        let values: &[ConstId] = &self.equals;
        if index < values.len() {
            RegisterConstraint::Equals(values[index])
        } else {
            match &self.last {
                Some(r) => {
                    proof! { assert(self@[index as int] == *r); assert(register_wf(*r)); }
                    r.copy()
                }
                None => unreachable!(),
            }
        }
    }
}

#[verus_verify]
pub(crate) struct ClassChoices {
    pub(crate) names: SmallVec<[ConstId; 4]>,
    pub(crate) register: bool,
    pub(crate) infinite: bool,
    pub(crate) other: Option<ConstId>,
}

#[verus_verify]
impl ClassChoices {
    #[verus_spec(result => requires self@.len() <= usize::MAX, ensures result == self@.len())]
    fn len(&self) -> usize {
        self.names.len()
            + if self.infinite { 1 } else { 0 }
            + if self.register { 1 } else { 0 }
            + if self.other.is_some() { 1 } else { 0 }
    }

    #[verus_spec(result => requires index < self@.len(), self@.len() <= usize::MAX,
        ensures result == self@[index as int])]
    fn get(&self, mut index: usize) -> Option<Class> {
        if self.infinite {
            if index == 0 {
                return None;
            }
            index -= 1;
        }
        if self.register {
            if index == 0 {
                return Some(Class::Register);
            }
            index -= 1;
        }
        let values: &[ConstId] = &self.names;
        if index < values.len() {
            Some(Class::Constant(values[index]))
        } else {
            match self.other {
                Some(value) => Some(Class::Constant(value)),
                None => unreachable!(),
            }
        }
    }
}
