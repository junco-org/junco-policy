//! Constraints on the candidate, their splits, and letters: the finite alphabet of the search.
//!
//! A constraint records what is known about each register `κ_c`, the candidate's value of
//! component `c`. Splitting refines a constraint until it decides every comparison between a
//! register and a constant that a set of atoms makes; a register of a finite domain is fixed to
//! one value instead. Relative to such a constraint, a letter names one class of events that no
//! atom of the set can tell apart: for each component, the operand it equals, or none of them.

#[cfg(verus_keep_ghost)]
use self::equality::{constraint_key, register_key};
use history_store::native::NativeMap;
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

// Event arity is carried by each sequence, rather than a global register count.

/// Identity of an interned constant; constants of different components never share one.
pub(crate) type ConstId = u32;

/// The declared values of one component, in declaration order, or `None` if it is infinite.
pub(crate) type Universe = Option<Rc<Vec<ConstId>>>;

/// The universe of each component.
pub(crate) type Universes = Vec<Universe>;

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
// Equality compares the ordered register keys, exactly as the derived Hash hashes them.
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, Eq, Hash)]
pub(crate) struct Constraint(pub(crate) Vec<RegisterConstraint>);

#[verus_verify]
impl Constraint {
    /// The constraint fixing the registers that head constants pin, or `None` if some register
    /// can take no value of its universe.
    #[verus_spec(result => requires constants@.len() == universes@.len(),
    1 <= constants@.len() <= history_syntax::MAX_ARITY,
    ensures match result {
        Some(c) => constraint_wf(c) && c@.len() == constants@.len()
            && (forall|i: int| 0 <= i < constants@.len() ==> c.0[i]@ == match constants@[i] {
                Some(v) => implementation::RegisterView::Equals(v as nat),
                None => implementation::RegisterView::Differs(Set::empty()),
            })
            && implementation::constraint_of(c@) == inclusion::head_constraint(head_view(constants@))
            && inclusion::satisfiable(ndomains(*universes), implementation::constraint_of(c@)),
        None => !inclusion::satisfiable(ndomains(*universes), inclusion::head_constraint(head_view(constants@))),
    })]
    pub(crate) fn head(constants: &[Option<ConstId>], universes: &Universes) -> Option<Self> {
        let mut registers = Vec::with_capacity(constants.len());
        let mut possible = true;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= constants@.len(), registers@.len() == index,
        constants@.len() == universes@.len(), 1 <= constants@.len() <= history_syntax::MAX_ARITY,
        forall|i: int| 0 <= i < index ==> register_wf(registers@[i])
            && registers@[i]@ == match constants@[i] {
                Some(v) => implementation::RegisterView::Equals(v as nat),
                None => implementation::RegisterView::Differs(Set::empty()),
            },
        possible == (forall|i: int| 0 <= i < index ==> register_possible(registers@[i], universes@[i])),
        decreases constants@.len() - index))]
        while index < constants.len() {
            let register = RegisterConstraint::head(constants[index]);
            possible = register.satisfiable(&universes[index]) && possible;
            registers.push(register);
            index += 1;
        }
        let constraint = Self(registers);
        proof! { lemma_head_view(constraint, constants@); lemma_constraint_possible(constraint, *universes); }
        if possible { Some(constraint) } else { None }
    }

    /// Whether every valuation satisfying `self` satisfies `other`, read syntactically.
    #[verus_spec(result => requires constraint_wf(*self), constraint_wf(*other),
    self@.len() == other@.len(),
    ensures result == (forall|i: int| 0 <= i < self@.len()
            ==> register_entails(self@[i], other@[i])),
        result ==> forall|d: encoding::NDomains|
            inclusion::entails(d, implementation::constraint_of(self@), implementation::constraint_of(other@)))]
    pub(crate) fn entails(&self, other: &Self) -> bool {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= self.0@.len(), self.0@.len() == other.0@.len(),
        constraint_wf(*self), constraint_wf(*other),
        forall|i: int| 0 <= i < index ==> register_entails(self.0@[i]@, other.0@[i]@),
        decreases self.0@.len() - index))]
        while index < self.0.len() {
            if !self.0[index].entails(&other.0[index]) {
                proof! {
                    assert(self@[index as int] == self.0@[index as int]@);
                    assert(other@[index as int] == other.0@[index as int]@);
                    assert(!register_entails(self@[index as int], other@[index as int]));
                    assert(!(forall|i: int| 0 <= i < self@.len()
                        ==> register_entails(self@[i], other@[i])));
                }
                return false;
            }
            index += 1;
        }
        proof! { lemma_constraint_entails(self@, other@); }
        true
    }

    #[verus_spec(result => ensures result@ == self@, constraint_key(result) == constraint_key(*self),
    constraint_wf(result) == constraint_wf(*self))]
    pub(crate) fn copy(&self) -> Self {
        let mut registers: Vec<RegisterConstraint> = Vec::with_capacity(self.0.len());
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= self.0@.len(), registers@.len() == index,
        forall|i: int| 0 <= i < index ==> registers@[i]@ == self.0@[i]@
            && register_key(registers@[i]) == register_key(self.0@[i])
            && register_wf(registers@[i]) == register_wf(self.0@[i]),
        decreases self.0@.len() - index))]
        while index < self.0.len() {
            registers.push(self.0[index].copy());
            index += 1;
        }
        let result = Self(registers);
        proof! {
            assert forall|i: int| 0 <= i < self.0@.len() implies
                register_wf(result.0[i]) == register_wf(self.0[i]) by {
                assert(result.0[i] == result.0@[i]);
                assert(self.0[i] == self.0@[i]);
            }
            if constraint_wf(*self) {
                assert forall|i: int| 0 <= i < result.0@.len() implies register_wf(result.0[i]) by {
                    assert(register_wf(self.0[i]));
                }
            } else if constraint_wf(result) {
                assert forall|i: int| 0 <= i < self.0@.len() implies register_wf(self.0[i]) by {
                    assert(register_wf(result.0[i]));
                }
            }
        }
        result
    }
}

/// Index of an interned constraint.
pub(crate) type ConstraintId = u32;

/// Decision 4's exact internal-key introduction; not an axiom for user component types.
/// Constraint's verified equality compares every ordered register key; derived Hash hashes it.
#[inline(always)]
fn native_constraint_key_laws() {}

#[cfg(verus_keep_ghost)]
verus! {
    assume_specification[native_constraint_key_laws]()
        ensures junco_core::spec::hypotheses::key_laws::<Constraint>();
}

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
        native_constraint_key_laws();
        Self {
            constraints: Vec::new(),
            ids: NativeMap::new(),
        }
    }

    #[verus_spec(result => requires table_wf(*old(self)), constraint_wf(constraint),
        ensures table_wf(*final(self)),
            junco_core::verify::history_specs::no_invariant_failure(result),
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Letter {
    /// Class that each component equals, or `None` for any value outside the named classes.
    pub(crate) classes: Vec<Option<Class>>,
    /// Class of each register under the letter's constraint.
    pub(crate) registers: Vec<Class>,
}

#[verus_verify]
impl Letter {
    /// Whether events of this letter satisfy `atom`, which must belong to the atom set the letter
    /// was built for.
    #[verus_spec(result => requires atom.component < self.classes@.len(), atom.component <= u8::MAX,
    self.classes@.len() == self.registers@.len(),
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
    #[verus_spec(result => requires component < self.classes@.len(), component <= u8::MAX,
    ensures class_option(result) == implementation::letter_class(self@, component_at(component)))]
    pub(crate) fn class(&self, component: usize) -> Option<Class> {
        self.classes[component]
    }
    #[verus_spec(result => ensures result.classes@ == self.classes@,
    result.registers@ == self.registers@, result@ == self@)]
    pub(crate) fn copy(&self) -> Self {
        let classes = copy_slice(&self.classes);
        let registers = copy_slice(&self.registers);
        Self { classes, registers }
    }
}

/// Copy scalar entries without depending on the opaque `Clone` relation.
#[verus_verify]
#[verus_spec(result => ensures result@ == values@)]
fn copy_slice<T: Copy>(values: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(values.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= values@.len(), result@.len() == index,
        forall|i: int| 0 <= i < index ==> result@[i] == values@[i],
        decreases values@.len() - index))]
    while index < values.len() {
        result.push(values[index]);
        index += 1;
    }
    proof! { assert(result@ =~= values@); }
    result
}

/// Operands that a set of atoms compares with each component.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Default)]
pub(crate) struct Operands {
    pub(crate) register: Vec<bool>,
    pub(crate) constants: Vec<SmallVec<[ConstId; 4]>>,
}

#[verus_verify]
impl Operands {
    /// Collects the operands of `atoms`.
    #[verus_spec(result => requires atoms_wf(atoms@, arity as nat),
    1 <= arity <= history_syntax::MAX_ARITY,
    ensures operands_of(result, atoms@), result.register@.len() == arity)]
    pub(crate) fn of(atoms: &[Atom], arity: usize) -> Self {
        let mut operands = Self {
            register: Vec::with_capacity(arity),
            constants: Vec::with_capacity(arity),
        };
        let mut component = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        component <= arity, operands.register@.len() == component,
        operands.constants@.len() == component,
forall|i: int| #![trigger operands.register@[i]] 0 <= i < component ==> !operands.register@[i],
forall|i: int| #![trigger operands.constants@[i]] 0 <= i < component ==> operands.constants@[i].view().len() == 0,
        decreases arity - component))]
        while component < arity {
            operands.register.push(false);
            operands.constants.push(SmallVec::new());
            component += 1;
        }
        proof! {
            assert(atoms@.subrange(0, 0) =~= Seq::<Atom>::empty());
            assert forall|i: int, v: u32| 0 <= i < arity implies !operands.constants[i].view().contains(v) by {
        assert(operands.constants@[i].view().len() == 0);
        assert(operands.constants[i] == operands.constants@[i]);
        assert(operands.constants@[i].view() =~= Seq::<u32>::empty());
            }
            assert(operands_members(operands, atoms@.subrange(0, 0)));
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
index <= atoms@.len(), atoms_wf(atoms@, arity as nat),
1 <= arity <= history_syntax::MAX_ARITY,
operands.register@.len() == arity, operands.constants@.len() == arity,
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

    #[verus_spec(result => requires self.register@.len() == self.constants@.len(),
    1 <= self.register@.len() <= history_syntax::MAX_ARITY,
    ensures operands_wf(*final(self)), final(self).register == old(self).register,
    final(self).constants@.len() == old(self).constants@.len(),
    forall|i: int| 0 <= i < final(self).constants@.len() ==> final(self).constants[i].view().to_set()
        == old(self).constants[i].view().to_set())]
    fn normalize(&mut self) {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= self.constants@.len(), self.register == old(self).register,
        self.constants@.len() == old(self).constants@.len(),
        1 <= self.register@.len() <= history_syntax::MAX_ARITY,
        self.register@.len() == self.constants@.len(),
        forall|i: int| 0 <= i < self.constants@.len() ==> self.constants[i].view().to_set() == old(self).constants[i].view().to_set(),
        forall|i: int| 0 <= i < index ==> canonical(self.constants[i].view()),
        decreases self.constants@.len() - index))]
        while index < self.constants.len() {
            normalize_ids(&mut self.constants[index]);
            index += 1;
        }
    }
}

/// `Split(Γ, A)`: all coordinate-local refinements, in lexicographic order.
#[verus_verify]
#[verus_spec(result => requires shape_wf(*constraint, *operands, *universes),
    ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(values) ==> constraint_views(values@) == split_views(*constraint, *operands, *universes)
        && split_contract(*constraint, *operands, *universes, values@)
        && (universes_distinct(*universes) ==> constraint_sequence(values@).no_duplicates())
        && forall|i: int| 0 <= i < values@.len() ==> constraint_wf(values@[i]) && values@[i]@.len() == constraint@.len())]
pub(crate) fn split(
    constraint: &Constraint,
    operands: &Operands,
    universes: &Universes,
) -> Result<Vec<Constraint>, HistoryError> {
    let mut choices: Vec<RegisterChoices> = Vec::with_capacity(constraint.0.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= constraint.0@.len(), choices@.len() == index, shape_wf(*constraint, *operands, *universes),
forall|i: int| #![trigger choices@[i]] 0 <= i < index
    ==> register_views(choices@[i]@) == split_axes(*constraint, *operands, *universes)[i],
forall|i: int| #![trigger choices@[i]] 0 <= i < index && universes_distinct(*universes)
    ==> register_sequence(choices@[i]@).no_duplicates(),
forall|i: int, j: int| #![trigger choices@[i]@[j]] 0 <= i < index && 0 <= j < choices@[i]@.len()
    ==> register_wf(choices@[i]@[j]),
        decreases constraint.0@.len() - index))]
    while index < constraint.0.len() {
        choices.push(split_register(
            &constraint.0[index],
            operands.register[index],
            &operands.constants[index],
            &universes[index],
        ));
        index += 1;
    }
    let mut refs: Vec<&RegisterChoices> = Vec::with_capacity(choices.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
index <= choices@.len(), refs@.len() == index,
choices@.len() == constraint.0@.len(), shape_wf(*constraint, *operands, *universes),
forall|i: int| #![trigger choices@[i]] 0 <= i < choices@.len()
    ==> register_views(choices@[i]@) == split_axes(*constraint, *operands, *universes)[i],
forall|i: int| #![trigger choices@[i]] 0 <= i < choices@.len() && universes_distinct(*universes)
    ==> register_sequence(choices@[i]@).no_duplicates(),
forall|i: int, j: int| #![trigger choices@[i]@[j]] 0 <= i < choices@.len() && 0 <= j < choices@[i]@.len()
    ==> register_wf(choices@[i]@[j]),
forall|i: int| 0 <= i < index ==> *refs@[i] == choices@[i],
        decreases choices@.len() - index))]
    while index < choices.len() {
        refs.push(&choices[index]);
        index += 1;
    }
    proof! {
        assert forall|a: int, i: int| 0 <= a < refs@.len() && 0 <= i < refs@[a]@.len()
            implies register_wf(refs@[a]@[i]) by {
            assert(*refs@[a] == choices@[a]);
            assert(register_wf(choices@[a]@[i]));
        }
        if universes_distinct(*universes) {
            assert forall|a: int| 0 <= a < refs@.len() implies register_sequence(refs@[a]@).no_duplicates() by {
                assert(*refs@[a] == choices@[a]);
                assert(register_sequence(choices@[a]@).no_duplicates());
            }
        }
    }
    let result = product_constraints(&refs)?;
    proof! {
        assert(refs@.map_values(|c: &RegisterChoices| register_views(c@)) =~= split_axes(*constraint, *operands, *universes));
        lemma_split_contract(*constraint, *operands, *universes, result@);
    }
    Ok(result)
}

/// `Λ(Γ, A)`: all coordinate-local event classes, in the same product order.
#[verus_verify]
#[verus_spec(result => requires shape_wf(*constraint, *operands, *universes),
    ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(values) ==> letter_views(values@) == letters_views(*constraint, *operands, *universes)
        && letters_contract(*constraint, *operands, *universes, values@)
        && letter_sequence(values@).no_duplicates()
        && letter_alpha_unique(*constraint, *operands, *universes, values@)
        && forall|i: int| 0 <= i < values@.len() ==> letter_wf(values@[i]) && values@[i]@.classes.len() == constraint@.len())]
fn letters(
    constraint: &Constraint,
    operands: &Operands,
    universes: &Universes,
) -> Result<Vec<Letter>, HistoryError> {
    let registers = register_classes(constraint);
    let mut choices: Vec<ClassChoices> = Vec::with_capacity(constraint.0.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
index <= constraint.0@.len(), choices@.len() == index, shape_wf(*constraint, *operands, *universes),
registers@.len() == constraint.0@.len(),
forall|i: int| 0 <= i < registers@.len() ==> registers@[i] == raw_register_class(constraint.0[i]),
forall|i: int| #![trigger choices@[i]] 0 <= i < index
    ==> option_views(choices@[i]@) == letter_axes(*constraint, *operands, *universes)[i],
forall|i: int| #![trigger choices@[i]] 0 <= i < index ==> class_sequence(choices@[i]@).no_duplicates(),
        decreases constraint.0@.len() - index))]
    while index < constraint.0.len() {
        choices.push(class_choices(
            &constraint.0[index],
            operands.register[index],
            &operands.constants[index],
            &universes[index],
        ));
        index += 1;
    }
    let mut refs: Vec<&ClassChoices> = Vec::with_capacity(choices.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
index <= choices@.len(), refs@.len() == index,
choices@.len() == constraint.0@.len(), shape_wf(*constraint, *operands, *universes),
registers@.len() == constraint.0@.len(),
forall|i: int| 0 <= i < registers@.len() ==> registers@[i] == raw_register_class(constraint.0[i]),
forall|i: int| #![trigger choices@[i]] 0 <= i < choices@.len()
    ==> option_views(choices@[i]@) == letter_axes(*constraint, *operands, *universes)[i],
forall|i: int| #![trigger choices@[i]] 0 <= i < choices@.len() ==> class_sequence(choices@[i]@).no_duplicates(),
forall|i: int| 0 <= i < index ==> *refs@[i] == choices@[i],
        decreases choices@.len() - index))]
    while index < choices.len() {
        refs.push(&choices[index]);
        index += 1;
    }
    proof! {
        assert forall|a: int| 0 <= a < refs@.len() implies class_sequence(refs@[a]@).no_duplicates() by {
            assert(*refs@[a] == choices@[a]);
            assert(class_sequence(choices@[a]@).no_duplicates());
        }
    }
    let result = product_letters(&refs, &registers)?;
    proof! {
        assert(refs@.map_values(|c: &ClassChoices| option_views(c@)) =~= letter_axes(*constraint, *operands, *universes));
        assert(registers@ =~= constraint.0@.map_values(|r: RegisterConstraint| raw_register_class(r)));
        lemma_letters_contract(*constraint, *operands, *universes, result@);
        lemma_letter_alpha_unique(*constraint, *operands, *universes, result@);
    }
    Ok(result)
}

#[verus_verify]
#[verus_spec(result => ensures result@.len() == constraint.0@.len(),
    forall|i: int| 0 <= i < result@.len() ==> result@[i] == raw_register_class(constraint.0[i]))]
fn register_classes(constraint: &Constraint) -> Vec<Class> {
    let mut result = Vec::with_capacity(constraint.0.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= constraint.0@.len(), result@.len() == index,
        forall|i: int| 0 <= i < index ==> result@[i] == raw_register_class(constraint.0[i]),
        decreases constraint.0@.len() - index))]
    while index < constraint.0.len() {
        result.push(class_of(&constraint.0[index]));
        index += 1;
    }
    result
}

/// The successor cases `succ(Γ, A)` (`def:successors`), grouped by refined constraint. Product
/// exhaustion propagates to the analyzer.
#[verus_verify]
#[verus_spec(result => requires atoms_wf(atoms@, universes@.len()), constraint_wf(*constraint),
    constraint@.len() == universes@.len(),
    inclusion::satisfiable(ndomains(*universes), implementation::constraint_of(constraint@)),
    ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(groups) ==> steps_result(*constraint, atoms@, *universes, groups@)
        && (universes_distinct(*universes) ==> constraint_sequence(group_constraints(groups@)).no_duplicates())
        && (forall|i: int| 0 <= i < groups@.len() ==> letter_sequence(groups@[i].1@).no_duplicates())
        && steps_alphas_unique(*constraint, atoms@, *universes, groups@))]
pub(crate) fn steps(
    constraint: &Constraint,
    atoms: &[Atom],
    universes: &Universes,
) -> Result<Vec<(Constraint, Vec<Letter>)>, HistoryError> {
    let operands = Operands::of(atoms, universes.len());
    let refinements = split(constraint, &operands, universes)?;
    let count = refinements.len();
    proof_decl! { let ghost source = refinements@; }
    let mut iter = refinements.into_iter();
    let mut result: Vec<(Constraint, Vec<Letter>)> = Vec::with_capacity(count);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        index <= count, count == source.len(), result@.len() == index,
        shape_wf(*constraint, operands, *universes), operands_of(operands, atoms@),
        constraint_views(source) == split_views(*constraint, operands, *universes),
        forall|i: int| 0 <= i < source.len() ==> constraint_wf(source[i]) && source[i]@.len() == universes@.len(),
        universes_distinct(*universes) ==> constraint_sequence(source).no_duplicates(),
        iter.obeys_prophetic_iter_laws(), iter.remaining() == source.subrange(index as int, count as int),
        forall|i: int| 0 <= i < index ==> result@[i].0 == source[i]
            && letter_views(result@[i].1@) == letters_views(source[i], operands, *universes)
            && letter_sequence(result@[i].1@).no_duplicates()
            && letter_alpha_unique(source[i], operands, *universes, result@[i].1@)
            && forall|j: int| 0 <= j < result@[i].1@.len() ==> letter_wf(result@[i].1@[j]) && result@[i].1@[j]@.classes.len() == universes@.len(),
        decreases count - index))]
    while index < count {
        let refined = match iter.next() {
            Some(value) => value,
            None => unreachable!(),
        };
        proof! { assert(refined == source[index as int]); }
        let choices = letters(&refined, &operands, universes)?;
        result.push((refined, choices));
        index += 1;
    }
    proof! {
            assert(group_constraints(result@) =~= source);
    assert forall|i: int| 0 <= i < result@.len() implies
        constraint_wf(result@[i].0) && result@[i].0@.len() == universes@.len()
        && letter_views(result@[i].1@) == letters_views(result@[i].0, operands, *universes)
        && letter_alpha_unique(result@[i].0, operands, *universes, result@[i].1@)
        && (forall|j: int| 0 <= j < result@[i].1@.len() ==> letter_wf(result@[i].1@[j])
            && result@[i].1@[j]@.classes.len() == universes@.len()) by {
        assert(result@[i].0 == source[i]);
        assert(letter_alpha_unique(source[i], operands, *universes, result@[i].1@));
    }
    lemma_steps_alphas_unique(*constraint, atoms@, *universes, operands, result@);
    assert(steps_result(*constraint, atoms@, *universes, result@));
    assert forall|i: int| 0 <= i < result@.len() implies letter_sequence(result@[i].1@).no_duplicates() by {
        assert(result@[i].0 == source[i]);
    }
    if universes_distinct(*universes) {
        assert(constraint_sequence(group_constraints(result@)) =~= constraint_sequence(source));
        assert(constraint_sequence(group_constraints(result@)).no_duplicates());
    }
    assert(steps_alphas_unique(*constraint, atoms@, *universes, result@));
        }
    Ok(result)
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

    /// The exact ordered register keys used by native constraint equality.
    pub open(crate) spec fn constraint_key(constraint: Constraint) -> Seq<(Option<u32>, Seq<u32>)> {
        constraint.0@.map_values(|r: RegisterConstraint| register_key(r))
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
            proof! {
                assert(constraint_key(*self).len() == self.0@.len());
                assert(constraint_key(*other).len() == other.0@.len());
            }
            if self.0.len() != other.0.len() {
                return false;
            }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
    index <= self.0@.len(), self.0@.len() == other.0@.len(),
    forall|i: int| 0 <= i < index ==> register_key(self.0@[i]) == register_key(other.0@[i]),
    decreases self.0@.len() - index))]
            while index < self.0.len() {
                if self.0[index] != other.0[index] {
                    proof! {
                        assert(constraint_key(*self)[index as int] == register_key(self.0@[index as int]));
                        assert(constraint_key(*other)[index as int] == register_key(other.0@[index as int]));
                        assert(constraint_key(*self)[index as int] != constraint_key(*other)[index as int]);
                    }
                    return false;
                }
                index += 1;
            }
            proof! { assert(constraint_key(*self) =~= constraint_key(*other)); }
            true
        }
    }
}

#[verus_verify]
#[verus_spec(result => requires register_wf(*current), canonical(constants@),
    ensures register_views(result@) == register_options(current@, register, codes(constants@), domain_view(*universe)),
        result@.len() == register_count(current@, register, constants@, *universe),
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

/// Advance the least-significant-last odometer, carrying through exhausted axes.
#[verus_verify]
#[verus_spec(result => requires row_valid(dimensions_view(sizes@), old(counters)@),
    row_rank(dimensions_view(sizes@), old(counters)@) + 1 < product_size(dimensions_view(sizes@)),
    ensures row_valid(dimensions_view(sizes@), final(counters)@),
        row_rank(dimensions_view(sizes@), final(counters)@) == row_rank(dimensions_view(sizes@), old(counters)@) + 1)]
fn advance_row(counters: &mut [usize], sizes: &[usize]) {
    proof_decl! { let ghost before = counters@; }
    let mut pivot = counters.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
pivot <= counters@.len(), counters@.len() == before.len(), before.len() == sizes@.len(),
before == old(counters)@,
        row_valid(dimensions_view(sizes@), before),
        row_rank(dimensions_view(sizes@), before) + 1 < product_size(dimensions_view(sizes@)),
        forall|i: int| 0 <= i < pivot ==> counters@[i] == before[i],
        forall|i: int| pivot <= i < counters@.len() ==> before[i] + 1 == sizes@[i] && counters@[i] == 0,
        decreases pivot))]
    while pivot > 0 {
        pivot -= 1;
        proof! {
            assert(counters@[pivot as int] == before[pivot as int]);
            assert(before[pivot as int] < dimensions_view(sizes@)[pivot as int]);
            assert(dimensions_view(sizes@)[pivot as int] == sizes@[pivot as int] as nat);
        }
        let next = counters[pivot] + 1;
        if next < sizes[pivot] {
            counters[pivot] = next;
            proof! { lemma_row_successor(dimensions_view(sizes@), before, counters@, pivot as int); }
            return;
        }
        counters[pivot] = 0;
    }
    proof! { lemma_row_max(dimensions_view(sizes@), before); }
    unreachable!()
}

#[verus_verify]
#[verus_spec(result => requires 1 <= choices@.len() <= history_syntax::MAX_ARITY,
    forall|a: int, i: int| 0 <= a < choices@.len() && 0 <= i < choices@[a]@.len() ==> register_wf(choices@[a]@[i]),
    ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(values) ==> values@.len() == product_size(choices@.map_values(|c: &RegisterChoices| c@.len()))
        && constraint_views(values@) == register_product(choices@.map_values(|c: &RegisterChoices| register_views(c@)))
        && ((forall|a: int| 0 <= a < choices@.len() ==> register_sequence(choices@[a]@).no_duplicates())
            ==> constraint_sequence(values@).no_duplicates())
        && forall|i: int| 0 <= i < values@.len() ==> constraint_wf(values@[i]) && values@[i]@.len() == choices@.len())]
fn product_constraints(choices: &[&RegisterChoices]) -> Result<Vec<Constraint>, HistoryError> {
    proof_decl! { let ghost axes = choices@.map_values(|c: &RegisterChoices| c@); }
    let mut sizes = Vec::with_capacity(choices.len());
    let mut counters = Vec::with_capacity(choices.len());
    let mut capacity: usize = 1;
    let mut axis = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        axis <= choices@.len(), sizes@.len() == axis, counters@.len() == axis,
        capacity == product_size(axis_sizes(axes).take(axis as int)),
        axes == choices@.map_values(|c: &RegisterChoices| c@),
forall|i: int| 0 <= i < axis ==> sizes@[i] == axes[i].len() && counters@[i] == 0,
forall|i: int| 0 <= i < axis ==> axes[i].len() <= usize::MAX,
        decreases choices@.len() - axis))]
    while axis < choices.len() {
        let size = choices[axis].len()?;
        capacity = match capacity.checked_mul(size) {
            Some(value) => value,
            None => return Err(HistoryError::graph_index_overflow()),
        };
        sizes.push(size);
        counters.push(0);
        proof! {
            assert(axis_sizes(axes).take(axis as int + 1).drop_last() =~= axis_sizes(axes).take(axis as int));
        }
        axis += 1;
    }
    proof! {
        assert(axis == axes.len());
        assert(axis_sizes(axes).take(axis as int) =~= axis_sizes(axes));
        assert(capacity == product_size(axis_sizes(axes)));
        assert forall|i: int| 0 <= i < axes.len() implies axes[i].len() <= usize::MAX by {
            assert(axes[i].len() == sizes@[i] as nat);
        }
    }
    let mut result = Vec::with_capacity(capacity);
    proof! {
        assert(dimensions_view(sizes@) =~= axis_sizes(axes));
        lemma_product_positive(axis_sizes(axes)); lemma_row_zero(axis_sizes(axes), counters@);
        lemma_register_product_members(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        result@.len() <= capacity, capacity == product_size(axis_sizes(axes)),
        1 <= choices@.len() <= history_syntax::MAX_ARITY, forall|a: int, i: int| 0 <= a < choices@.len() && 0 <= i < choices@[a]@.len() ==> register_wf(choices@[a]@[i]),
        axes == choices@.map_values(|c: &RegisterChoices| c@),
sizes@.len() == axes.len(), dimensions_view(sizes@) == axis_sizes(axes), counters@.len() == axes.len(),
forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
        result@.len() < capacity ==> row_valid(axis_sizes(axes), counters@) && row_rank(axis_sizes(axes), counters@) == result@.len(),
        product_done(axes, constraint_views(result@), result@.len()), constraint_positions(axes, result@),
        constraint_views(result@).subset_of(register_product(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)))),
        forall|i: int| 0 <= i < result@.len() ==> constraint_wf(result@[i]) && result@[i]@.len() == choices@.len(),
        decreases capacity - result@.len()))]
    while result.len() < capacity {
        let mut row: Vec<RegisterConstraint> = Vec::with_capacity(choices.len());
        let mut axis = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            axis <= choices@.len(), row@.len() == axis,
            axes == choices@.map_values(|c: &RegisterChoices| c@), row_valid(axis_sizes(axes), counters@),
dimensions_view(sizes@) == axis_sizes(axes),
forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
            forall|a: int, i: int| 0 <= a < choices@.len() && 0 <= i < choices@[a]@.len() ==> register_wf(choices@[a]@[i]),
            forall|i: int| 0 <= i < axis ==> row@[i]@ == axes[i][counters@[i] as int]@ && register_wf(row@[i]),
            decreases choices@.len() - axis))]
        while axis < choices.len() {
            row.push(choices[axis].get(counters[axis]));
            axis += 1;
        }
        let next = Constraint(row);
        proof_decl! { let ghost previous = result@; let ghost copied = next; }
        result.push(next);
        proof! {
                    lemma_constraint_views_push(previous, copied);
                    assert(copied@ =~= choice_view(axes, counters@));
                    lemma_constraint_position_push(axes, previous, copied, counters@);
                    lemma_product_step(axes, constraint_views(previous), constraint_views(result@), counters@, previous.len());
                    assert forall|i: int| 0 <= i < axes.len() implies register_views(axes[i]).contains(copied@[i]) by { lemma_register_view_at(axes[i], counters@[i] as int); }
        lemma_register_product_members(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)));
        assert(copied@.len() == axes.len());
        assert((register_product(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a)))).contains(copied@));
                }
        if result.len() < capacity {
            advance_row(&mut counters, &sizes);
        }
    }
    proof! {
    lemma_constraint_product_complete(axes, result@);
    assert(axis_sizes(axes) =~= choices@.map_values(|c: &RegisterChoices| c@.len()));
    assert(axes.map_values(|a: Seq<RegisterConstraint>| register_views(a))
        =~= choices@.map_values(|c: &RegisterChoices| register_views(c@)));
            if forall|i: int| 0 <= i < axes.len() ==> register_sequence(axes[i]).no_duplicates() {
                lemma_constraint_product_distinct(axes, result@);
            }
        }
    Ok(result)
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
#[verus_spec(result => ensures option_views(result@) == class_options(current@, register, codes(constants@), *universe),
        class_choices_wf(result), result@.len() == option_views(result@).len(),
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
#[verus_spec(result => requires 1 <= choices@.len() <= history_syntax::MAX_ARITY,
    registers@.len() == choices@.len(),
    ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(values) ==> values@.len() == product_size(choices@.map_values(|c: &ClassChoices| c@.len()))
        && letter_views(values@) == letter_product(choices@.map_values(|c: &ClassChoices| option_views(c@)), registers@)
        && ((forall|a: int| 0 <= a < choices@.len() ==> class_sequence(choices@[a]@).no_duplicates())
            ==> letter_sequence(values@).no_duplicates())
        && forall|i: int| 0 <= i < values@.len() ==> letter_wf(values@[i]) && values@[i]@.classes.len() == choices@.len())]
fn product_letters(
    choices: &[&ClassChoices],
    registers: &[Class],
) -> Result<Vec<Letter>, HistoryError> {
    proof_decl! { let ghost axes = choices@.map_values(|c: &ClassChoices| c@); }
    let mut sizes = Vec::with_capacity(choices.len());
    let mut counters = Vec::with_capacity(choices.len());
    let mut capacity: usize = 1;
    let mut axis = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        axis <= choices@.len(), sizes@.len() == axis, counters@.len() == axis,
        capacity == product_size(axis_sizes(axes).take(axis as int)),
        axes == choices@.map_values(|c: &ClassChoices| c@),
forall|i: int| 0 <= i < axis ==> sizes@[i] == axes[i].len() && counters@[i] == 0,
forall|i: int| 0 <= i < axis ==> axes[i].len() <= usize::MAX,
        decreases choices@.len() - axis))]
    while axis < choices.len() {
        let size = choices[axis].len()?;
        capacity = match capacity.checked_mul(size) {
            Some(value) => value,
            None => return Err(HistoryError::graph_index_overflow()),
        };
        sizes.push(size);
        counters.push(0);
        proof! {
            assert(axis_sizes(axes).take(axis as int + 1).drop_last() =~= axis_sizes(axes).take(axis as int));
        }
        axis += 1;
    }
    proof! {
        assert(axis == axes.len());
        assert(axis_sizes(axes).take(axis as int) =~= axis_sizes(axes));
        assert(capacity == product_size(axis_sizes(axes)));
        assert forall|i: int| 0 <= i < axes.len() implies axes[i].len() <= usize::MAX by {
            assert(axes[i].len() == sizes@[i] as nat);
        }
    }
    let mut result = Vec::with_capacity(capacity);
    proof! {
        assert(dimensions_view(sizes@) =~= axis_sizes(axes));
        lemma_product_positive(axis_sizes(axes)); lemma_row_zero(axis_sizes(axes), counters@);
        lemma_letter_product_members(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers@);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        result@.len() <= capacity, capacity == product_size(axis_sizes(axes)),
        1 <= choices@.len() <= history_syntax::MAX_ARITY, registers@.len() == choices@.len(),
        axes == choices@.map_values(|c: &ClassChoices| c@),
sizes@.len() == axes.len(), dimensions_view(sizes@) == axis_sizes(axes), counters@.len() == axes.len(),
forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
        result@.len() < capacity ==> row_valid(axis_sizes(axes), counters@) && row_rank(axis_sizes(axes), counters@) == result@.len(),
        letter_product_done(axes, registers@, letter_views(result@), result@.len()), letter_positions(axes, registers@, result@),
        letter_views(result@).subset_of(letter_product(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers@)),
        forall|i: int| 0 <= i < result@.len() ==> letter_wf(result@[i]) && result@[i]@.classes.len() == choices@.len(),
        decreases capacity - result@.len()))]
    while result.len() < capacity {
        let mut row = Vec::with_capacity(choices.len());
        let mut axis = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            axis <= choices@.len(), row@.len() == axis,
            axes == choices@.map_values(|c: &ClassChoices| c@), row_valid(axis_sizes(axes), counters@),
dimensions_view(sizes@) == axis_sizes(axes),
forall|i: int| 0 <= i < axes.len() ==> axes[i].len() <= usize::MAX,
            registers@.len() == choices@.len(),
            forall|i: int| 0 <= i < axis ==> class_option(row@[i]) == class_option(axes[i][counters@[i] as int]) ,
            decreases choices@.len() - axis))]
        while axis < choices.len() {
            row.push(choices[axis].get(counters[axis]));
            axis += 1;
        }
        let copied_registers = copy_slice(registers);
        let next = Letter {
            classes: row,
            registers: copied_registers,
        };
        proof_decl! { let ghost previous = result@; let ghost copied = next; }
        result.push(next);
        proof! {
                    lemma_letter_views_push(previous, copied);
        assert(copied@.classes =~= letter_choice_view(axes, registers@, counters@).classes);
        assert(copied@.registers =~= letter_choice_view(axes, registers@, counters@).registers);
        assert(copied@ == letter_choice_view(axes, registers@, counters@));
                    lemma_letter_position_push(axes, registers@, previous, copied, counters@);
                    lemma_letter_product_step(axes, registers@, letter_views(previous), letter_views(result@), counters@, previous.len());
                    assert forall|i: int| 0 <= i < axes.len() implies option_views(axes[i]).contains(copied@.classes[i]) by { lemma_option_view_at(axes[i], counters@[i] as int); }
        lemma_letter_product_members(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers@);
        assert(copied@.classes.len() == axes.len());
        assert((letter_product(axes.map_values(|a: Seq<Option<Class>>| option_views(a)), registers@)).contains(copied@));
                }
        if result.len() < capacity {
            advance_row(&mut counters, &sizes);
        }
    }
    proof! {
    lemma_letter_product_complete(axes, registers@, result@);
    assert(axis_sizes(axes) =~= choices@.map_values(|c: &ClassChoices| c@.len()));
    assert(axes.map_values(|a: Seq<Option<Class>>| option_views(a))
        =~= choices@.map_values(|c: &ClassChoices| option_views(c@)));
            if forall|i: int| 0 <= i < axes.len() ==> class_sequence(axes[i]).no_duplicates() {
                lemma_letter_product_distinct(axes, registers@, result@);
            }
        }
    Ok(result)
}

#[verus_verify]
pub(crate) struct RegisterChoices {
    pub(crate) equals: SmallVec<[ConstId; 4]>,
    pub(crate) last: Option<RegisterConstraint>,
}

#[verus_verify]
impl RegisterChoices {
    #[verus_spec(result => ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(n) ==> n == self@.len())]
    fn len(&self) -> Result<usize, HistoryError> {
        match self
            .equals
            .len()
            .checked_add(if self.last.is_some() { 1 } else { 0 })
        {
            Some(n) => Ok(n),
            None => Err(HistoryError::graph_index_overflow()),
        }
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
    #[verus_spec(result => ensures junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error is IndexOverflow,
        result matches Ok(n) ==> n == self@.len())]
    fn len(&self) -> Result<usize, HistoryError> {
        let extras = (if self.infinite { 1usize } else { 0 })
            + (if self.register { 1usize } else { 0 })
            + (if self.other.is_some() { 1usize } else { 0 });
        match self.names.len().checked_add(extras) {
            Some(n) => Ok(n),
            None => Err(HistoryError::graph_index_overflow()),
        }
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
