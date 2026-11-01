//! Register constraints, constraint splitting, and letters: the finite alphabet of the inclusion
//! search.
//!
//! A constraint records what is known about each register `κ_c`, the value of component `c` of the
//! candidate event. Splitting refines a constraint until it decides every comparison between a
//! register and a constant that a set of atoms makes. Relative to such a constraint, a letter names
//! one class of events that no atom of the set can tell apart: for each component, the operand class
//! the component equals, or none of them.

use hashbrown::HashMap;
use smallvec::SmallVec;

use super::super::component::{CompiledAtomPattern, ResolvedValue};
use super::super::source::ComponentPattern;
use super::Alphabet;

/// Number of event components, and so of registers.
pub(super) const COMPONENTS: usize = 3;

/// Operand an atom compares its component with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Operand<'arena> {
    /// The component's register.
    Register,
    /// A constant of the component's domain.
    Constant(ResolvedValue<'arena>),
}

/// Splits an atom into the index of the component it tests and the operand it compares with.
///
/// Variables are registers: a head binds at most one variable per component.
pub(super) fn atom_operand(atom: CompiledAtomPattern<'_>) -> (usize, Operand<'_>) {
    match atom {
        CompiledAtomPattern::Principal(ComponentPattern::Constant(value)) => {
            (0, Operand::Constant(ResolvedValue::Principal(value)))
        }
        CompiledAtomPattern::Principal(ComponentPattern::Variable(_)) => (0, Operand::Register),
        CompiledAtomPattern::Action(ComponentPattern::Constant(value)) => {
            (1, Operand::Constant(ResolvedValue::Action(value)))
        }
        CompiledAtomPattern::Action(ComponentPattern::Variable(_)) => (1, Operand::Register),
        CompiledAtomPattern::Resource(ComponentPattern::Constant(value)) => {
            (2, Operand::Constant(ResolvedValue::Resource(value)))
        }
        CompiledAtomPattern::Resource(ComponentPattern::Variable(_)) => (2, Operand::Register),
    }
}

/// What a constraint states about one register.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum RegisterConstraint<'arena> {
    /// The register equals this constant.
    Equals(ResolvedValue<'arena>),
    /// The register differs from every listed constant (sorted and deduplicated).
    Differs(SmallVec<[ResolvedValue<'arena>; 2]>),
}

impl<'arena> RegisterConstraint<'arena> {
    fn entails_equal(&self, value: ResolvedValue<'arena>) -> bool {
        matches!(self, Self::Equals(equal) if *equal == value)
    }

    fn entails_differ(&self, value: ResolvedValue<'arena>) -> bool {
        match self {
            Self::Equals(equal) => *equal != value,
            Self::Differs(differs) => differs.binary_search(&value).is_ok(),
        }
    }

    /// Whether the comparison between the register and `value` is settled.
    fn decides(&self, value: ResolvedValue<'arena>) -> bool {
        matches!(self, Self::Equals(_)) || self.entails_differ(value)
    }

    fn entails(&self, other: &Self) -> bool {
        match other {
            Self::Equals(value) => self.entails_equal(*value),
            Self::Differs(values) => values.iter().all(|value| self.entails_differ(*value)),
        }
    }
}

/// Satisfiable conjunction of register literals, one entry per component.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Constraint<'arena>(pub(super) [RegisterConstraint<'arena>; COMPONENTS]);

impl<'arena> Constraint<'arena> {
    /// The constraint satisfied by every valuation.
    pub(super) fn unconstrained() -> Self {
        Self(std::array::from_fn(|_| {
            RegisterConstraint::Differs(SmallVec::new())
        }))
    }

    /// The constraint fixing the registers of the components a head constant pins.
    pub(super) fn equations(values: [Option<ResolvedValue<'arena>>; COMPONENTS]) -> Self {
        Self(values.map(|value| match value {
            Some(value) => RegisterConstraint::Equals(value),
            None => RegisterConstraint::Differs(SmallVec::new()),
        }))
    }

    /// Whether every valuation satisfying `self` satisfies `other`.
    pub(super) fn entails(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip(&other.0)
            .all(|(mine, theirs)| mine.entails(theirs))
    }
}

/// Index of an interned constraint.
pub(super) type ConstraintId = u32;

/// Interned constraints with memoised entailment, local to one search.
#[derive(Default)]
pub(super) struct ConstraintTable<'arena> {
    constraints: Vec<Constraint<'arena>>,
    ids: HashMap<Constraint<'arena>, ConstraintId>,
    entailments: HashMap<(ConstraintId, ConstraintId), bool>,
}

impl<'arena> ConstraintTable<'arena> {
    pub(super) fn intern(&mut self, constraint: Constraint<'arena>) -> ConstraintId {
        if let Some(id) = self.ids.get(&constraint) {
            return *id;
        }
        let id = ConstraintId::try_from(self.constraints.len()).expect("constraint ids fit in u32");
        self.constraints.push(constraint.clone());
        self.ids.insert(constraint, id);
        id
    }

    pub(super) fn get(&self, id: ConstraintId) -> &Constraint<'arena> {
        &self.constraints[id as usize]
    }

    /// Whether every valuation satisfying constraint `left` satisfies constraint `right`.
    pub(super) fn entails(&mut self, left: ConstraintId, right: ConstraintId) -> bool {
        if left == right {
            return true;
        }
        let constraints = &self.constraints;
        *self
            .entailments
            .entry((left, right))
            .or_insert_with(|| constraints[left as usize].entails(&constraints[right as usize]))
    }
}

/// Representative of a class of operands that a constraint makes equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Class<'arena> {
    /// The class of a register that the constraint does not pin to a constant.
    Register,
    /// The class of a constant, possibly together with a register pinned to it.
    Constant(ResolvedValue<'arena>),
}

/// One class of events relative to a constraint and a set of atoms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Letter<'arena> {
    /// Class that each component equals, or `None` when it equals no operand of the atom set.
    classes: [Option<Class<'arena>>; COMPONENTS],
    /// Class of each register under the letter's constraint.
    registers: [Class<'arena>; COMPONENTS],
}

impl<'arena> Letter<'arena> {
    /// Whether events of this letter satisfy the equality `atom`, which must belong to the atom set
    /// the letter was built for.
    pub(super) fn holds(&self, atom: CompiledAtomPattern<'arena>) -> bool {
        let (component, operand) = atom_operand(atom);
        let class = match operand {
            Operand::Register => self.registers[component],
            Operand::Constant(value) => Class::Constant(value),
        };
        self.classes[component] == Some(class)
    }

    /// Class that component `component` of the letter's events equals, if any.
    pub(super) fn class(&self, component: usize) -> Option<Class<'arena>> {
        self.classes[component]
    }
}

/// Operands that a set of atoms compares with each component.
#[derive(Default)]
pub(super) struct Operands<'arena> {
    register: [bool; COMPONENTS],
    constants: [SmallVec<[ResolvedValue<'arena>; 4]>; COMPONENTS],
}

impl<'arena> Operands<'arena> {
    /// Collects the operands of `atoms`.
    pub(super) fn of(atoms: &[CompiledAtomPattern<'arena>]) -> Self {
        let mut operands = Self::default();
        for atom in atoms {
            operands.add(*atom);
        }
        operands.normalize();
        operands
    }

    /// Operands that compare each register with the listed constants.
    pub(super) fn pairs(pairs: impl IntoIterator<Item = (usize, ResolvedValue<'arena>)>) -> Self {
        let mut operands = Self::default();
        for (component, value) in pairs {
            operands.register[component] = true;
            operands.constants[component].push(value);
        }
        operands.normalize();
        operands
    }

    fn add(&mut self, atom: CompiledAtomPattern<'arena>) {
        match atom_operand(atom) {
            (component, Operand::Register) => self.register[component] = true,
            (component, Operand::Constant(value)) => self.constants[component].push(value),
        }
    }

    fn normalize(&mut self) {
        for constants in &mut self.constants {
            constants.sort_unstable();
            constants.dedup();
        }
    }
}

/// `Split(Γ, A)`: refinements of `constraint` that decide every register–constant pair of the
/// operands, one per satisfiable choice of literals.
pub(super) fn split<'arena>(
    constraint: &Constraint<'arena>,
    operands: &Operands<'arena>,
) -> Vec<Constraint<'arena>> {
    let options: [SmallVec<[RegisterConstraint<'arena>; 2]>; COMPONENTS] =
        std::array::from_fn(|component| {
            let current = &constraint.0[component];
            let undecided = if operands.register[component] {
                operands.constants[component]
                    .iter()
                    .copied()
                    .filter(|value| !current.decides(*value))
                    .collect::<SmallVec<[ResolvedValue<'arena>; 4]>>()
            } else {
                SmallVec::new()
            };
            let RegisterConstraint::Differs(differs) = current else {
                return SmallVec::from_elem(current.clone(), 1);
            };
            if undecided.is_empty() {
                return SmallVec::from_elem(current.clone(), 1);
            }
            // A register equals at most one constant: either it equals one undecided constant,
            // which settles all others, or it differs from all of them.
            let mut options = undecided
                .iter()
                .map(|value| RegisterConstraint::Equals(*value))
                .collect::<SmallVec<[RegisterConstraint<'arena>; 2]>>();
            let mut all_differ = differs.clone();
            all_differ.extend(undecided);
            all_differ.sort_unstable();
            all_differ.dedup();
            options.push(RegisterConstraint::Differs(all_differ));
            options
        });
    product(options.each_ref().map(SmallVec::as_slice), |choice| {
        Constraint(choice.map(Clone::clone))
    })
}

/// `Λ(Γ, A)`: the letters for a constraint that decides the operands.
fn letters<'arena>(
    constraint: &Constraint<'arena>,
    operands: &Operands<'arena>,
) -> Vec<Letter<'arena>> {
    let registers = register_classes(constraint);
    let choices: [SmallVec<[Option<Class<'arena>>; 4]>; COMPONENTS] =
        std::array::from_fn(|component| {
            let mut classes = operands.constants[component]
                .iter()
                .map(|value| Class::Constant(*value))
                .collect::<SmallVec<[Class<'arena>; 4]>>();
            if operands.register[component] {
                classes.push(registers[component]);
            }
            classes.sort_unstable();
            classes.dedup();
            std::iter::once(None)
                .chain(classes.into_iter().map(Some))
                .collect()
        });
    product(choices.each_ref().map(SmallVec::as_slice), |classes| {
        Letter {
            classes: classes.map(|class| *class),
            registers,
        }
    })
}

/// The same letters as [`letters`], found by enumerating every truth assignment to `atoms` and
/// keeping the satisfiable ones, as a minterm construction does.
fn minterm_letters<'arena>(
    constraint: &Constraint<'arena>,
    atoms: &[CompiledAtomPattern<'arena>],
) -> Vec<Letter<'arena>> {
    assert!(
        atoms.len() < usize::BITS as usize,
        "minterm enumeration supports fewer than {} atoms",
        usize::BITS
    );
    let registers = register_classes(constraint);
    let class_of = |atom: CompiledAtomPattern<'arena>| match atom_operand(atom) {
        (component, Operand::Register) => (component, registers[component]),
        (component, Operand::Constant(value)) => (component, Class::Constant(value)),
    };
    let mut letters = Vec::new();
    'assignments: for assignment in 0..(1_usize << atoms.len()) {
        let mut classes = [None; COMPONENTS];
        for (index, atom) in atoms.iter().enumerate() {
            if assignment & (1 << index) == 0 {
                continue;
            }
            let (component, class) = class_of(*atom);
            match classes[component] {
                None => classes[component] = Some(class),
                Some(existing) if existing == class => {}
                Some(_) => continue 'assignments,
            }
        }
        let letter = Letter { classes, registers };
        if atoms
            .iter()
            .enumerate()
            .all(|(index, atom)| letter.holds(*atom) == (assignment & (1 << index) != 0))
        {
            letters.push(letter);
        }
    }
    letters
}

fn register_classes<'arena>(constraint: &Constraint<'arena>) -> [Class<'arena>; COMPONENTS] {
    std::array::from_fn(|component| match &constraint.0[component] {
        RegisterConstraint::Equals(value) => Class::Constant(*value),
        RegisterConstraint::Differs(_) => Class::Register,
    })
}

/// `Steps(Γ, A)`, grouped by refined constraint.
pub(super) fn steps<'arena>(
    constraint: &Constraint<'arena>,
    atoms: &[CompiledAtomPattern<'arena>],
    alphabet: Alphabet,
) -> Vec<(Constraint<'arena>, Vec<Letter<'arena>>)> {
    let operands = Operands::of(atoms);
    split(constraint, &operands)
        .into_iter()
        .map(|refined| {
            let letters = match alphabet {
                Alphabet::Letters => letters(&refined, &operands),
                Alphabet::Minterms => minterm_letters(&refined, atoms),
            };
            (refined, letters)
        })
        .collect()
}

/// Cartesian product of per-component choices, mapped through `build`.
fn product<T, R>(
    choices: [&[T]; COMPONENTS],
    mut build: impl FnMut([&T; COMPONENTS]) -> R,
) -> Vec<R> {
    let mut result = Vec::with_capacity(choices.iter().map(|choice| choice.len()).product());
    for first in choices[0] {
        for second in choices[1] {
            for third in choices[2] {
                result.push(build([first, second, third]));
            }
        }
    }
    result
}
