//! Constraints on the candidate, their splits, and letters: the finite alphabet of the search.
//!
//! A constraint records what is known about each register `κ_c`, the candidate's value of
//! component `c`. Splitting refines a constraint until it decides every comparison between a
//! register and a constant that a set of atoms makes; a register of a finite domain is fixed to
//! one value instead. Relative to such a constraint, a letter names one class of events that no
//! atom of the set can tell apart: for each component, the operand it equals, or none of them.

use alloc::rc::Rc;
use alloc::vec::Vec;
use hashbrown::HashMap;
use smallvec::SmallVec;

/// Number of event components, and so of registers.
pub(crate) const COMPONENTS: usize = 3;

/// Identity of an interned constant; constants of different components never share one.
pub(crate) type ConstId = u32;

/// The declared values of one component, in declaration order, or `None` if it is infinite.
pub(crate) type Universe = Option<Rc<[ConstId]>>;

/// The universe of each component.
pub(crate) type Universes = [Universe; COMPONENTS];

/// Operand an atom compares its component with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Operand {
    /// The candidate's value of the same component.
    Register,
    /// A constant of the component.
    Constant(ConstId),
}

/// Equality between one component of an event and an operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Atom {
    /// Index of the compared component.
    pub(crate) component: usize,
    /// The operand it is compared with.
    pub(crate) operand: Operand,
}

/// What a constraint states about one register.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RegisterConstraint {
    /// The register equals this constant.
    Equals(ConstId),
    /// The register differs from every listed constant (sorted and deduplicated).
    Differs(SmallVec<[ConstId; 2]>),
}

impl RegisterConstraint {
    fn entails_equal(&self, value: ConstId) -> bool {
        matches!(self, Self::Equals(equal) if *equal == value)
    }

    fn entails_differ(&self, value: ConstId) -> bool {
        match self {
            Self::Equals(equal) => *equal != value,
            Self::Differs(differs) => differs.binary_search(&value).is_ok(),
        }
    }

    /// Whether the comparison between the register and `value` is settled.
    fn decides(&self, value: ConstId) -> bool {
        matches!(self, Self::Equals(_)) || self.entails_differ(value)
    }

    fn entails(&self, other: &Self) -> bool {
        match other {
            Self::Equals(value) => self.entails_equal(*value),
            Self::Differs(values) => values.iter().all(|value| self.entails_differ(*value)),
        }
    }

    /// Whether some value of `universe` satisfies the constraint.
    fn satisfiable(&self, universe: &Universe) -> bool {
        match (self, universe) {
            (_, None) => true,
            (Self::Equals(value), Some(values)) => values.contains(value),
            (Self::Differs(differs), Some(values)) => values
                .iter()
                .any(|value| differs.binary_search(value).is_err()),
        }
    }

    /// The first value of a finite `universe` that satisfies the constraint.
    pub(crate) fn witness(&self, universe: &[ConstId]) -> Option<ConstId> {
        match self {
            Self::Equals(value) => universe.contains(value).then_some(*value),
            Self::Differs(differs) => universe
                .iter()
                .copied()
                .find(|value| differs.binary_search(value).is_err()),
        }
    }
}

/// Satisfiable conjunction of register literals, one entry per component.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Constraint(pub(crate) [RegisterConstraint; COMPONENTS]);

impl Constraint {
    /// The constraint fixing the registers that head constants pin, or `None` if some register
    /// can take no value of its universe.
    pub(crate) fn head(
        constants: [Option<ConstId>; COMPONENTS],
        universes: &Universes,
    ) -> Option<Self> {
        let constraint = Self(constants.map(|constant| match constant {
            Some(value) => RegisterConstraint::Equals(value),
            None => RegisterConstraint::Differs(SmallVec::new()),
        }));
        constraint
            .0
            .iter()
            .zip(universes)
            .all(|(register, universe)| register.satisfiable(universe))
            .then_some(constraint)
    }

    /// Whether every valuation satisfying `self` satisfies `other`, read syntactically.
    pub(crate) fn entails(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip(&other.0)
            .all(|(mine, theirs)| mine.entails(theirs))
    }
}

/// Index of an interned constraint.
pub(crate) type ConstraintId = u32;

/// Interned constraints, local to one search.
#[derive(Default)]
pub(crate) struct ConstraintTable {
    constraints: Vec<Constraint>,
    ids: HashMap<Constraint, ConstraintId>,
}

impl ConstraintTable {
    pub(crate) fn intern(&mut self, constraint: Constraint) -> ConstraintId {
        if let Some(id) = self.ids.get(&constraint) {
            return *id;
        }
        let id = ConstraintId::try_from(self.constraints.len()).expect("constraint ids fit in u32");
        self.constraints.push(constraint.clone());
        self.ids.insert(constraint, id);
        id
    }

    pub(crate) fn get(&self, id: ConstraintId) -> &Constraint {
        &self.constraints[id as usize]
    }
}

/// Representative of a class of operands that a constraint makes equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Class {
    /// The class of a register that the constraint does not pin to a constant.
    Register,
    /// The class of a constant, possibly together with a register pinned to it.
    Constant(ConstId),
}

/// One class of events relative to a constraint and a set of atoms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Letter {
    /// Class that each component equals, or `None` for any value outside the named classes.
    classes: [Option<Class>; COMPONENTS],
    /// Class of each register under the letter's constraint.
    registers: [Class; COMPONENTS],
}

impl Letter {
    /// Whether events of this letter satisfy `atom`, which must belong to the atom set the letter
    /// was built for.
    pub(crate) fn holds(&self, atom: Atom) -> bool {
        let class = match atom.operand {
            Operand::Register => self.registers[atom.component],
            Operand::Constant(value) => Class::Constant(value),
        };
        self.classes[atom.component] == Some(class)
    }

    /// Class that component `component` of the letter's events equals, if any.
    pub(crate) fn class(&self, component: usize) -> Option<Class> {
        self.classes[component]
    }
}

/// Operands that a set of atoms compares with each component.
#[derive(Default)]
pub(crate) struct Operands {
    register: [bool; COMPONENTS],
    constants: [SmallVec<[ConstId; 4]>; COMPONENTS],
}

impl Operands {
    /// Collects the operands of `atoms`.
    pub(crate) fn of(atoms: &[Atom]) -> Self {
        let mut operands = Self::default();
        for atom in atoms {
            match atom.operand {
                Operand::Register => operands.register[atom.component] = true,
                Operand::Constant(value) => operands.constants[atom.component].push(value),
            }
        }
        operands.normalize();
        operands
    }

    /// Operands that compare each register with the listed constants.
    pub(crate) fn pairs(pairs: impl IntoIterator<Item = (usize, ConstId)>) -> Self {
        let mut operands = Self::default();
        for (component, value) in pairs {
            operands.register[component] = true;
            operands.constants[component].push(value);
        }
        operands.normalize();
        operands
    }

    fn normalize(&mut self) {
        for constants in &mut self.constants {
            constants.sort_unstable();
            constants.dedup();
        }
    }
}

/// `Split(Γ, A)`: refinements of `constraint` that decide every register–constant pair of the
/// operands, one per satisfiable choice of literals. A finite register the operands mention is
/// fixed to each of its remaining values instead, so that letters never depend on its value.
pub(crate) fn split(
    constraint: &Constraint,
    operands: &Operands,
    universes: &Universes,
) -> Vec<Constraint> {
    let options: [SmallVec<[RegisterConstraint; 2]>; COMPONENTS] =
        core::array::from_fn(|component| {
            let current = &constraint.0[component];
            let RegisterConstraint::Differs(differs) = current else {
                return SmallVec::from_elem(current.clone(), 1);
            };
            if !operands.register[component] {
                return SmallVec::from_elem(current.clone(), 1);
            }
            if let Some(values) = &universes[component] {
                return values
                    .iter()
                    .filter(|value| differs.binary_search(value).is_err())
                    .map(|value| RegisterConstraint::Equals(*value))
                    .collect();
            }
            let undecided = operands.constants[component]
                .iter()
                .copied()
                .filter(|value| !current.decides(*value))
                .collect::<SmallVec<[ConstId; 4]>>();
            if undecided.is_empty() {
                return SmallVec::from_elem(current.clone(), 1);
            }
            // A register equals at most one constant: either one undecided constant, which settles
            // all others, or none of them.
            let mut options = undecided
                .iter()
                .map(|value| RegisterConstraint::Equals(*value))
                .collect::<SmallVec<[RegisterConstraint; 2]>>();
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

/// `Λ(Γ, A)`: the letters for a constraint that decides the operands. For a finite component,
/// the values outside the named classes form one class, represented by the first of them.
fn letters(constraint: &Constraint, operands: &Operands, universes: &Universes) -> Vec<Letter> {
    let registers = register_classes(constraint);
    let choices: [SmallVec<[Option<Class>; 4]>; COMPONENTS] = core::array::from_fn(|component| {
        let universe = &universes[component];
        let mut classes = operands.constants[component]
            .iter()
            .filter(|value| {
                universe
                    .as_ref()
                    .is_none_or(|values| values.contains(value))
            })
            .map(|value| Class::Constant(*value))
            .collect::<SmallVec<[Class; 4]>>();
        if operands.register[component] {
            classes.push(registers[component]);
        }
        classes.sort_unstable();
        classes.dedup();
        match universe {
            None => core::iter::once(None)
                .chain(classes.into_iter().map(Some))
                .collect(),
            Some(values) => {
                let rest = values
                    .iter()
                    .find(|value| classes.binary_search(&Class::Constant(**value)).is_err())
                    .map(|value| Class::Constant(*value));
                classes.into_iter().chain(rest).map(Some).collect()
            }
        }
    });
    product(choices.each_ref().map(SmallVec::as_slice), |classes| {
        Letter {
            classes: classes.map(|class| *class),
            registers,
        }
    })
}

fn register_classes(constraint: &Constraint) -> [Class; COMPONENTS] {
    core::array::from_fn(|component| match &constraint.0[component] {
        RegisterConstraint::Equals(value) => Class::Constant(*value),
        RegisterConstraint::Differs(_) => Class::Register,
    })
}

/// `Steps(Γ, A)`, grouped by refined constraint.
pub(crate) fn steps(
    constraint: &Constraint,
    atoms: &[Atom],
    universes: &Universes,
) -> Vec<(Constraint, Vec<Letter>)> {
    let operands = Operands::of(atoms);
    split(constraint, &operands, universes)
        .into_iter()
        .map(|refined| {
            let letters = letters(&refined, &operands, universes);
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
