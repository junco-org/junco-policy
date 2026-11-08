//! Tail inclusion for every candidate matching a head.

use alloc::rc::Rc;
use alloc::vec::Vec;
use hashbrown::HashMap;
use history_semantics::SymbolicLanguage;
use history_syntax::{Component, Event, Head, RegexExpr, Rule, RuleMode};
use junco_core::compile::validate_component;
use junco_core::flat::{FlatHead, FlatPair};
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
use junco_core::{
    CompileError, ComponentValue, FlatEncoder, HistoryError, flatten_rule, lower_flat,
};

use crate::constraint::{
    COMPONENTS, Class, ConstId, Constraint, Letter, RegisterConstraint, Universes,
};
use crate::search::{SearchOutcome, search};
use crate::tables::Tables;

/// Bytes of runtime graph one search may be charged before it is reported `Exhausted`;
/// the runtime keeps `MAX_GRAPH_BYTES` per rule.
const GRAPH_BYTES: usize = 16 * 1024 * 1024;

/// The values each event component can take.
///
/// By default every component is infinite: it has more values than any analysis mentions, so a
/// counterexample may use a [fresh](Value::Fresh) value for it. Declare the values of a component
/// whose type has only a few, such as an action enum; treated as infinite, it could yield
/// counterexamples that need a value the type does not have.
#[derive(Clone, Debug)]
pub struct Domains<E: Event> {
    principals: Option<Vec<E::Principal>>,
    actions: Option<Vec<E::Action>>,
    resources: Option<Vec<E::Resource>>,
}

impl<E: Event> Domains<E> {
    /// Every component infinite.
    pub fn infinite() -> Self {
        Self {
            principals: None,
            actions: None,
            resources: None,
        }
    }

    /// Declares every principal that events and candidates can have.
    pub fn with_principals(mut self, values: impl IntoIterator<Item = E::Principal>) -> Self {
        self.principals = Some(values.into_iter().collect());
        self
    }

    /// Declares every action that events and candidates can have.
    pub fn with_actions(mut self, values: impl IntoIterator<Item = E::Action>) -> Self {
        self.actions = Some(values.into_iter().collect());
        self
    }

    /// Declares every resource that events and candidates can have.
    pub fn with_resources(mut self, values: impl IntoIterator<Item = E::Resource>) -> Self {
        self.resources = Some(values.into_iter().collect());
        self
    }
}

/// One component value of a counterexample.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Value<T> {
    /// A constant of the analysed rules, or a declared value of a finite component.
    Constant(T),
    /// A value of an infinite component that equals no constant of that component known to the
    /// analyzer. Within one counterexample, equal numbers denote equal values and different
    /// numbers different values.
    Fresh(usize),
}

/// The components of one event of a counterexample.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Components<E: Event> {
    /// The principal.
    pub principal: Value<E::Principal>,
    /// The action.
    pub action: Value<E::Action>,
    /// The resource.
    pub resource: Value<E::Resource>,
}

/// A candidate and a history on which an inclusion fails.
///
/// What failing means depends on the query; each query documents it. No shorter history fails.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample<E: Event> {
    /// Components of the candidate event that rule heads are matched against.
    pub candidate: Components<E>,
    /// Components of the events before the candidate, oldest first.
    pub history: Vec<Components<E>>,
}

/// Outcome of an analysis query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Inclusion<E: Event> {
    /// The inclusion holds for every candidate.
    Holds,
    /// The inclusion fails; the counterexample witnesses it.
    Counterexample(Counterexample<E>),
    /// A search exceeded its graph budget before deciding.
    Exhausted,
}

/// Constants of the analysed rules and domains, interned with ids per value. Ids start at 1, as
/// the `FlatEncoder` contract requires nonzero codes; the constant with id `i` is `values[i - 1]`.
struct Constants<E: Event> {
    ids: HashMap<ComponentValue<E>, ConstId>,
    values: Vec<ComponentValue<E>>,
}

impl<E: Event> Constants<E> {
    fn intern(&mut self, value: ComponentValue<E>) -> ConstId {
        if let Some(id) = self.ids.get(&value) {
            return *id;
        }
        let id = ConstId::try_from(self.values.len() + 1).expect("constant ids fit in u32");
        self.values.push(value);
        self.ids.insert(value, id);
        id
    }

    /// The universe of a declared finite component, in declaration order without repeats.
    fn universe(&mut self, values: impl IntoIterator<Item = ComponentValue<E>>) -> Rc<[ConstId]> {
        let mut ids = Vec::new();
        for value in values {
            let id = self.intern(value);
            if !ids.contains(&id) {
                ids.push(id);
            }
        }
        Rc::from(ids)
    }
}

/// Encodes each constant as its constant id, so compiled tails compare constant ids.
impl<E: Event> FlatEncoder<ComponentValue<E>> for Constants<E> {
    fn encode(&mut self, field: Component, value: &ComponentValue<E>) -> Result<u64, HistoryError> {
        validate_component(field, value)?;
        Ok(u64::from(self.intern(*value)))
    }
}

/// A counterexample component before its constant is resolved.
#[derive(Clone, Copy)]
enum Slot {
    Constant(ConstId),
    Fresh(usize),
}

/// Static analysis of tail inclusion: for every candidate a head matches, whether every history
/// in one tail is in another.
pub struct PolicyAnalyzer<E: Event> {
    constants: Constants<E>,
    universes: Universes,
}

impl<E: Event> PolicyAnalyzer<E> {
    /// Creates an analyzer for events whose components take the values of `domains`.
    pub fn new(domains: Domains<E>) -> Self {
        let mut constants = Constants {
            ids: HashMap::new(),
            values: Vec::new(),
        };
        let universes: Universes = [
            domains.principals.map(|values| {
                constants.universe(values.into_iter().map(ComponentValue::Principal))
            }),
            domains
                .actions
                .map(|values| constants.universe(values.into_iter().map(ComponentValue::Action))),
            domains
                .resources
                .map(|values| constants.universe(values.into_iter().map(ComponentValue::Resource))),
        ];
        Self {
            constants,
            universes,
        }
    }

    /// Whether, for every candidate that `head` matches, every history in `left` is in `right`.
    ///
    /// Both tails may refer to the head's variables. A counterexample is a matching candidate and
    /// a history in `left` but not in `right`.
    pub fn tail_included(
        &mut self,
        head: &Head<E>,
        left: &RegexExpr<E>,
        right: &RegexExpr<E>,
    ) -> Result<Inclusion<E>, CompileError> {
        let left = flatten_rule(
            &Rule::new(RuleMode::Forbid, head.clone(), left.clone()),
            &mut Unmetered,
            &mut ObservationWorld,
        )?;
        let right = flatten_rule(
            &Rule::new(RuleMode::Forbid, head.clone(), right.clone()),
            &mut Unmetered,
            &mut ObservationWorld,
        )?;
        let constants = self.head_constants(&left.source.head);
        let (left, right) = (self.encode(&left.source)?, self.encode(&right.source)?);
        Ok(match Constraint::head(constants, &self.universes) {
            Some(constraint) => {
                let mut tables = Tables::default();
                let (left, right) = (tables.append(&left)?, tables.append(&right)?);
                self.decide(constraint, tables.difference(left, right)?)?
            }
            None => Inclusion::Holds,
        })
    }

    /// The constants that a head pins; variables leave their register free.
    fn head_constants(
        &mut self,
        head: &[FlatHead<ComponentValue<E>>; COMPONENTS],
    ) -> [Option<ConstId>; COMPONENTS] {
        head.each_ref().map(|field| match field {
            FlatHead::Constant(value) => Some(self.constants.intern(*value)),
            FlatHead::Bind | FlatHead::Any => None,
        })
    }

    /// `source` with each constant replaced by its constant id.
    fn encode(
        &mut self,
        source: &FlatPair<ComponentValue<E>>,
    ) -> Result<FlatPair<u64>, HistoryError> {
        lower_flat(
            source,
            &mut self.constants,
            &mut Unmetered,
            &mut ObservationWorld,
        )
    }

    /// Decides whether `difference` is empty under `constraint`.
    fn decide(
        &self,
        constraint: Constraint,
        difference: FlatPair<u64>,
    ) -> Result<Inclusion<E>, HistoryError> {
        let outcome = SymbolicLanguage::compile(&difference, GRAPH_BYTES)
            .and_then(|mut language| search(&mut language, &self.universes, constraint));
        match outcome {
            Ok(SearchOutcome::Holds) => Ok(Inclusion::Holds),
            Err(HistoryError::GraphLimit { .. }) => Ok(Inclusion::Exhausted),
            Ok(SearchOutcome::Refuted(refutation)) => Ok(Inclusion::Counterexample(
                self.counterexample(&refutation.constraint, &refutation.letters),
            )),
            Err(error) => Err(error),
        }
    }

    /// Builds a candidate and history from a refuting constraint and letter sequence.
    ///
    /// A register takes the constant the constraint pins it to, the first remaining value of a
    /// finite domain, or a fresh value. A component that a letter leaves unmatched takes a fresh
    /// value, distinct from every other one; a finite component never is unmatched.
    fn counterexample(&self, constraint: &Constraint, letters: &[Letter]) -> Counterexample<E> {
        let mut fresh = 0;
        let mut next = || {
            fresh += 1;
            Slot::Fresh(fresh - 1)
        };
        let candidate: [Slot; COMPONENTS] = core::array::from_fn(|component| {
            let register = &constraint.0[component];
            match (register, &self.universes[component]) {
                (RegisterConstraint::Equals(value), _) => Slot::Constant(*value),
                (RegisterConstraint::Differs(_), Some(values)) => Slot::Constant(
                    register
                        .witness(values)
                        .expect("constraints are satisfiable in their universe"),
                ),
                (RegisterConstraint::Differs(_), None) => next(),
            }
        });
        let history = letters
            .iter()
            .map(|letter| {
                core::array::from_fn(|component| match letter.class(component) {
                    Some(Class::Constant(value)) => Slot::Constant(value),
                    Some(Class::Register) => candidate[component],
                    None => next(),
                })
            })
            .collect::<Vec<[Slot; COMPONENTS]>>();
        Counterexample {
            candidate: self.components(candidate),
            history: history
                .into_iter()
                .map(|slots| self.components(slots))
                .collect(),
        }
    }

    fn components(&self, [principal, action, resource]: [Slot; COMPONENTS]) -> Components<E> {
        Components {
            principal: self.value(principal, |value| match value {
                ComponentValue::Principal(value) => value,
                _ => unreachable!("principal constants are principals"),
            }),
            action: self.value(action, |value| match value {
                ComponentValue::Action(value) => value,
                _ => unreachable!("action constants are actions"),
            }),
            resource: self.value(resource, |value| match value {
                ComponentValue::Resource(value) => value,
                _ => unreachable!("resource constants are resources"),
            }),
        }
    }

    fn value<T>(&self, slot: Slot, project: impl FnOnce(ComponentValue<E>) -> T) -> Value<T> {
        match slot {
            Slot::Constant(id) => Value::Constant(project(self.constants.values[id as usize - 1])),
            Slot::Fresh(number) => Value::Fresh(number),
        }
    }
}
