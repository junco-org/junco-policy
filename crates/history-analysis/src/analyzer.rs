//! Policy questions answered by inclusion: redundancy, strictness, and vacuity.

use alloc::rc::Rc;
use alloc::vec::Vec;
use hashbrown::HashMap;
use history_syntax::{Event, Head, RegexExpr, Rule, RuleMode};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
use junco_core::{CompileError, ComponentValue, flatten_rule};
use smallvec::SmallVec;

use crate::constraint::{
    Atom, COMPONENTS, Class, ConstId, Constraint, Letter, Operand, Operands, RegisterConstraint,
    Universes, split,
};
use crate::expression::{ExprId, Expressions, TestId};
use crate::search::{SearchOptions, SearchOutcome, SearchStats, search};

/// Handle of a rule added to a [`PolicyAnalyzer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleId(usize);

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

impl<E: Event> Default for Domains<E> {
    fn default() -> Self {
        Self::infinite()
    }
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
    /// A search exceeded [`SearchOptions::max_items`] before deciding.
    Exhausted,
}

/// Outcome of an analysis query together with the work it took.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verdict<E: Event> {
    /// Whether the inclusion holds.
    pub inclusion: Inclusion<E>,
    /// Work done by the inclusion searches.
    pub stats: SearchStats,
}

impl<E: Event> Verdict<E> {
    /// Whether the inclusion holds.
    pub fn holds(&self) -> bool {
        matches!(self.inclusion, Inclusion::Holds)
    }
}

/// Constants of the analysed rules and domains, interned with ids per value.
struct Constants<E: Event> {
    ids: HashMap<ComponentValue<E>, ConstId>,
    values: Vec<ComponentValue<E>>,
}

impl<E: Event> Constants<E> {
    fn intern(&mut self, value: ComponentValue<E>) -> ConstId {
        if let Some(id) = self.ids.get(&value) {
            return *id;
        }
        let id = ConstId::try_from(self.values.len()).expect("constant ids fit in u32");
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

/// One analysed rule: its head constants, the constraint they impose on the candidate (`None` if
/// no candidate can match), and the language of histories it denies.
struct AnalyzedRule {
    constants: [Option<ConstId>; COMPONENTS],
    constraint: Option<Constraint>,
    denial: ExprId,
}

/// A counterexample component before its constant is resolved.
#[derive(Clone, Copy)]
enum Slot {
    Constant(ConstId),
    Fresh(usize),
}

/// Static analysis of rule tables by inclusion between tails.
///
/// A rule denies a candidate and history when its head matches the candidate and the history is
/// inside its tail (`Forbid`) or outside it (`Require`). The analyzer decides, for every
/// candidate, whether the denials of one rule are covered by those of others, and whether a rule
/// can fire.
///
/// # Example
///
/// ```
/// use history_analysis::{Domains, PolicyAnalyzer};
/// use history_syntax::{
///     AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
/// };
///
/// #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// enum Action {
///     Read,
///     Edit,
/// }
///
/// #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// struct Access {
///     principal: u32,
///     action: Action,
///     resource: u32,
/// }
///
/// impl Event for Access {
///     type Principal = u32;
///     type Action = Action;
///     type Resource = u32;
///
///     fn principal(self) -> u32 {
///         self.principal
///     }
///     fn action(self) -> Action {
///         self.action
///     }
///     fn resource(self) -> u32 {
///         self.resource
///     }
/// }
///
/// let head = Head::<Access>::new(
///     ComponentPattern::variable("p"),
///     ComponentPattern::constant(Action::Edit),
///     ComponentPattern::constant(7_u32),
/// );
/// let read_by_p = TestExpr::and([
///     TestExpr::atom(Comparison::Eq, AtomPattern::Principal(ComponentPattern::variable("p"))),
///     TestExpr::atom(Comparison::Eq, AtomPattern::Action(ComponentPattern::constant(Action::Read))),
/// ]);
/// let ever_read = RegexExpr::concat([RegexExpr::all(), RegexExpr::test(read_by_p), RegexExpr::all()]);
///
/// let domains = Domains::infinite().with_actions([Action::Read, Action::Edit]);
/// let mut analyzer = PolicyAnalyzer::new(domains);
/// let narrow = analyzer.add_rule(&Rule::new(RuleMode::Forbid, head.clone(), ever_read))?;
/// let broad = analyzer.add_rule(&Rule::new(RuleMode::Forbid, head, RegexExpr::all()))?;
/// assert!(analyzer.redundant(narrow, &[narrow, broad]).holds());
/// assert!(!analyzer.redundant(broad, &[narrow, broad]).holds());
/// # Ok::<(), junco_core::CompileError>(())
/// ```
pub struct PolicyAnalyzer<E: Event> {
    constants: Constants<E>,
    universes: Universes,
    expressions: Expressions,
    rules: Vec<AnalyzedRule>,
    options: SearchOptions,
}

impl<E: Event> PolicyAnalyzer<E> {
    /// Creates an analyzer for events whose components take the values of `domains`.
    pub fn new(domains: Domains<E>) -> Self {
        Self::with_options(domains, SearchOptions::default())
    }

    /// Creates an analyzer with explicit search options.
    pub fn with_options(domains: Domains<E>, options: SearchOptions) -> Self {
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
            expressions: Expressions::default(),
            rules: Vec::new(),
            options,
        }
    }

    /// Search options used by subsequent queries.
    pub fn options(&self) -> SearchOptions {
        self.options
    }

    /// Replaces the search options used by subsequent queries.
    pub fn set_options(&mut self, options: SearchOptions) {
        self.options = options;
    }

    /// Validates `rule` and adds it to the analysis.
    pub fn add_rule(&mut self, rule: &Rule<E>) -> Result<RuleId, CompileError> {
        let flat = flatten_rule(rule, &mut Unmetered, &mut ObservationWorld)?;
        let constants = self.head_constants(&flat.source.head);
        let tail = self.lower(&flat.source);
        let denial = match flat.mode {
            RuleMode::Forbid => tail,
            RuleMode::Require => self.expressions.not(tail),
        };
        self.rules.push(AnalyzedRule {
            constants,
            constraint: Constraint::head(constants, &self.universes),
            denial,
        });
        Ok(RuleId(self.rules.len() - 1))
    }

    /// Whether every candidate and history that `rule` denies is denied by some rule of `by`.
    ///
    /// A counterexample is a candidate and history that `rule` denies and no rule of `by` denies.
    ///
    /// # Panics
    /// Panics if a [`RuleId`] was not returned by this analyzer.
    pub fn covered(&mut self, rule: RuleId, by: &[RuleId]) -> Verdict<E> {
        let mut stats = SearchStats::default();
        let inclusion = self.covered_with(rule, by, &mut stats);
        Verdict { inclusion, stats }
    }

    /// Whether `rule` is redundant in `policy`: covered by the policy's other rules.
    ///
    /// A counterexample is a candidate and history that only `rule` denies.
    pub fn redundant(&mut self, rule: RuleId, policy: &[RuleId]) -> Verdict<E> {
        let others = policy
            .iter()
            .copied()
            .filter(|other| *other != rule)
            .collect::<Vec<_>>();
        self.covered(rule, &others)
    }

    /// Whether `stricter` denies everything that `than` denies.
    ///
    /// A counterexample is a candidate and history that `than` denies and `stricter` grants.
    pub fn at_least_as_strict(&mut self, stricter: &[RuleId], than: &[RuleId]) -> Verdict<E> {
        let mut stats = SearchStats::default();
        for rule in than {
            let inclusion = self.covered_with(*rule, stricter, &mut stats);
            if !matches!(inclusion, Inclusion::Holds) {
                return Verdict { inclusion, stats };
            }
        }
        Verdict {
            inclusion: Inclusion::Holds,
            stats,
        }
    }

    /// Whether `rule` never denies.
    ///
    /// A counterexample is a candidate and history that `rule` denies.
    pub fn never_fires(&mut self, rule: RuleId) -> Verdict<E> {
        self.rule_query(rule, |denial| (denial, ExprId::EMPTY))
    }

    /// Whether `rule` denies every candidate its head matches, whatever the history.
    ///
    /// A counterexample is a matching candidate and a history that `rule` grants.
    pub fn always_fires(&mut self, rule: RuleId) -> Verdict<E> {
        self.rule_query(rule, |denial| (ExprId::ALL, denial))
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
    ) -> Result<Verdict<E>, CompileError> {
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
        let (left, right) = (self.lower(&left.source), self.lower(&right.source));
        let mut stats = SearchStats::default();
        let inclusion = match Constraint::head(constants, &self.universes) {
            Some(constraint) => self.decide(constraint, left, right, &mut stats),
            None => Inclusion::Holds,
        };
        Ok(Verdict { inclusion, stats })
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

    /// The normal form of a lowered tail, built bottom-up by the smart constructors.
    fn lower(&mut self, source: &FlatPair<ComponentValue<E>>) -> ExprId {
        let mut tests = Vec::<TestId>::with_capacity(source.tests.len());
        for test in &source.tests {
            let test = match test {
                FlatTest::Bool(value) => self.expressions.test_bool(*value),
                FlatTest::Atom {
                    field,
                    term,
                    positive,
                } => {
                    let operand = match term {
                        FlatTerm::Constant(value) => {
                            Operand::Constant(self.constants.intern(*value))
                        }
                        // Lowering resolves a variable only in its own component.
                        FlatTerm::Variable(_) => Operand::Register,
                    };
                    let atom = Atom {
                        component: field.index(),
                        operand,
                    };
                    self.expressions.test_atom(atom, *positive)
                }
                FlatTest::And(children) => {
                    let children = children
                        .iter()
                        .map(|child| tests[*child as usize])
                        .collect::<SmallVec<[TestId; 4]>>();
                    self.expressions.test_and(&children)
                }
                FlatTest::Or(children) => {
                    let children = children
                        .iter()
                        .map(|child| tests[*child as usize])
                        .collect::<SmallVec<[TestId; 4]>>();
                    self.expressions.test_or(&children)
                }
            };
            tests.push(test);
        }
        let mut regexes = Vec::<ExprId>::with_capacity(source.regexes.len());
        for regex in &source.regexes {
            let expressions = &mut self.expressions;
            let regex = match regex {
                FlatRegex::Empty => ExprId::EMPTY,
                FlatRegex::All => ExprId::ALL,
                FlatRegex::Epsilon => ExprId::EPSILON,
                FlatRegex::Test(test) => expressions.test(tests[*test as usize]),
                FlatRegex::Union(children) => {
                    expressions.union(children.iter().map(|child| regexes[*child as usize]))
                }
                FlatRegex::Intersect(children) => {
                    expressions.intersect(children.iter().map(|child| regexes[*child as usize]))
                }
                // Concatenation is binary in normal form; associate it to the right.
                FlatRegex::Concat(children) => {
                    children.iter().rev().fold(ExprId::EPSILON, |tail, child| {
                        expressions.concat(regexes[*child as usize], tail)
                    })
                }
                FlatRegex::Star(child) => expressions.star(regexes[*child as usize]),
                FlatRegex::Complement(child) => expressions.not(regexes[*child as usize]),
            };
            regexes.push(regex);
        }
        regexes[source.root as usize]
    }

    fn rule_query(
        &mut self,
        rule: RuleId,
        sides: impl FnOnce(ExprId) -> (ExprId, ExprId),
    ) -> Verdict<E> {
        let analyzed = &self.rules[rule.0];
        let (constraint, (left, right)) = (analyzed.constraint.clone(), sides(analyzed.denial));
        let mut stats = SearchStats::default();
        let inclusion = match constraint {
            Some(constraint) => self.decide(constraint, left, right, &mut stats),
            // No candidate matches the head, so the rule denies nothing.
            None => Inclusion::Holds,
        };
        Verdict { inclusion, stats }
    }

    /// Splits on the head constants of `by` and decides one inclusion per case: under each case,
    /// every head of `by` either matches every candidate or none.
    fn covered_with(
        &mut self,
        rule: RuleId,
        by: &[RuleId],
        stats: &mut SearchStats,
    ) -> Inclusion<E> {
        let analyzed = &self.rules[rule.0];
        let Some(constraint) = analyzed.constraint.clone() else {
            return Inclusion::Holds;
        };
        let denial = analyzed.denial;
        let operands = Operands::pairs(by.iter().flat_map(|other| {
            self.rules[other.0]
                .constants
                .iter()
                .enumerate()
                .filter_map(|(component, value)| value.map(|value| (component, value)))
        }));
        for case in split(&constraint, &operands, &self.universes) {
            let matching = by
                .iter()
                .filter(|other| {
                    self.rules[other.0]
                        .constraint
                        .as_ref()
                        .is_some_and(|theirs| case.entails(theirs))
                })
                .map(|other| self.rules[other.0].denial)
                .collect::<Vec<_>>();
            let covering = self.expressions.union(matching);
            let inclusion = self.decide(case, denial, covering, stats);
            if !matches!(inclusion, Inclusion::Holds) {
                return inclusion;
            }
        }
        Inclusion::Holds
    }

    fn decide(
        &mut self,
        constraint: Constraint,
        left: ExprId,
        right: ExprId,
        stats: &mut SearchStats,
    ) -> Inclusion<E> {
        let excluded = self.expressions.not(right);
        let difference = self.expressions.intersect([left, excluded]);
        match search(
            &mut self.expressions,
            &self.universes,
            constraint,
            difference,
            self.options,
            stats,
        ) {
            SearchOutcome::Holds => Inclusion::Holds,
            SearchOutcome::Exhausted => Inclusion::Exhausted,
            SearchOutcome::Refuted(refutation) => Inclusion::Counterexample(
                self.counterexample(&refutation.constraint, &refutation.letters),
            ),
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
            Slot::Constant(id) => Value::Constant(project(self.constants.values[id as usize])),
            Slot::Fresh(number) => Value::Fresh(number),
        }
    }
}
