//! Policy questions answered by inclusion: redundancy, strictness, and vacuity.

use std::collections::HashMap;

use bumpalo::Bump;

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::CompileError;

use super::super::compile::compile_head_and_tail;
use super::super::component::{ComponentResolver, ResolvedValue};
use super::super::environment::CompiledHead;
use super::super::node::RegexId;
use super::super::source::{
    AtomPattern, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use super::super::store::CanonicalStore;
use super::constraint::{
    COMPONENTS, Class, Constraint, Letter, Operands, RegisterConstraint, split,
};
use super::search::{InclusionEngine, SearchOutcome};
use super::{SearchOptions, SearchStats};

/// Handle of a rule added to a [`PolicyAnalyzer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleId(usize);

/// Outcome of an analysis query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Inclusion {
    /// The inclusion holds for every candidate.
    Holds,
    /// The inclusion fails; the counterexample witnesses it.
    Counterexample(Counterexample),
    /// The search exceeded [`SearchOptions::max_items`] before deciding.
    Exhausted,
}

/// A candidate and a history on which an inclusion fails.
///
/// What failing means depends on the query; each query documents it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    /// Candidate event the rule heads are matched against.
    pub candidate: Event,
    /// History before the candidate, oldest first.
    pub history: Vec<Event>,
}

/// Outcome of an analysis query together with the work it took.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verdict {
    /// Whether the inclusion holds.
    pub inclusion: Inclusion,
    /// Work done by the inclusion searches.
    pub stats: SearchStats,
}

impl Verdict {
    /// Whether the inclusion holds.
    pub fn holds(&self) -> bool {
        self.inclusion == Inclusion::Holds
    }
}

/// One analysed rule: the head constants and the language of histories it denies.
struct AnalyzedRule<'arena> {
    constants: [Option<ResolvedValue<'arena>>; COMPONENTS],
    denial: RegexId<'arena>,
}

impl<'arena> AnalyzedRule<'arena> {
    fn constraint(&self) -> Constraint<'arena> {
        Constraint::equations(self.constants)
    }
}

/// Static analysis of rule tables by inclusion between tails.
///
/// A rule denies a candidate and history when its head matches the candidate and the history is
/// inside its tail (`Forbid`) or outside it (`Require`). The analyzer decides, for every candidate,
/// whether the denials of one rule are covered by those of others, and whether a rule can fire.
///
/// # Example
///
/// ```rust
/// use junco_policy::{
///     Action, AtomPattern, Bump, Comparison, ComponentPattern, Head, PolicyAnalyzer, RegexExpr,
///     Rule, RuleMode, TestExpr,
/// };
///
/// let head = Head::new(
///     ComponentPattern::variable("p"),
///     ComponentPattern::constant(Action::Edit),
///     ComponentPattern::constant(["secret"]),
/// );
/// let read_by_p = TestExpr::and([
///     TestExpr::atom(Comparison::Eq, AtomPattern::Principal(ComponentPattern::variable("p"))),
///     TestExpr::atom(Comparison::Eq, AtomPattern::Action(ComponentPattern::constant(Action::Read))),
/// ]);
/// let ever_read = RegexExpr::concat([RegexExpr::all(), RegexExpr::test(read_by_p), RegexExpr::all()]);
///
/// let arena = Bump::new();
/// let mut analyzer = PolicyAnalyzer::new(&arena);
/// let narrow = analyzer.add_rule(&Rule::new(RuleMode::Forbid, head.clone(), ever_read))?;
/// let broad = analyzer.add_rule(&Rule::new(RuleMode::Forbid, head, RegexExpr::all()))?;
/// assert!(analyzer.redundant(narrow, &[narrow, broad]).holds());
/// assert!(!analyzer.redundant(broad, &[narrow, broad]).holds());
/// # Ok::<(), junco_policy::CompileError>(())
/// ```
pub struct PolicyAnalyzer<'arena> {
    store: CanonicalStore<'arena>,
    engine: InclusionEngine<'arena>,
    rules: Vec<AnalyzedRule<'arena>>,
    options: SearchOptions,
}

impl<'arena> PolicyAnalyzer<'arena> {
    /// Creates an analyzer whose canonical syntax lives in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self::with_options(arena, SearchOptions::default())
    }

    /// Creates an analyzer with explicit search options.
    pub fn with_options(arena: &'arena Bump, options: SearchOptions) -> Self {
        Self {
            store: CanonicalStore::new(arena),
            engine: InclusionEngine::default(),
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

    /// Validates and compiles `rule` for analysis.
    pub fn add_rule(&mut self, rule: &Rule) -> Result<RuleId, CompileError> {
        let (head, tail) = self.compile(rule)?;
        let denial = match rule.mode {
            RuleMode::Forbid => tail,
            RuleMode::Require => self.store.regex_not(tail),
        };
        self.rules.push(AnalyzedRule {
            constants: head_constants(&head),
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
    pub fn covered(&mut self, rule: RuleId, by: &[RuleId]) -> Verdict {
        let mut stats = SearchStats::default();
        let inclusion = self.covered_with(rule, by, &mut stats);
        Verdict { inclusion, stats }
    }

    /// Whether `rule` is redundant in `policy`: covered by the policy's other rules.
    ///
    /// A counterexample is a candidate and history that only `rule` denies.
    pub fn redundant(&mut self, rule: RuleId, policy: &[RuleId]) -> Verdict {
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
    pub fn at_least_as_strict(&mut self, stricter: &[RuleId], than: &[RuleId]) -> Verdict {
        let mut stats = SearchStats::default();
        for rule in than {
            let inclusion = self.covered_with(*rule, stricter, &mut stats);
            if inclusion != Inclusion::Holds {
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
    pub fn never_fires(&mut self, rule: RuleId) -> Verdict {
        let empty = self.store.empty;
        self.rule_query(rule, |denial| (denial, empty))
    }

    /// Whether `rule` denies every candidate its head matches, whatever the history.
    ///
    /// A counterexample is a matching candidate and a history that `rule` grants.
    pub fn always_fires(&mut self, rule: RuleId) -> Verdict {
        let all = self.store.all;
        self.rule_query(rule, |denial| (all, denial))
    }

    /// Whether, for every candidate that `head` matches, every history in `left` is in `right`.
    ///
    /// Both tails may refer to the head's variables. A counterexample is a matching candidate and a
    /// history in `left` but not in `right`.
    pub fn tail_included(
        &mut self,
        head: &Head,
        left: &RegexExpr,
        right: &RegexExpr,
    ) -> Result<Verdict, CompileError> {
        let (compiled, left) =
            self.compile(&Rule::new(RuleMode::Forbid, head.clone(), left.clone()))?;
        let (_, right) = self.compile(&Rule::new(RuleMode::Forbid, head.clone(), right.clone()))?;
        let constraint = Constraint::equations(head_constants(&compiled));
        let mut stats = SearchStats::default();
        let inclusion = self.decide(constraint, left, right, &mut stats);
        Ok(Verdict { inclusion, stats })
    }

    /// Validates `rule` with its own variable names, then compiles it with every variable renamed
    /// to its component's register, so that tails of different rules share canonical syntax.
    fn compile(
        &mut self,
        rule: &Rule,
    ) -> Result<(CompiledHead<'arena>, RegexId<'arena>), CompileError> {
        compile_head_and_tail(&mut self.store, rule)?;
        Ok(compile_head_and_tail(&mut self.store, &canonical(rule))
            .expect("renaming variables to registers preserves validity"))
    }

    fn rule_query(
        &mut self,
        rule: RuleId,
        sides: impl FnOnce(RegexId<'arena>) -> (RegexId<'arena>, RegexId<'arena>),
    ) -> Verdict {
        let analyzed = &self.rules[rule.0];
        let constraint = analyzed.constraint();
        let (left, right) = sides(analyzed.denial);
        let mut stats = SearchStats::default();
        let inclusion = self.decide(constraint, left, right, &mut stats);
        Verdict { inclusion, stats }
    }

    /// Splits on the head constants of `by` and decides one inclusion per case.
    fn covered_with(&mut self, rule: RuleId, by: &[RuleId], stats: &mut SearchStats) -> Inclusion {
        let analyzed = &self.rules[rule.0];
        let (constraint, denial) = (analyzed.constraint(), analyzed.denial);
        let operands = Operands::pairs(by.iter().flat_map(|other| {
            self.rules[other.0]
                .constants
                .iter()
                .enumerate()
                .filter_map(|(component, value)| value.map(|value| (component, value)))
        }));
        for case in split(&constraint, &operands) {
            let matching = by
                .iter()
                .filter(|other| case.entails(&self.rules[other.0].constraint()))
                .map(|other| self.rules[other.0].denial)
                .collect::<Vec<_>>();
            let covering = self.store.regex_union(matching);
            let inclusion = self.decide(case, denial, covering, stats);
            if inclusion != Inclusion::Holds {
                return inclusion;
            }
        }
        Inclusion::Holds
    }

    fn decide(
        &mut self,
        constraint: Constraint<'arena>,
        left: RegexId<'arena>,
        right: RegexId<'arena>,
        stats: &mut SearchStats,
    ) -> Inclusion {
        match self.engine.includes(
            &mut self.store,
            constraint,
            left,
            right,
            self.options,
            stats,
        ) {
            SearchOutcome::Holds => Inclusion::Holds,
            SearchOutcome::Exhausted => Inclusion::Exhausted,
            SearchOutcome::Refuted(refutation) => Inclusion::Counterexample(concretize(
                &self.store.resolver,
                &refutation.constraint,
                &refutation.letters,
            )),
        }
    }
}

/// Head constants per component; variables leave their register free.
fn head_constants<'arena>(
    head: &CompiledHead<'arena>,
) -> [Option<ResolvedValue<'arena>>; COMPONENTS] {
    [
        match head.principal {
            ComponentPattern::Constant(value) => Some(ResolvedValue::Principal(value)),
            ComponentPattern::Variable(_) => None,
        },
        match head.action {
            ComponentPattern::Constant(value) => Some(ResolvedValue::Action(value)),
            ComponentPattern::Variable(_) => None,
        },
        match head.resource {
            ComponentPattern::Constant(value) => Some(ResolvedValue::Resource(value)),
            ComponentPattern::Variable(_) => None,
        },
    ]
}

/// Variable names given to the registers; the names never escape the analyzer.
const REGISTERS: [&str; COMPONENTS] = ["κ.principal", "κ.action", "κ.resource"];

/// `rule` with each head variable, and its tail occurrences in the same component, renamed to the
/// component's register. Other occurrences keep their names; `rule` is valid, so there are none.
fn canonical(rule: &Rule) -> Rule {
    let mut bound = HashMap::new();
    let principal = bind(&rule.head.principal, 0, &mut bound);
    let action = bind(&rule.head.action, 1, &mut bound);
    let resource = bind(&rule.head.resource, 2, &mut bound);
    Rule::new(
        rule.mode,
        Head::new(principal, action, resource),
        rename_regex(&rule.tail, &bound),
    )
}

fn bind<T: Clone>(
    pattern: &ComponentPattern<T>,
    component: usize,
    bound: &mut HashMap<String, usize>,
) -> ComponentPattern<T> {
    if let ComponentPattern::Variable(name) = pattern {
        bound.insert(name.clone(), component);
    }
    rename_pattern(pattern, component, bound)
}

fn rename_pattern<T: Clone>(
    pattern: &ComponentPattern<T>,
    component: usize,
    bound: &HashMap<String, usize>,
) -> ComponentPattern<T> {
    match pattern {
        ComponentPattern::Variable(name) if bound.get(name) == Some(&component) => {
            ComponentPattern::Variable(REGISTERS[component].to_owned())
        }
        pattern => pattern.clone(),
    }
}

fn rename_regex(regex: &RegexExpr, bound: &HashMap<String, usize>) -> RegexExpr {
    let all = |children: &[RegexExpr]| {
        children
            .iter()
            .map(|child| rename_regex(child, bound))
            .collect()
    };
    match regex {
        RegexExpr::Empty => RegexExpr::Empty,
        RegexExpr::All => RegexExpr::All,
        RegexExpr::Epsilon => RegexExpr::Epsilon,
        RegexExpr::Test(test) => RegexExpr::Test(rename_test(test, bound)),
        RegexExpr::Union(children) => RegexExpr::Union(all(children)),
        RegexExpr::Concat(children) => RegexExpr::Concat(all(children)),
        RegexExpr::Star(inner) => RegexExpr::Star(Box::new(rename_regex(inner, bound))),
        RegexExpr::Intersect(children) => RegexExpr::Intersect(all(children)),
        RegexExpr::Not(inner) => RegexExpr::Not(Box::new(rename_regex(inner, bound))),
    }
}

fn rename_test(test: &TestExpr, bound: &HashMap<String, usize>) -> TestExpr {
    match test {
        TestExpr::True => TestExpr::True,
        TestExpr::False => TestExpr::False,
        TestExpr::Atom {
            comparison,
            pattern,
        } => TestExpr::Atom {
            comparison: *comparison,
            pattern: match pattern {
                AtomPattern::Principal(pattern) => {
                    AtomPattern::Principal(rename_pattern(pattern, 0, bound))
                }
                AtomPattern::Action(pattern) => {
                    AtomPattern::Action(rename_pattern(pattern, 1, bound))
                }
                AtomPattern::Resource(pattern) => {
                    AtomPattern::Resource(rename_pattern(pattern, 2, bound))
                }
            },
        },
        TestExpr::And(children) => TestExpr::And(
            children
                .iter()
                .map(|child| rename_test(child, bound))
                .collect(),
        ),
        TestExpr::Or(children) => TestExpr::Or(
            children
                .iter()
                .map(|child| rename_test(child, bound))
                .collect(),
        ),
    }
}

/// Builds a candidate and history from a refuting constraint and letter sequence.
///
/// Registers the constraint pins take their constant; the others, and every component a letter
/// leaves unmatched, take fresh values that equal no compiled constant and no other fresh value.
fn concretize<'arena>(
    resolver: &ComponentResolver<'arena>,
    constraint: &Constraint<'arena>,
    letters: &[Letter<'arena>],
) -> Counterexample {
    let mut fresh = Fresh { resolver, next: 0 };
    let principal = match &constraint.0[0] {
        RegisterConstraint::Equals(ResolvedValue::Principal(value)) => resolver.principal(*value),
        RegisterConstraint::Equals(_) => unreachable!("principal registers hold principals"),
        RegisterConstraint::Differs(_) => Principal::new(fresh.string()),
    };
    let action = match &constraint.0[1] {
        RegisterConstraint::Equals(ResolvedValue::Action(value)) => resolver.action(*value),
        RegisterConstraint::Equals(_) => unreachable!("action registers hold actions"),
        RegisterConstraint::Differs(_) => fresh.action(),
    };
    let resource = match &constraint.0[2] {
        RegisterConstraint::Equals(ResolvedValue::Resource(value)) => resolver.resource(*value),
        RegisterConstraint::Equals(_) => unreachable!("resource registers hold resources"),
        RegisterConstraint::Differs(_) => Resource::new([fresh.string()]),
    };
    let history = letters
        .iter()
        .map(|letter| Event {
            principal: match letter.class(0) {
                Some(Class::Constant(ResolvedValue::Principal(value))) => resolver.principal(value),
                Some(Class::Register) => principal.clone(),
                Some(Class::Constant(_)) => unreachable!("principal classes hold principals"),
                None => Principal::new(fresh.string()),
            },
            action: match letter.class(1) {
                Some(Class::Constant(ResolvedValue::Action(value))) => resolver.action(value),
                Some(Class::Register) => action.clone(),
                Some(Class::Constant(_)) => unreachable!("action classes hold actions"),
                None => fresh.action(),
            },
            resource: match letter.class(2) {
                Some(Class::Constant(ResolvedValue::Resource(value))) => resolver.resource(value),
                Some(Class::Register) => resource.clone(),
                Some(Class::Constant(_)) => unreachable!("resource classes hold resources"),
                None => Resource::new([fresh.string()]),
            },
        })
        .collect();
    Counterexample {
        candidate: Event::new(principal, action, resource),
        history,
    }
}

/// Source of strings that no compiled constant mentions.
struct Fresh<'resolver, 'arena> {
    resolver: &'resolver ComponentResolver<'arena>,
    next: usize,
}

impl Fresh<'_, '_> {
    fn string(&mut self) -> String {
        loop {
            let candidate = format!("fresh-{}", self.next);
            self.next += 1;
            if !self.resolver.is_interned(&candidate) {
                return candidate;
            }
        }
    }

    /// Every finite action set misses some commit message.
    fn action(&mut self) -> Action {
        Action::commit(self.string())
    }
}
