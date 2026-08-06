use std::collections::HashMap;
use std::hash::Hash;

use bumpalo::Bump;
use hashconsing::{BHConsed, BHConsign};
use string_interner::{DefaultStringInterner, DefaultSymbol};

use crate::model::{Action, Event, Principal, Resource};
use crate::validator::CompileError;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ComponentPattern<T> {
    Constant(T),
    Variable(String),
}

impl<T> ComponentPattern<T> {
    pub fn constant(value: impl Into<T>) -> Self {
        Self::Constant(value.into())
    }

    pub fn variable(name: impl Into<String>) -> Self {
        Self::Variable(name.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Head {
    pub principal: ComponentPattern<Principal>,
    pub action: ComponentPattern<Action>,
    pub resource: ComponentPattern<Resource>,
}

impl Head {
    pub fn new(
        principal: ComponentPattern<Principal>,
        action: ComponentPattern<Action>,
        resource: ComponentPattern<Resource>,
    ) -> Self {
        Self {
            principal,
            action,
            resource,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Component {
    Principal,
    Action,
    Resource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Comparison {
    Eq,
    Neq,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomPattern {
    Variable { component: Component, name: String },
    Principal(Principal),
    Action(Action),
    Resource(Resource),
}

impl AtomPattern {
    pub fn variable(component: Component, name: impl Into<String>) -> Self {
        Self::Variable {
            component,
            name: name.into(),
        }
    }

    pub fn principal(value: impl Into<Principal>) -> Self {
        Self::Principal(value.into())
    }

    pub fn action(value: Action) -> Self {
        Self::Action(value)
    }

    pub fn resource(value: impl Into<Resource>) -> Self {
        Self::Resource(value.into())
    }

    pub fn component(&self) -> Component {
        match self {
            Self::Variable { component, .. } => *component,
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TestAtom {
    comparison: Comparison,
    pattern: AtomPattern,
}

impl TestAtom {
    pub fn comparison(&self) -> Comparison {
        self.comparison
    }

    pub fn component(&self) -> Component {
        self.pattern.component()
    }

    pub fn pattern(&self) -> &AtomPattern {
        &self.pattern
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Test {
    True,
    False,
    Atom(TestAtom),
    And(Vec<Test>),
    Or(Vec<Test>),
}

impl Test {
    pub fn atom(comparison: Comparison, pattern: AtomPattern) -> Self {
        Self::Atom(TestAtom {
            comparison,
            pattern,
        })
    }

    pub fn eq(pattern: AtomPattern) -> Self {
        Self::atom(Comparison::Eq, pattern)
    }

    pub fn neq(pattern: AtomPattern) -> Self {
        Self::atom(Comparison::Neq, pattern)
    }

    pub fn and(tests: impl IntoIterator<Item = Test>) -> Self {
        Self::And(tests.into_iter().collect())
    }

    pub fn or(tests: impl IntoIterator<Item = Test>) -> Self {
        Self::Or(tests.into_iter().collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Regex {
    Empty,
    All,
    Epsilon,
    Test(Test),
    Union(Vec<Regex>),
    Concat(Vec<Regex>),
    Star(Box<Regex>),
    Intersect(Vec<Regex>),
    Not(Box<Regex>),
}

impl Regex {
    pub fn test(test: Test) -> Self {
        Self::Test(test)
    }

    pub fn union(regexes: impl IntoIterator<Item = Regex>) -> Self {
        Self::Union(regexes.into_iter().collect())
    }

    pub fn concat(regexes: impl IntoIterator<Item = Regex>) -> Self {
        Self::Concat(regexes.into_iter().collect())
    }

    pub fn star(regex: Regex) -> Self {
        Self::Star(Box::new(regex))
    }

    pub fn intersect(regexes: impl IntoIterator<Item = Regex>) -> Self {
        Self::Intersect(regexes.into_iter().collect())
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(regex: Regex) -> Self {
        Self::Not(Box::new(regex))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    Require,
    Forbid,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule {
    pub mode: RuleMode,
    pub head: Head,
    pub tail: Regex,
}

impl Rule {
    pub fn new(mode: RuleMode, head: Head, tail: Regex) -> Self {
        Self { mode, head, tail }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CompiledAction<'a> {
    Read,
    Edit,
    Stage,
    Unstage,
    Commit(Option<&'a str>),
    Checkout,
    Stash,
    Diff,
    History,
}

impl<'a> CompiledAction<'a> {
    fn from_action(arena: &'a Bump, action: &Action) -> Self {
        match action {
            Action::Read => Self::Read,
            Action::Edit => Self::Edit,
            Action::Stage => Self::Stage,
            Action::Unstage => Self::Unstage,
            Action::Commit { message } => {
                Self::Commit(message.as_deref().map(|m| arena.alloc_str(m) as &str))
            }
            Action::Checkout => Self::Checkout,
            Action::Stash => Self::Stash,
            Action::Diff => Self::Diff,
            Action::History => Self::History,
        }
    }

    fn matches(self, action: &Action) -> bool {
        match (self, action) {
            (Self::Read, Action::Read)
            | (Self::Edit, Action::Edit)
            | (Self::Stage, Action::Stage)
            | (Self::Unstage, Action::Unstage)
            | (Self::Checkout, Action::Checkout)
            | (Self::Stash, Action::Stash)
            | (Self::Diff, Action::Diff)
            | (Self::History, Action::History) => true,
            (Self::Commit(expected), Action::Commit { message }) => expected == message.as_deref(),
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TermValue<'a> {
    Variable {
        component: Component,
        symbol: DefaultSymbol,
    },
    Principal(&'a str),
    Action(CompiledAction<'a>),
    Resource(&'a [&'a str]),
}

impl TermValue<'_> {
    fn component(self) -> Component {
        match self {
            Self::Variable { component, .. } => component,
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TestNode<'a> {
    True,
    False,
    Atom(Comparison, TermValue<'a>),
    And(&'a [TestId<'a>]),
    Or(&'a [TestId<'a>]),
}

pub(crate) type TestId<'a> = BHConsed<'a, TestNode<'a>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RegexNode<'a> {
    Empty,
    All,
    Epsilon,
    Test(TestId<'a>),
    Union(&'a [RegexId<'a>]),
    Concat(&'a [RegexId<'a>]),
    Star(RegexId<'a>),
    Intersect(&'a [RegexId<'a>]),
    Not(RegexId<'a>),
}

pub(crate) type RegexId<'a> = BHConsed<'a, RegexNode<'a>>;

#[derive(Clone, Copy, Debug)]
pub(crate) enum BoundValue<'event> {
    Principal(&'event Principal),
    Action(&'event Action),
    Resource(&'event Resource),
}

impl BoundValue<'_> {
    fn component(self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }

    fn equals(self, other: Self) -> bool {
        match (self, other) {
            (Self::Principal(left), Self::Principal(right)) => left == right,
            (Self::Action(left), Self::Action(right)) => left == right,
            (Self::Resource(left), Self::Resource(right)) => left == right,
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Bindings<'event> {
    values: HashMap<DefaultSymbol, BoundValue<'event>>,
}

impl<'event> Bindings<'event> {
    fn bind(&mut self, symbol: DefaultSymbol, value: BoundValue<'event>) -> bool {
        match self.values.get(&symbol).copied() {
            Some(existing) => existing.equals(value),
            None => {
                self.values.insert(symbol, value);
                true
            }
        }
    }

    fn get(&self, symbol: DefaultSymbol) -> BoundValue<'event> {
        self.values
            .get(&symbol)
            .copied()
            .expect("compiled head binds every tail variable")
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CompiledHead<'a> {
    principal: TermValue<'a>,
    action: TermValue<'a>,
    resource: TermValue<'a>,
}

impl<'a> CompiledHead<'a> {
    pub(crate) fn matches<'event>(&self, event: &'event Event) -> Option<Bindings<'event>> {
        let mut bindings = Bindings::default();
        if !match_head_term(
            self.principal,
            BoundValue::Principal(&event.principal),
            &mut bindings,
        ) || !match_head_term(
            self.action,
            BoundValue::Action(&event.action),
            &mut bindings,
        ) || !match_head_term(
            self.resource,
            BoundValue::Resource(&event.resource),
            &mut bindings,
        ) {
            return None;
        }
        Some(bindings)
    }
}

fn match_head_term<'event>(
    term: TermValue<'_>,
    value: BoundValue<'event>,
    bindings: &mut Bindings<'event>,
) -> bool {
    match term {
        TermValue::Variable { component, symbol } => {
            component == value.component() && bindings.bind(symbol, value)
        }
        TermValue::Principal(expected) => {
            matches!(value, BoundValue::Principal(actual) if actual.as_str() == expected)
        }
        TermValue::Action(expected) => {
            matches!(value, BoundValue::Action(actual) if expected.matches(actual))
        }
        TermValue::Resource(expected) => {
            matches!(value, BoundValue::Resource(actual) if resource_matches(expected, actual))
        }
    }
}

#[derive(Default)]
struct Scope {
    variables: HashMap<DefaultSymbol, Component>,
}

impl Scope {
    fn bind(
        &mut self,
        rule: usize,
        name: &str,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), CompileError> {
        if let Some(&bound_component) = self.variables.get(&symbol) {
            if bound_component != component {
                return Err(CompileError::VariableComponentConflict {
                    rule,
                    name: name.to_owned(),
                });
            }
            return Ok(());
        }
        self.variables.insert(symbol, component);
        Ok(())
    }

    fn resolve(
        &self,
        rule: usize,
        name: &str,
        symbol: DefaultSymbol,
        component: Component,
    ) -> Result<(), CompileError> {
        let Some(&bound_component) = self.variables.get(&symbol) else {
            return Err(CompileError::UnboundVariable {
                rule,
                name: name.to_owned(),
            });
        };
        if bound_component != component {
            return Err(CompileError::VariableComponentConflict {
                rule,
                name: name.to_owned(),
            });
        }
        Ok(())
    }
}

pub(crate) struct SyntaxContext<'a> {
    variables: DefaultStringInterner,
    test_consign: BHConsign<'a, TestNode<'a>>,
    regex_consign: BHConsign<'a, RegexNode<'a>>,
    regex_nullable: Vec<bool>,
    test_true: TestId<'a>,
    test_false: TestId<'a>,
    empty: RegexId<'a>,
    all: RegexId<'a>,
    epsilon: RegexId<'a>,
}

trait ArenaComponent<'a>: Sized {
    const COMPONENT: Component;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> TermValue<'a>;
}

impl<'a> ArenaComponent<'a> for Principal {
    const COMPONENT: Component = Component::Principal;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> TermValue<'a> {
        TermValue::Principal(context.alloc_principal(value))
    }
}

impl<'a> ArenaComponent<'a> for Action {
    const COMPONENT: Component = Component::Action;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> TermValue<'a> {
        TermValue::Action(CompiledAction::from_action(context.arena(), value))
    }
}

impl<'a> ArenaComponent<'a> for Resource {
    const COMPONENT: Component = Component::Resource;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> TermValue<'a> {
        TermValue::Resource(context.alloc_resource(value))
    }
}

impl<'a> SyntaxContext<'a> {
    pub(crate) fn new(arena: &'a Bump) -> Self {
        let mut test_consign = BHConsign::with_capacity(arena, 128);
        let test_true = test_consign.mk(TestNode::True);
        let test_false = test_consign.mk(TestNode::False);

        let mut regex_consign = BHConsign::with_capacity(arena, 1024);
        let empty = regex_consign.mk(RegexNode::Empty);
        let all = regex_consign.mk(RegexNode::All);
        let epsilon = regex_consign.mk(RegexNode::Epsilon);
        let mut regex_nullable = Vec::with_capacity(1024);
        regex_nullable.push(false);
        regex_nullable.push(true);
        regex_nullable.push(true);

        Self {
            variables: DefaultStringInterner::with_capacity(64),
            test_consign,
            regex_consign,
            regex_nullable,
            test_true,
            test_false,
            empty,
            all,
            epsilon,
        }
    }

    pub(crate) fn compile_rule_parts(
        &mut self,
        rule: usize,
        head: &Head,
        tail: &Regex,
    ) -> Result<(CompiledHead<'a>, RegexId<'a>), CompileError> {
        let mut scope = Scope::default();
        let principal = self.compile_head_pattern(rule, &head.principal, &mut scope)?;
        let action = self.compile_head_pattern(rule, &head.action, &mut scope)?;
        let resource = self.compile_head_pattern(rule, &head.resource, &mut scope)?;
        let tail = self.compile_regex(rule, tail, &scope)?;
        Ok((
            CompiledHead {
                principal,
                action,
                resource,
            },
            tail,
        ))
    }

    fn arena(&self) -> &'a Bump {
        self.test_consign.arena()
    }

    fn alloc_principal(&self, principal: &Principal) -> &'a str {
        self.arena().alloc_str(principal.as_str())
    }

    fn alloc_resource(&self, resource: &Resource) -> &'a [&'a str] {
        let segments: Vec<&'a str> = resource
            .segments()
            .iter()
            .map(|segment| self.arena().alloc_str(segment) as &str)
            .collect();
        self.arena().alloc_slice_copy(&segments)
    }

    fn compile_head_pattern<T: ArenaComponent<'a>>(
        &mut self,
        rule: usize,
        pattern: &ComponentPattern<T>,
        scope: &mut Scope,
    ) -> Result<TermValue<'a>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => T::intern(self, value),
            ComponentPattern::Variable(name) => {
                let symbol = self.variables.get_or_intern(name);
                scope.bind(rule, name, symbol, T::COMPONENT)?;
                TermValue::Variable {
                    component: T::COMPONENT,
                    symbol,
                }
            }
        })
    }

    fn compile_atom_pattern(
        &self,
        rule: usize,
        pattern: &AtomPattern,
        scope: &Scope,
    ) -> Result<TermValue<'a>, CompileError> {
        Ok(match pattern {
            AtomPattern::Variable { component, name } => {
                let Some(symbol) = self.variables.get(name) else {
                    return Err(CompileError::UnboundVariable {
                        rule,
                        name: name.to_owned(),
                    });
                };
                scope.resolve(rule, name, symbol, *component)?;
                TermValue::Variable {
                    component: *component,
                    symbol,
                }
            }
            AtomPattern::Principal(value) => Principal::intern(self, value),
            AtomPattern::Action(value) => Action::intern(self, value),
            AtomPattern::Resource(value) => Resource::intern(self, value),
        })
    }

    fn compile_test(
        &mut self,
        rule: usize,
        test: &Test,
        scope: &Scope,
    ) -> Result<TestId<'a>, CompileError> {
        Ok(match test {
            Test::True => self.test_true,
            Test::False => self.test_false,
            Test::Atom(atom) => {
                let term = self.compile_atom_pattern(rule, &atom.pattern, scope)?;
                self.test_consign.mk(TestNode::Atom(atom.comparison, term))
            }
            Test::And(children) => {
                let children = children
                    .iter()
                    .map(|child| self.compile_test(rule, child, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                self.test_and(children)
            }
            Test::Or(children) => {
                let children = children
                    .iter()
                    .map(|child| self.compile_test(rule, child, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                self.test_or(children)
            }
        })
    }

    fn test_and(&mut self, children: Vec<TestId<'a>>) -> TestId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TestNode::False => return self.test_false,
                TestNode::True => {}
                TestNode::And(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_tests(&flat) {
            return self.test_false;
        }
        match flat.as_slice() {
            [] => self.test_true,
            [only] => *only,
            _ => {
                let values = self.test_consign.arena().alloc_slice_copy(&flat);
                self.test_consign.mk(TestNode::And(values))
            }
        }
    }

    fn test_or(&mut self, children: Vec<TestId<'a>>) -> TestId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TestNode::True => return self.test_true,
                TestNode::False => {}
                TestNode::Or(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_tests(&flat) {
            return self.test_true;
        }
        match flat.as_slice() {
            [] => self.test_false,
            [only] => *only,
            _ => {
                let values = self.test_consign.arena().alloc_slice_copy(&flat);
                self.test_consign.mk(TestNode::Or(values))
            }
        }
    }

    fn compile_regex(
        &mut self,
        rule: usize,
        regex: &Regex,
        scope: &Scope,
    ) -> Result<RegexId<'a>, CompileError> {
        Ok(match regex {
            Regex::Empty => self.empty,
            Regex::All => self.all,
            Regex::Epsilon => self.epsilon,
            Regex::Test(test) => {
                let test = self.compile_test(rule, test, scope)?;
                self.regex_test(test)
            }
            Regex::Union(children) => {
                let children = children
                    .iter()
                    .map(|child| self.compile_regex(rule, child, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                self.regex_union(children)
            }
            Regex::Concat(children) => {
                let children = children
                    .iter()
                    .map(|child| self.compile_regex(rule, child, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                self.regex_concat(children)
            }
            Regex::Star(inner) => {
                let inner = self.compile_regex(rule, inner, scope)?;
                self.regex_star(inner)
            }
            Regex::Intersect(children) => {
                let children = children
                    .iter()
                    .map(|child| self.compile_regex(rule, child, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                self.regex_intersect(children)
            }
            Regex::Not(inner) => {
                let inner = self.compile_regex(rule, inner, scope)?;
                self.regex_not(inner)
            }
        })
    }

    fn intern_regex(&mut self, node: RegexNode<'a>, nullable: bool) -> RegexId<'a> {
        let (id, is_new) = self.regex_consign.mk_is_new(node);
        let index = id.uid() as usize;
        if is_new {
            assert_eq!(index, self.regex_nullable.len());
            self.regex_nullable.push(nullable);
        } else {
            assert_eq!(self.regex_nullable[index], nullable);
        }
        id
    }

    fn regex_test(&mut self, test: TestId<'a>) -> RegexId<'a> {
        if test == self.test_false {
            self.empty
        } else {
            self.intern_regex(RegexNode::Test(test), false)
        }
    }

    pub(crate) fn regex_union(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::All => return self.all,
                RegexNode::Empty => {}
                RegexNode::Union(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_regexes(&flat) {
            return self.all;
        }
        match flat.as_slice() {
            [] => self.empty,
            [only] => *only,
            _ => {
                let nullable = flat.iter().any(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Union(values), nullable)
            }
        }
    }

    pub(crate) fn regex_intersect(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::Empty => return self.empty,
                RegexNode::All => {}
                RegexNode::Intersect(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_regexes(&flat) {
            return self.empty;
        }
        match flat.as_slice() {
            [] => self.all,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Intersect(values), nullable)
            }
        }
    }

    pub(crate) fn regex_concat(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::Empty => return self.empty,
                RegexNode::Epsilon => {}
                RegexNode::Concat(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        match flat.as_slice() {
            [] => self.epsilon,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Concat(values), nullable)
            }
        }
    }

    pub(crate) fn regex_star(&mut self, inner: RegexId<'a>) -> RegexId<'a> {
        match *inner.get() {
            RegexNode::Empty | RegexNode::Epsilon => self.epsilon,
            RegexNode::All => self.all,
            RegexNode::Star(_) => inner,
            _ => self.intern_regex(RegexNode::Star(inner), true),
        }
    }

    pub(crate) fn regex_not(&mut self, inner: RegexId<'a>) -> RegexId<'a> {
        match *inner.get() {
            RegexNode::Empty => self.all,
            RegexNode::All => self.empty,
            RegexNode::Not(value) => value,
            _ => self.intern_regex(RegexNode::Not(inner), !self.nullable(inner)),
        }
    }

    pub(crate) fn nullable(&self, regex: RegexId<'a>) -> bool {
        self.regex_nullable[regex.uid() as usize]
    }

    pub(crate) fn accepts<'event>(
        &mut self,
        root: RegexId<'a>,
        history: impl IntoIterator<Item = &'event Event>,
        bindings: &Bindings<'event>,
    ) -> bool {
        let mut state = root;
        for event in history {
            state = self.derive(state, event, bindings);
        }
        self.nullable(state)
    }

    fn derive<'event>(
        &mut self,
        regex: RegexId<'a>,
        event: &'event Event,
        bindings: &Bindings<'event>,
    ) -> RegexId<'a> {
        match *regex.get() {
            RegexNode::Empty | RegexNode::Epsilon => self.empty,
            RegexNode::All => self.all,
            RegexNode::Test(test) => {
                if self.eval_test(test, event, bindings) {
                    self.epsilon
                } else {
                    self.empty
                }
            }
            RegexNode::Union(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_union(derivatives)
            }
            RegexNode::Intersect(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_intersect(derivatives)
            }
            RegexNode::Not(inner) => {
                let derivative = self.derive(inner, event, bindings);
                self.regex_not(derivative)
            }
            RegexNode::Concat(factors) => {
                let mut alternatives = Vec::new();
                for (index, factor) in factors.iter().enumerate() {
                    let derivative = self.derive(*factor, event, bindings);
                    let mut product = Vec::with_capacity(factors.len() - index);
                    product.push(derivative);
                    product.extend_from_slice(&factors[index + 1..]);
                    alternatives.push(self.regex_concat(product));
                    if !self.nullable(*factor) {
                        break;
                    }
                }
                self.regex_union(alternatives)
            }
            RegexNode::Star(inner) => {
                let derivative = self.derive(inner, event, bindings);
                self.regex_concat(vec![derivative, regex])
            }
        }
    }

    fn eval_test<'event>(
        &self,
        test: TestId<'a>,
        event: &'event Event,
        bindings: &Bindings<'event>,
    ) -> bool {
        match *test.get() {
            TestNode::True => true,
            TestNode::False => false,
            TestNode::Atom(comparison, term) => {
                let equal = eval_atom(term, event, bindings);
                match comparison {
                    Comparison::Eq => equal,
                    Comparison::Neq => !equal,
                }
            }
            TestNode::And(children) => children
                .iter()
                .all(|child| self.eval_test(*child, event, bindings)),
            TestNode::Or(children) => children
                .iter()
                .any(|child| self.eval_test(*child, event, bindings)),
        }
    }

    #[cfg(test)]
    pub(crate) fn regex_node_count(&self) -> usize {
        self.regex_consign.len()
    }
}

fn eval_atom<'event>(
    term: TermValue<'_>,
    event: &'event Event,
    bindings: &Bindings<'event>,
) -> bool {
    let component = term.component();
    let actual = match component {
        Component::Principal => BoundValue::Principal(&event.principal),
        Component::Action => BoundValue::Action(&event.action),
        Component::Resource => BoundValue::Resource(&event.resource),
    };
    match term {
        TermValue::Variable { symbol, .. } => bindings.get(symbol).equals(actual),
        TermValue::Principal(expected) => {
            matches!(actual, BoundValue::Principal(value) if value.as_str() == expected)
        }
        TermValue::Action(expected) => {
            matches!(actual, BoundValue::Action(value) if expected.matches(value))
        }
        TermValue::Resource(expected) => {
            matches!(actual, BoundValue::Resource(value) if resource_matches(expected, value))
        }
    }
}

fn resource_matches(expected: &[&str], actual: &Resource) -> bool {
    expected.len() == actual.segments().len()
        && expected
            .iter()
            .zip(actual.segments())
            .all(|(left, right)| *left == right)
}

fn has_complementary_tests(tests: &[TestId<'_>]) -> bool {
    tests.iter().enumerate().any(|(index, left)| {
        tests[index + 1..]
            .iter()
            .any(|right| complementary_test(*left, *right))
    })
}

fn complementary_test(left: TestId<'_>, right: TestId<'_>) -> bool {
    match (*left.get(), *right.get()) {
        (
            TestNode::Atom(left_comparison, left_term),
            TestNode::Atom(right_comparison, right_term),
        ) => left_comparison != right_comparison && left_term == right_term,
        _ => false,
    }
}

fn has_complementary_regexes(regexes: &[RegexId<'_>]) -> bool {
    regexes.iter().enumerate().any(|(index, left)| {
        regexes[index + 1..]
            .iter()
            .any(|right| complementary_regex(*left, *right))
    })
}

fn complementary_regex(left: RegexId<'_>, right: RegexId<'_>) -> bool {
    matches!(*left.get(), RegexNode::Not(inner) if inner == right)
        || matches!(*right.get(), RegexNode::Not(inner) if inner == left)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variable_head() -> Head {
        Head::new(
            ComponentPattern::variable("principal"),
            ComponentPattern::variable("action"),
            ComponentPattern::variable("resource"),
        )
    }

    #[test]
    fn aci_and_identity_normalization_reuse_handles() {
        let arena = Bump::new();
        let mut syntax = SyntaxContext::new(&arena);
        let read = Regex::test(Test::eq(AtomPattern::action(Action::Read)));
        let edit = Regex::test(Test::eq(AtomPattern::action(Action::Edit)));

        let (_, left) = syntax
            .compile_rule_parts(
                1,
                &variable_head(),
                &Regex::union([read.clone(), Regex::Empty, edit.clone(), read.clone()]),
            )
            .unwrap();
        let (_, right) = syntax
            .compile_rule_parts(
                2,
                &variable_head(),
                &Regex::union([edit.clone(), read.clone()]),
            )
            .unwrap();
        assert_eq!(left, right);

        let (_, concat) = syntax
            .compile_rule_parts(
                3,
                &variable_head(),
                &Regex::concat([Regex::Epsilon, read.clone(), Regex::Epsilon]),
            )
            .unwrap();
        let (_, single) = syntax
            .compile_rule_parts(4, &variable_head(), &read)
            .unwrap();
        assert_eq!(concat, single);

        let (_, contradiction) = syntax
            .compile_rule_parts(
                5,
                &variable_head(),
                &Regex::intersect([edit.clone(), Regex::not(edit)]),
            )
            .unwrap();
        assert_eq!(contradiction, syntax.empty);
    }

    #[test]
    fn variable_names_share_interned_symbols_across_rules() {
        let arena = Bump::new();
        let mut syntax = SyntaxContext::new(&arena);
        let (first, _) = syntax
            .compile_rule_parts(1, &variable_head(), &Regex::All)
            .unwrap();
        let (second, _) = syntax
            .compile_rule_parts(2, &variable_head(), &Regex::All)
            .unwrap();

        let TermValue::Variable {
            component: first_component,
            symbol: first_symbol,
        } = first.principal
        else {
            panic!("principal head pattern was not compiled as a variable")
        };
        let TermValue::Variable {
            component: second_component,
            symbol: second_symbol,
        } = second.principal
        else {
            panic!("principal head pattern was not compiled as a variable")
        };
        assert_eq!(first_component, Component::Principal);
        assert_eq!(second_component, Component::Principal);
        assert_eq!(first_symbol, second_symbol);
        assert_eq!(syntax.variables.resolve(first_symbol), Some("principal"));
        assert_eq!(syntax.variables.len(), 3);
    }

    #[test]
    fn derivative_cycle_returns_the_same_hashconsed_state() {
        let arena = Bump::new();
        let mut syntax = SyntaxContext::new(&arena);
        let cycle = Regex::star(Regex::union([
            Regex::test(Test::eq(AtomPattern::action(Action::Read))),
            Regex::test(Test::eq(AtomPattern::action(Action::Edit))),
        ]));
        let (head, initial) = syntax
            .compile_rule_parts(1, &variable_head(), &cycle)
            .unwrap();
        let event = Event::new("alice", Action::Read, ["a"]);
        let bindings = head.matches(&event).unwrap();
        let before = syntax.regex_node_count();
        let mut state = initial;
        for _ in 0..100 {
            state = syntax.derive(state, &event, &bindings);
            assert_eq!(state, initial);
        }
        assert_eq!(syntax.regex_node_count(), before);
    }
}
