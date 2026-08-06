use std::collections::HashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_CONTEXT_ID: AtomicU64 = AtomicU64::new(1);

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
    Principal(ComponentPattern<Principal>),
    Action(ComponentPattern<Action>),
    Resource(ComponentPattern<Resource>),
}

impl AtomPattern {
    pub fn component(&self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    Require,
    Forbid,
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
pub(crate) enum ComponentValue<'a> {
    Variable {
        component: Component,
        symbol: DefaultSymbol,
    },
    Principal(&'a str),
    Action(CompiledAction<'a>),
    Resource(&'a [&'a str]),
}

impl ComponentValue<'_> {
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
    Atom {
        comparison: Comparison,
        pattern: ComponentValue<'a>,
    },
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Test<'a> {
    context: u64,
    scope: u64,
    id: TestId<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Regex<'a> {
    context: u64,
    scope: u64,
    id: RegexId<'a>,
}

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
    principal: ComponentValue<'a>,
    action: ComponentValue<'a>,
    resource: ComponentValue<'a>,
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
    term: ComponentValue<'_>,
    value: BoundValue<'event>,
    bindings: &mut Bindings<'event>,
) -> bool {
    match term {
        ComponentValue::Variable { component, symbol } => {
            component == value.component() && bindings.bind(symbol, value)
        }
        ComponentValue::Principal(expected) => {
            matches!(value, BoundValue::Principal(actual) if actual.as_str() == expected)
        }
        ComponentValue::Action(expected) => {
            matches!(value, BoundValue::Action(actual) if expected.matches(actual))
        }
        ComponentValue::Resource(expected) => {
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
    context_id: u64,
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

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> ComponentValue<'a>;
}

impl<'a> ArenaComponent<'a> for Principal {
    const COMPONENT: Component = Component::Principal;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> ComponentValue<'a> {
        ComponentValue::Principal(context.alloc_principal(value))
    }
}

impl<'a> ArenaComponent<'a> for Action {
    const COMPONENT: Component = Component::Action;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> ComponentValue<'a> {
        ComponentValue::Action(CompiledAction::from_action(context.arena(), value))
    }
}

impl<'a> ArenaComponent<'a> for Resource {
    const COMPONENT: Component = Component::Resource;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> ComponentValue<'a> {
        ComponentValue::Resource(context.alloc_resource(value))
    }
}

impl<'a> SyntaxContext<'a> {
    pub(crate) fn new(arena: &'a Bump) -> Self {
        let context_id = NEXT_CONTEXT_ID.fetch_add(1, Ordering::Relaxed);
        assert_ne!(context_id, 0, "syntax context identifier space exhausted");
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
            context_id,
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

    fn compile_head(
        &mut self,
        rule: usize,
        head: &Head,
    ) -> Result<(CompiledHead<'a>, Scope), CompileError> {
        let mut scope = Scope::default();
        let principal = self.compile_head_pattern(rule, &head.principal, &mut scope)?;
        let action = self.compile_head_pattern(rule, &head.action, &mut scope)?;
        let resource = self.compile_head_pattern(rule, &head.resource, &mut scope)?;
        Ok((
            CompiledHead {
                principal,
                action,
                resource,
            },
            scope,
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
    ) -> Result<ComponentValue<'a>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => T::intern(self, value),
            ComponentPattern::Variable(name) => {
                let symbol = self.variables.get_or_intern(name);
                scope.bind(rule, name, symbol, T::COMPONENT)?;
                ComponentValue::Variable {
                    component: T::COMPONENT,
                    symbol,
                }
            }
        })
    }

    fn compile_pattern<T: ArenaComponent<'a>>(
        &self,
        rule: usize,
        pattern: &ComponentPattern<T>,
        scope: &Scope,
    ) -> Result<ComponentValue<'a>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => T::intern(self, value),
            ComponentPattern::Variable(name) => {
                let Some(symbol) = self.variables.get(name) else {
                    return Err(CompileError::UnboundVariable {
                        rule,
                        name: name.to_owned(),
                    });
                };
                scope.resolve(rule, name, symbol, T::COMPONENT)?;
                ComponentValue::Variable {
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
    ) -> Result<ComponentValue<'a>, CompileError> {
        Ok(match pattern {
            AtomPattern::Principal(pattern) => self.compile_pattern(rule, pattern, scope)?,
            AtomPattern::Action(pattern) => self.compile_pattern(rule, pattern, scope)?,
            AtomPattern::Resource(pattern) => self.compile_pattern(rule, pattern, scope)?,
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
            TestNode::Atom {
                comparison,
                pattern,
            } => {
                let equal = eval_atom(pattern, event, bindings);
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

pub struct RuleSyntax<'context, 'arena> {
    syntax: &'context mut SyntaxContext<'arena>,
    rule: usize,
    scope_id: u64,
    scope: Scope,
}

impl<'context, 'arena> RuleSyntax<'context, 'arena> {
    pub(crate) fn new(
        syntax: &'context mut SyntaxContext<'arena>,
        rule: usize,
        scope_id: u64,
        head: &Head,
    ) -> Result<(CompiledHead<'arena>, Self), CompileError> {
        let (head, scope) = syntax.compile_head(rule, head)?;
        Ok((
            head,
            Self {
                syntax,
                rule,
                scope_id,
                scope,
            },
        ))
    }

    fn wrap_test(&self, id: TestId<'arena>) -> Test<'arena> {
        Test {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    fn test_id(&self, test: Test<'arena>) -> TestId<'arena> {
        assert_eq!(
            test.context, self.syntax.context_id,
            "test belongs to another syntax context"
        );
        assert_eq!(
            test.scope, self.scope_id,
            "test belongs to another rule scope"
        );
        test.id
    }

    fn wrap_regex(&self, id: RegexId<'arena>) -> Regex<'arena> {
        Regex {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    pub(crate) fn regex_id(&self, regex: Regex<'arena>) -> RegexId<'arena> {
        assert_eq!(
            regex.context, self.syntax.context_id,
            "regex belongs to another syntax context"
        );
        assert_eq!(
            regex.scope, self.scope_id,
            "regex belongs to another rule scope"
        );
        regex.id
    }

    pub(crate) fn finish_regex(
        &self,
        regex: Regex<'arena>,
    ) -> Result<RegexId<'arena>, CompileError> {
        if regex.context != self.syntax.context_id || regex.scope != self.scope_id {
            return Err(CompileError::ForeignRuleHandle { rule: self.rule });
        }
        Ok(regex.id)
    }

    pub fn true_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_true)
    }

    pub fn false_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_false)
    }

    pub fn atom(
        &mut self,
        comparison: Comparison,
        pattern: AtomPattern,
    ) -> Result<Test<'arena>, CompileError> {
        let term = self
            .syntax
            .compile_atom_pattern(self.rule, &pattern, &self.scope)?;
        let id = self.syntax.test_consign.mk(TestNode::Atom {
            comparison,
            pattern: term,
        });
        Ok(self.wrap_test(id))
    }

    pub fn and(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_and(ids);
        self.wrap_test(id)
    }

    pub fn or(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_or(ids);
        self.wrap_test(id)
    }

    pub fn empty(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.empty)
    }

    pub fn all(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.all)
    }

    pub fn epsilon(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.epsilon)
    }

    pub fn test(&mut self, test: Test<'arena>) -> Regex<'arena> {
        let test = self.test_id(test);
        let id = self.syntax.regex_test(test);
        self.wrap_regex(id)
    }

    pub fn union(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_union(ids);
        self.wrap_regex(id)
    }

    pub fn concat(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_concat(ids);
        self.wrap_regex(id)
    }

    pub fn star(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_star(regex);
        self.wrap_regex(id)
    }

    pub fn intersect(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_intersect(ids);
        self.wrap_regex(id)
    }

    pub fn not(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_not(regex);
        self.wrap_regex(id)
    }

    pub fn nullable(&self, regex: Regex<'arena>) -> bool {
        self.syntax.nullable(self.regex_id(regex))
    }
}

fn eval_atom<'event>(
    term: ComponentValue<'_>,
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
        ComponentValue::Variable { symbol, .. } => bindings.get(symbol).equals(actual),
        ComponentValue::Principal(expected) => {
            matches!(actual, BoundValue::Principal(value) if value.as_str() == expected)
        }
        ComponentValue::Action(expected) => {
            matches!(actual, BoundValue::Action(value) if expected.matches(value))
        }
        ComponentValue::Resource(expected) => {
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
            TestNode::Atom {
                comparison: left_comparison,
                pattern: left_pattern,
            },
            TestNode::Atom {
                comparison: right_comparison,
                pattern: right_pattern,
            },
        ) => left_comparison != right_comparison && left_pattern == right_pattern,
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

    fn action_regex<'a>(syntax: &mut RuleSyntax<'_, 'a>, action: Action) -> Regex<'a> {
        let test = syntax
            .atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(action)),
            )
            .unwrap();
        syntax.test(test)
    }

    #[test]
    fn aci_and_identity_normalization_reuse_handles() {
        let arena = Bump::new();
        let mut syntax = SyntaxContext::new(&arena);

        let (_, mut first) = RuleSyntax::new(&mut syntax, 1, 1, &variable_head()).unwrap();
        let read = action_regex(&mut first, Action::Read);
        let edit = action_regex(&mut first, Action::Edit);
        let empty = first.empty();
        let left = first.union([read, empty, edit, read]);
        let left = first.regex_id(left);
        drop(first);

        let (_, mut second) = RuleSyntax::new(&mut syntax, 2, 2, &variable_head()).unwrap();
        let edit = action_regex(&mut second, Action::Edit);
        let read = action_regex(&mut second, Action::Read);
        let right = second.union([edit, read]);
        let right = second.regex_id(right);
        assert_eq!(left, right);
        drop(second);

        let (_, mut third) = RuleSyntax::new(&mut syntax, 3, 3, &variable_head()).unwrap();
        let epsilon = third.epsilon();
        let read = action_regex(&mut third, Action::Read);
        let concat = third.concat([epsilon, read, epsilon]);
        let concat = third.regex_id(concat);
        drop(third);

        let (_, mut fourth) = RuleSyntax::new(&mut syntax, 4, 4, &variable_head()).unwrap();
        let single = action_regex(&mut fourth, Action::Read);
        let single = fourth.regex_id(single);
        assert_eq!(concat, single);
        drop(fourth);

        let (_, mut fifth) = RuleSyntax::new(&mut syntax, 5, 5, &variable_head()).unwrap();
        let edit = action_regex(&mut fifth, Action::Edit);
        let not_edit = fifth.not(edit);
        let contradiction = fifth.intersect([edit, not_edit]);
        let contradiction = fifth.regex_id(contradiction);
        assert_eq!(contradiction, syntax.empty);
    }

    #[test]
    fn variable_names_share_interned_symbols_across_rules() {
        let arena = Bump::new();
        let mut syntax = SyntaxContext::new(&arena);
        let (first, first_syntax) = RuleSyntax::new(&mut syntax, 1, 1, &variable_head()).unwrap();
        drop(first_syntax);
        let (second, second_syntax) = RuleSyntax::new(&mut syntax, 2, 2, &variable_head()).unwrap();
        drop(second_syntax);

        let ComponentValue::Variable {
            component: first_component,
            symbol: first_symbol,
        } = first.principal
        else {
            panic!("principal head pattern was not compiled as a variable")
        };
        let ComponentValue::Variable {
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
        let (head, mut rule) = RuleSyntax::new(&mut syntax, 1, 1, &variable_head()).unwrap();
        let read = action_regex(&mut rule, Action::Read);
        let edit = action_regex(&mut rule, Action::Edit);
        let alternatives = rule.union([read, edit]);
        let initial = rule.star(alternatives);
        let initial = rule.regex_id(initial);
        drop(rule);

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
