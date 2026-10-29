//! Structural views and independent, concrete-component semantics for the owned DSL.
//!
//! Component equality is `PartialEqSpec::eq_spec`, not representation equality. Connecting
//! native projections/equality to this model remains conditional on their respective contracts.

use crate::event::{Event, specs::EventSpec};
use crate::syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use alloc::boxed::Box;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

pub enum PatternView<T> {
    Constant(T),
    Variable(Seq<char>),
}

pub struct HeadView<P, A, R> {
    pub principal: PatternView<P>,
    pub action: PatternView<A>,
    pub resource: PatternView<R>,
}

pub enum AtomView<P, A, R> {
    Principal(PatternView<P>),
    Action(PatternView<A>),
    Resource(PatternView<R>),
}

pub enum TestView<P, A, R> {
    True,
    False,
    Atom { comparison: Comparison, pattern: AtomView<P, A, R> },
    And(Seq<TestView<P, A, R>>),
    Or(Seq<TestView<P, A, R>>),
}

/// The same algebra as the numeric history model, over concrete component values.
pub enum RegexView<P, A, R> {
    Empty, All, Epsilon,
    Test(TestView<P, A, R>),
    Union(Seq<RegexView<P, A, R>>),
    Concat(Seq<RegexView<P, A, R>>),
    Star(Box<RegexView<P, A, R>>),
    Intersect(Seq<RegexView<P, A, R>>),
    Not(Box<RegexView<P, A, R>>),
}

pub struct RuleView<P, A, R> {
    pub mode: RuleMode,
    pub head: HeadView<P, A, R>,
    pub tail: RegexView<P, A, R>,
}

/// Values are deliberately not IDs or views of values.
pub struct EventView<P, A, R> {
    pub principal: P,
    pub action: A,
    pub resource: R,
}

/// Remaining source nodes, used to prove that iterative disposal terminates.
pub open spec fn test_nodes<E: Event>(test: TestExpr<E>) -> nat
    decreases test,
{
    1 + match test {
        TestExpr::And(children) | TestExpr::Or(children) => test_forest_nodes(children@),
        _ => 0,
    }
}

pub open spec fn test_forest_nodes<E: Event>(tests: Seq<TestExpr<E>>) -> nat
    decreases tests,
{
    if tests.len() == 0 { 0 }
    else { test_forest_nodes(tests.drop_last()) + test_nodes(tests.last()) }
}

pub open spec fn regex_nodes<E: Event>(regex: RegexExpr<E>) -> nat
    decreases regex,
{
    1 + match regex {
        RegexExpr::Union(children) | RegexExpr::Concat(children) | RegexExpr::Intersect(children) =>
            regex_forest_nodes(children@),
        RegexExpr::Star(child) | RegexExpr::Not(child) => regex_nodes(*child),
        _ => 0,
    }
}

pub open spec fn regex_forest_nodes<E: Event>(regexes: Seq<RegexExpr<E>>) -> nat
    decreases regexes,
{
    if regexes.len() == 0 { 0 }
    else { regex_forest_nodes(regexes.drop_last()) + regex_nodes(regexes.last()) }
}

pub proof fn lemma_test_forest_append<E: Event>(left: Seq<TestExpr<E>>, right: Seq<TestExpr<E>>)
    ensures test_forest_nodes(left + right) == test_forest_nodes(left) + test_forest_nodes(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_test_forest_append(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert((left + right).last() == right.last());
    } else {
        assert(left + right =~= left);
    }
}

pub proof fn lemma_regex_forest_append<E: Event>(left: Seq<RegexExpr<E>>, right: Seq<RegexExpr<E>>)
    ensures regex_forest_nodes(left + right) == regex_forest_nodes(left) + regex_forest_nodes(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_regex_forest_append(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert((left + right).last() == right.last());
    } else {
        assert(left + right =~= left);
    }
}

impl<T> View for ComponentPattern<T> {
    type V = PatternView<T>;
    open spec fn view(&self) -> Self::V {
        match self {
            ComponentPattern::Constant(value) => PatternView::Constant(*value),
            ComponentPattern::Variable(name) => PatternView::Variable(name@),
        }
    }
}

impl<E: Event> View for Head<E> {
    type V = HeadView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        HeadView { principal: self.principal@, action: self.action@, resource: self.resource@ }
    }
}

impl<E: Event> View for AtomPattern<E> {
    type V = AtomView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        match self {
            AtomPattern::Principal(pattern) => AtomView::Principal(pattern@),
            AtomPattern::Action(pattern) => AtomView::Action(pattern@),
            AtomPattern::Resource(pattern) => AtomView::Resource(pattern@),
        }
    }
}

pub open spec fn test_view<E: Event>(test: TestExpr<E>) -> TestView<E::Principal, E::Action, E::Resource>
    decreases test,
{
    match test {
        TestExpr::True => TestView::True,
        TestExpr::False => TestView::False,
        TestExpr::Atom { comparison, pattern } => TestView::Atom { comparison, pattern: pattern@ },
        TestExpr::And(children) => TestView::And(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { test_view(children@[i]) } else { TestView::False })),
        TestExpr::Or(children) => TestView::Or(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { test_view(children@[i]) } else { TestView::False })),
    }
}

impl<E: Event> View for TestExpr<E> {
    type V = TestView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V { test_view(*self) }
}

pub open spec fn regex_view<E: Event>(regex: RegexExpr<E>) -> RegexView<E::Principal, E::Action, E::Resource>
    decreases regex,
{
    match regex {
        RegexExpr::Empty => RegexView::Empty,
        RegexExpr::All => RegexView::All,
        RegexExpr::Epsilon => RegexView::Epsilon,
        RegexExpr::Test(test) => RegexView::Test(test_view(test)),
        RegexExpr::Union(children) => RegexView::Union(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Concat(children) => RegexView::Concat(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Star(child) => RegexView::Star(Box::new(regex_view(*child))),
        RegexExpr::Intersect(children) => RegexView::Intersect(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Not(child) => RegexView::Not(Box::new(regex_view(*child))),
    }
}

impl<E: Event> View for RegexExpr<E> {
    type V = RegexView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V { regex_view(*self) }
}

impl<E: Event> View for Rule<E> {
    type V = RuleView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        RuleView { mode: self.mode, head: self.head@, tail: self.tail@ }
    }
}

pub open spec fn event_view<E: Event>(event: E) -> EventView<E::Principal, E::Action, E::Resource> {
    EventView { principal: event.principal_spec(), action: event.action_spec(), resource: event.resource_spec() }
}

pub open spec fn pattern_name<T>(pattern: PatternView<T>) -> Option<Seq<char>> {
    match pattern { PatternView::Constant(_) => None, PatternView::Variable(name) => Some(name) }
}

pub open spec fn distinct_names<T, U>(left: PatternView<T>, right: PatternView<U>) -> bool {
    match (pattern_name(left), pattern_name(right)) {
        (Some(a), Some(b)) => a != b,
        _ => true,
    }
}

pub open spec fn head_scoped<P, A, R>(head: HeadView<P, A, R>) -> bool {
    distinct_names(head.principal, head.action)
        && distinct_names(head.principal, head.resource)
        && distinct_names(head.action, head.resource)
}

pub open spec fn head_pattern_matches<T: PartialEq>(pattern: PatternView<T>, actual: T) -> bool {
    match pattern {
        PatternView::Constant(expected) => actual.eq_spec(&expected),
        PatternView::Variable(_) => true,
    }
}

pub open spec fn head_matches<P: PartialEq, A: PartialEq, R: PartialEq>(
    head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
) -> bool {
    head_pattern_matches(head.principal, candidate.principal)
        && head_pattern_matches(head.action, candidate.action)
        && head_pattern_matches(head.resource, candidate.resource)
}

/// Substitution is coordinate-local: an identically spelled name in another coordinate is absent.
pub open spec fn resolve_pattern<T>(
    pattern: PatternView<T>, head: PatternView<T>, candidate: T,
) -> Option<T> {
    match pattern {
        PatternView::Constant(value) => Some(value),
        PatternView::Variable(name) => match head {
            PatternView::Variable(bound) => if name == bound { Some(candidate) } else { None },
            PatternView::Constant(_) => None,
        },
    }
}

pub open spec fn pattern_scoped<T>(pattern: PatternView<T>, head: PatternView<T>) -> bool {
    match pattern {
        PatternView::Constant(_) => true,
        PatternView::Variable(name) => pattern_name(head) == Some(name),
    }
}

pub open spec fn atom_scoped<P, A, R>(atom: AtomView<P, A, R>, head: HeadView<P, A, R>) -> bool {
    match atom {
        AtomView::Principal(pattern) => pattern_scoped(pattern, head.principal),
        AtomView::Action(pattern) => pattern_scoped(pattern, head.action),
        AtomView::Resource(pattern) => pattern_scoped(pattern, head.resource),
    }
}

pub open spec fn test_scoped<P, A, R>(test: TestView<P, A, R>, head: HeadView<P, A, R>) -> bool
    decreases test,
{
    match test {
        TestView::True | TestView::False => true,
        TestView::Atom { pattern, .. } => atom_scoped(pattern, head),
        TestView::And(children) | TestView::Or(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(children[i], head),
    }
}

pub open spec fn regex_scoped<P, A, R>(regex: RegexView<P, A, R>, head: HeadView<P, A, R>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => true,
        RegexView::Test(test) => test_scoped(test, head),
        RegexView::Union(children) | RegexView::Concat(children) | RegexView::Intersect(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(children[i], head),
        RegexView::Star(child) | RegexView::Not(child) => regex_scoped(*child, head),
    }
}

pub open spec fn comparison_sem<T: PartialEq>(comparison: Comparison, actual: T, expected: Option<T>) -> bool {
    match expected {
        None => false,
        Some(value) => match comparison {
            Comparison::Eq => actual.eq_spec(&value),
            Comparison::Neq => !actual.eq_spec(&value),
        },
    }
}

pub open spec fn atom_sem<P: PartialEq, A: PartialEq, R: PartialEq>(
    comparison: Comparison, atom: AtomView<P, A, R>, head: HeadView<P, A, R>,
    candidate: EventView<P, A, R>, event: EventView<P, A, R>,
) -> bool {
    match atom {
        AtomView::Principal(pattern) => comparison_sem(comparison, event.principal,
            resolve_pattern(pattern, head.principal, candidate.principal)),
        AtomView::Action(pattern) => comparison_sem(comparison, event.action,
            resolve_pattern(pattern, head.action, candidate.action)),
        AtomView::Resource(pattern) => comparison_sem(comparison, event.resource,
            resolve_pattern(pattern, head.resource, candidate.resource)),
    }
}

pub open spec fn test_sem<P: PartialEq, A: PartialEq, R: PartialEq>(
    test: TestView<P, A, R>, head: HeadView<P, A, R>,
    candidate: EventView<P, A, R>, event: EventView<P, A, R>,
) -> bool
    decreases test,
{
    match test {
        TestView::True => true,
        TestView::False => false,
        TestView::Atom { comparison, pattern } => atom_sem(comparison, pattern, head, candidate, event),
        TestView::And(children) => forall|i: int| 0 <= i < children.len() ==>
            test_sem(children[i], head, candidate, event),
        TestView::Or(children) => exists|i: int| 0 <= i < children.len()
            && test_sem(children[i], head, candidate, event),
    }
}

/// Whole-word language semantics, in oldest-to-newest event order.
pub open spec fn lang<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
    word: Seq<EventView<P, A, R>>,
) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty => false,
        RegexView::All => true,
        RegexView::Epsilon => word.len() == 0,
        RegexView::Test(test) => word.len() == 1 && test_sem(test, head, candidate, word[0]),
        RegexView::Union(children) => exists|i: int| 0 <= i < children.len()
            && lang(children[i], head, candidate, word),
        RegexView::Intersect(children) => forall|i: int| 0 <= i < children.len() ==>
            lang(children[i], head, candidate, word),
        RegexView::Not(child) => !lang(*child, head, candidate, word),
        RegexView::Concat(children) => exists|parts: Seq<Seq<EventView<P, A, R>>>|
            parts.len() == children.len() && word == parts.flatten()
            && forall|i: int| 0 <= i < children.len() ==> lang(children[i], head, candidate, parts[i]),
        RegexView::Star(child) => exists|parts: Seq<Seq<EventView<P, A, R>>>|
            word == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(*child, head, candidate, parts[i]),
    }
}

pub open spec fn rule_accepts<E: Event>(rule: Rule<E>, candidate: E, history: Seq<E>) -> bool {
    head_matches(rule.head@, event_view(candidate))
        && lang(rule.tail@, rule.head@, event_view(candidate), history.map(|i: int, e: E| event_view(e)))
}

/// Empty operators retain their different Boolean and language identities.
pub proof fn lemma_empty_operators<P: PartialEq, A: PartialEq, R: PartialEq>(
    head: HeadView<P, A, R>, candidate: EventView<P, A, R>, word: Seq<EventView<P, A, R>>,
)
    ensures
        test_sem(TestView::And(Seq::empty()), head, candidate, candidate),
        !test_sem(TestView::Or(Seq::empty()), head, candidate, candidate),
        !lang(RegexView::Union(Seq::empty()), head, candidate, word),
        lang(RegexView::Intersect(Seq::empty()), head, candidate, word),
        lang(RegexView::Concat(Seq::empty()), head, candidate, word) <==> word.len() == 0,
{
    if lang(RegexView::Concat(Seq::empty()), head, candidate, word) {
        let parts = choose|parts: Seq<Seq<EventView<P, A, R>>>|
            parts.len() == 0 && word == parts.flatten()
            && forall|i: int| 0 <= i < 0 ==> lang(RegexView::Empty, head, candidate, parts[i]);
        assert(parts =~= Seq::empty());
    }
    if word.len() == 0 {
        let parts: Seq<Seq<EventView<P, A, R>>> = Seq::empty();
        assert(word =~= parts.flatten());
        assert(lang(RegexView::Concat(Seq::empty()), head, candidate, word));
    }
}

pub proof fn lemma_complement_is_whole_word<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
    word: Seq<EventView<P, A, R>>,
)
    ensures lang(RegexView::Not(Box::new(regex)), head, candidate, word)
        <==> !lang(regex, head, candidate, word),
{}

/// A real constructor/projection proof client, without a projection-obedience assumption.
pub fn constructor_client<E: Event>(principal: E::Principal, action: E::Action, resource: E::Resource)
    -> (rule: Rule<E>)
    ensures
        rule@.mode == RuleMode::Require,
        rule@.head.principal == PatternView::Constant(principal),
        rule@.head.action == PatternView::Constant(action),
        rule@.head.resource == PatternView::Constant(resource),
        rule@.tail == RegexView::Not(Box::new(RegexView::Epsilon)),
{
    proof! { reveal_with_fuel(regex_view, 2); }
    let head = Head::new(ComponentPattern::Constant(principal), ComponentPattern::Constant(action),
        ComponentPattern::Constant(resource));
    let tail = RegexExpr::complement(RegexExpr::epsilon());
    Rule::new(RuleMode::Require, head, tail)
}

/// The real scope bodies preserve declarations and reject a cross-coordinate use.
pub fn scope_client<'a>(name: &'a str) -> (result: Result<Component, crate::error::CompileError>)
    ensures result == Ok(Component::Principal),
{
    let mut scope = crate::syntax::VariableScope::new();
    let bound = scope.bind(Component::Principal, name);
    proof! { assert(bound is Ok); }
    let conflict = scope.bind(Component::Resource, name);
    proof! { assert(conflict is Err); }
    scope.resolve(Component::Principal, name)
}

}
