//! R2: denotational policy semantics over real events and oldest-first histories.
//! A candidate supplies the head variables; the candidate is not part of the history.

use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{HeadView, PatternView, RegexView, TestView, arity, event_view};
use history_syntax::{Comparison, Rule, RuleMode};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// A head matches iff every constant equals its coordinate of the candidate (Section 3).
pub open spec fn head_matches<E: Event>(head: HeadView<E::Component>, candidate: E) -> bool {
    head.len() == arity::<E>() && forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
        PatternView::Constant(value) => event_view(candidate)[i].eq_spec(&value),
        PatternView::Variable(_) => true,
    }
}

/// Resolves one scoped head variable, or retains a literal constant (Section 3).
pub open spec fn resolve<C>(pattern: PatternView<C>, binding: PatternView<C>, actual: C) -> Option<C> {
    match pattern {
        PatternView::Constant(value) => Some(value),
        PatternView::Variable(name) => match binding {
            PatternView::Variable(bound) => if name == bound { Some(actual) } else { None },
            PatternView::Constant(_) => None,
        },
    }
}

/// Component-local tests compare a history event with the candidate substitution (Section 3).
pub open spec fn test_sem<E: Event>(test: TestView<E::Component>, head: HeadView<E::Component>,
    candidate: E, event: E) -> bool
    decreases test,
{
    match test {
        TestView::True => true,
        TestView::False => false,
        TestView::Atom { comparison, pattern } => pattern.component < head.len()
            && pattern.component < arity::<E>() && match resolve(pattern.pattern,
                head[pattern.component as int], event_view(candidate)[pattern.component as int]) {
                None => false,
                Some(value) => match comparison {
                    Comparison::Eq => event_view(event)[pattern.component as int].eq_spec(&value),
                    Comparison::Neq => !event_view(event)[pattern.component as int].eq_spec(&value),
                },
            },
        TestView::And(children) => forall|i: int| 0 <= i < children.len()
            ==> test_sem(#[trigger] children[i], head, candidate, event),
        TestView::Or(children) => exists|i: int| 0 <= i < children.len()
            && test_sem(#[trigger] children[i], head, candidate, event),
    }
}

/// Tail-language membership with the candidate fixed, excluding it from the word (Section 3).
pub open spec fn lang<E: Event>(regex: RegexView<E::Component>, head: HeadView<E::Component>,
    candidate: E, word: Seq<E>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty => false,
        RegexView::All => true,
        RegexView::Epsilon => word.len() == 0,
        RegexView::Test(test) => word.len() == 1 && test_sem(test, head, candidate, word[0]),
        RegexView::Union(children) => exists|i: int| 0 <= i < children.len()
            && lang(#[trigger] children[i], head, candidate, word),
        RegexView::Intersect(children) => forall|i: int| 0 <= i < children.len()
            ==> lang(#[trigger] children[i], head, candidate, word),
        RegexView::Not(child) => !lang(*child, head, candidate, word),
        RegexView::Concat(children) => exists|parts: Seq<Seq<E>>| parts.len() == children.len()
            && word == parts.flatten() && forall|i: int| 0 <= i < children.len()
                ==> lang(#[trigger] children[i], head, candidate, parts[i]),
        RegexView::Star(child) => exists|parts: Seq<Seq<E>>| word == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(*child, head, candidate, #[trigger] parts[i]),
    }
}

/// A matching Forbid rule denies an accepted tail; Require denies its complement (Section 3).
pub open spec fn rule_violated<E: Event>(rule: Rule<E>, candidate: E, history: Seq<E>) -> bool {
    head_matches(rule.head@, candidate) && match rule.mode {
        RuleMode::Forbid => lang(rule.tail@, rule.head@, candidate, history),
        RuleMode::Require => !lang(rule.tail@, rule.head@, candidate, history),
    }
}

/// A policy denies iff at least one of its rules is violated (Section 3).
pub open spec fn policy_denies<E: Event>(rules: Seq<Rule<E>>, candidate: E, history: Seq<E>) -> bool {
    exists|i: int| 0 <= i < rules.len() && #[trigger] rule_violated(rules[i], candidate, history)
}

/// The index identifies the first violated rule in source order (monitor theorem).
pub open spec fn least_violation<E: Event>(rules: Seq<Rule<E>>, history: Seq<E>, candidate: E, index: int) -> bool {
    0 <= index < rules.len() && rule_violated(rules[index], candidate, history)
        && forall|j: int| 0 <= j < index ==> !#[trigger] rule_violated(rules[j], candidate, history)
}

/// A head has the event arity, correctly tagged literals, and distinct bound variable names.
pub open spec fn head_wf<E: Event>(head: HeadView<E::Component>) -> bool {
    head.len() == arity::<E>()
        && (forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
            PatternView::Constant(value) => E::coordinate_spec(value) == i,
            PatternView::Variable(_) => true,
        })
        && (forall|i: int, j: int| 0 <= i < j < head.len() ==> match (#[trigger] head[i], #[trigger] head[j]) {
            (PatternView::Variable(a), PatternView::Variable(b)) => a != b,
            _ => true,
        })
}

/// Tests use valid coordinates and only their head-bound variable or correctly tagged constants.
pub open spec fn test_wf<E: Event>(test: TestView<E::Component>, head: HeadView<E::Component>) -> bool
    decreases test,
{
    match test {
        TestView::True | TestView::False => true,
        TestView::Atom { pattern, .. } => pattern.component < head.len() && match pattern.pattern {
            PatternView::Constant(value) => E::coordinate_spec(value) == pattern.component,
            PatternView::Variable(name) => match head[pattern.component as int] {
                PatternView::Variable(bound) => name == bound,
                _ => false,
            },
        },
        TestView::And(children) => forall|i: int| 0 <= i < children.len() ==> test_wf::<E>(#[trigger] children[i], head),
        TestView::Or(children) => forall|i: int| 0 <= i < children.len() ==> test_wf::<E>(#[trigger] children[i], head),
    }
}

/// Every tail atom is scoped and tagged for the coordinate it tests.
pub open spec fn regex_wf<E: Event>(regex: RegexView<E::Component>, head: HeadView<E::Component>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => true,
        RegexView::Test(test) => test_wf::<E>(test, head),
        RegexView::Union(children) => forall|i: int| 0 <= i < children.len() ==> regex_wf::<E>(#[trigger] children[i], head),
        RegexView::Concat(children) => forall|i: int| 0 <= i < children.len() ==> regex_wf::<E>(#[trigger] children[i], head),
        RegexView::Intersect(children) => forall|i: int| 0 <= i < children.len() ==> regex_wf::<E>(#[trigger] children[i], head),
        RegexView::Star(child) | RegexView::Not(child) => regex_wf::<E>(*child, head),
    }
}

/// Accepted source rules have the event arity, scoped variables, and coordinate-correct constants.
pub open spec fn rule_wf<E: Event>(rule: Rule<E>) -> bool {
    head_wf::<E>(rule.head@) && regex_wf::<E>(rule.tail@, rule.head@)
}

/// A borrowed head and both tails have the event arity, scoped variables, and correct tags.
pub open spec fn head_tails_wf<E: Event>(head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>) -> bool {
    head_wf::<E>(head) && regex_wf::<E>(left, head) && regex_wf::<E>(right, head)
}

}
