//! White-box tests for canonicalization, name interning, and derivative-state reuse.

use bumpalo::Bump;

use super::builder::RuleSyntax;
use super::node::Regex;
use super::pattern::{AtomPattern, Comparison, ComponentPattern, Head};
use super::scope::CompiledHead;
use super::storage::SyntaxContext;
use crate::model::{Action, Event};
use crate::validator::RuleIndex;

fn variable_head() -> Head {
    Head::new(
        ComponentPattern::variable("principal"),
        ComponentPattern::variable("action"),
        ComponentPattern::variable("resource"),
    )
}

fn new_rule<'context, 'arena>(
    syntax: &'context mut SyntaxContext<'arena>,
    one_based: usize,
) -> (CompiledHead<'arena>, RuleSyntax<'context, 'arena>) {
    let rule = RuleIndex::new(one_based).expect("test rule indexes are non-zero");
    let scope = syntax.new_rule_scope();
    RuleSyntax::new(syntax, rule, scope, &variable_head()).unwrap()
}

fn action_regex<'arena>(syntax: &mut RuleSyntax<'_, 'arena>, action: Action) -> Regex<'arena> {
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

    let (_, mut first) = new_rule(&mut syntax, 1);
    let read = action_regex(&mut first, Action::Read);
    let edit = action_regex(&mut first, Action::Edit);
    let empty = first.empty();
    let left = first.union([read, empty, edit, read]);
    let left = first.regex_id(left);
    drop(first);

    let (_, mut second) = new_rule(&mut syntax, 2);
    let edit = action_regex(&mut second, Action::Edit);
    let read = action_regex(&mut second, Action::Read);
    let right = second.union([edit, read]);
    let right = second.regex_id(right);
    assert_eq!(left, right);
    drop(second);

    let (_, mut third) = new_rule(&mut syntax, 3);
    let epsilon = third.epsilon();
    let read = action_regex(&mut third, Action::Read);
    let concat = third.concat([epsilon, read, epsilon]);
    let concat = third.regex_id(concat);
    drop(third);

    let (_, mut fourth) = new_rule(&mut syntax, 4);
    let single = action_regex(&mut fourth, Action::Read);
    let single = fourth.regex_id(single);
    assert_eq!(concat, single);
    drop(fourth);

    let (_, mut fifth) = new_rule(&mut syntax, 5);
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
    let (first, first_syntax) = new_rule(&mut syntax, 1);
    drop(first_syntax);
    let (second, second_syntax) = new_rule(&mut syntax, 2);
    drop(second_syntax);

    let ComponentPattern::Variable(first_symbol) = first.principal else {
        panic!("principal head pattern was not compiled as a variable")
    };
    let ComponentPattern::Variable(second_symbol) = second.principal else {
        panic!("principal head pattern was not compiled as a variable")
    };
    assert_eq!(first_symbol, second_symbol);
    assert_eq!(syntax.variables.resolve(first_symbol), Some("principal"));
    assert_eq!(syntax.variables.len(), 3);
}

#[test]
fn derivative_cycle_returns_the_same_hashconsed_state() {
    let arena = Bump::new();
    let mut syntax = SyntaxContext::new(&arena);
    let (head, mut rule) = new_rule(&mut syntax, 1);
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
