use bumpalo::Bump;

use super::builder::RuleSyntax;
use super::node::Regex;
use super::pattern::{AtomPattern, Comparison, ComponentPattern, Head};
use super::storage::SyntaxContext;
use crate::model::{Action, Event};

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
