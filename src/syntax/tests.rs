//! White-box tests for source compilation, canonical reuse, and residual-state stability.

use bumpalo::Bump;

use super::compile::compile_rule;
use super::evaluate::derive;
use super::source::{
    AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use super::store::CanonicalStore;
use crate::model::{Action, Event};

fn variable_head() -> Head {
    Head::new(
        ComponentPattern::variable("principal"),
        ComponentPattern::variable("action"),
        ComponentPattern::variable("resource"),
    )
}

fn rule(tail: RegexExpr) -> Rule {
    Rule::new(RuleMode::Require, variable_head(), tail)
}

fn action_regex(action: Action) -> RegexExpr {
    RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(action)),
    ))
}

#[test]
fn aci_and_identity_normalization_reuse_handles() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);

    let left = RegexExpr::union([
        action_regex(Action::Read),
        RegexExpr::empty(),
        action_regex(Action::Edit),
        action_regex(Action::Read),
    ]);
    let left = compile_rule(&mut store, &rule(left)).unwrap().tail;

    let right = RegexExpr::union([action_regex(Action::Edit), action_regex(Action::Read)]);
    let right = compile_rule(&mut store, &rule(right)).unwrap().tail;
    assert_eq!(left, right);

    let concat = RegexExpr::concat([
        RegexExpr::epsilon(),
        action_regex(Action::Read),
        RegexExpr::epsilon(),
    ]);
    let concat = compile_rule(&mut store, &rule(concat)).unwrap().tail;
    let single = compile_rule(&mut store, &rule(action_regex(Action::Read)))
        .unwrap()
        .tail;
    assert_eq!(concat, single);

    let edit = action_regex(Action::Edit);
    let contradiction = RegexExpr::intersect([edit.clone(), RegexExpr::complement(edit)]);
    let contradiction = compile_rule(&mut store, &rule(contradiction)).unwrap().tail;
    assert_eq!(contradiction, store.empty);
}

#[test]
fn variable_names_share_string_symbols_across_rules() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let first = compile_rule(&mut store, &rule(RegexExpr::all())).unwrap();
    let second = compile_rule(&mut store, &rule(RegexExpr::all())).unwrap();

    let ComponentPattern::Variable(first_variable) = first.head.principal else {
        panic!("principal head pattern was not interned as a variable")
    };
    let ComponentPattern::Variable(second_variable) = second.head.principal else {
        panic!("principal head pattern was not interned as a variable")
    };
    assert_eq!(first_variable, second_variable);
    assert_eq!(store.resolver.string_count(), 3);
}

#[test]
fn derivative_cycle_returns_the_same_hashconsed_state() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let cycle = RegexExpr::star(RegexExpr::union([
        action_regex(Action::Read),
        action_regex(Action::Edit),
    ]));
    let compiled = compile_rule(&mut store, &rule(cycle)).unwrap();

    let event = Event::new("alice", Action::Read, ["a"]);
    let substitution = compiled.head.match_candidate(&mut store, &event).unwrap();
    let before = store.regex_node_count();
    let mut state = compiled.tail;
    for _ in 0..100 {
        state = derive(&mut store, state, &event, &substitution);
        assert_eq!(state, compiled.tail);
    }
    assert_eq!(store.regex_node_count(), before);
}
