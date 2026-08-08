//! White-box tests for source compilation, canonical reuse, and residual-state stability.

use bumpalo::Bump;

use super::compile::compile_rule;
use super::evaluate::{DerivativeCache, accepts_direct, derive, derive_cached};
use super::node::{RegexKind, TestId, TransitionId, TransitionNode};
use super::source::{
    AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use super::store::CanonicalStore;
use super::symbolic::{SymbolicDerivativeCache, accepts, eval_transition, symbolic_derivative};
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

fn action_test<'arena>(store: &mut CanonicalStore<'arena>, action: Action) -> TestId<'arena> {
    let regex = compile_rule(store, &rule(action_regex(action)))
        .unwrap()
        .tail;
    let RegexKind::Test(test) = regex.get().kind else {
        panic!("action atom must compile to one test regex")
    };
    test
}

fn assert_transition_normalized(transition: TransitionId<'_>) {
    match *transition.get() {
        TransitionNode::Const(_) => {}
        TransitionNode::If {
            test,
            then_transition,
            else_transition,
        } => {
            assert!(!matches!(
                *test.get(),
                super::node::TestNode::True | super::node::TestNode::False
            ));
            assert_ne!(then_transition, else_transition);
            assert_transition_normalized(then_transition);
            assert_transition_normalized(else_transition);
        }
        TransitionNode::Union(children) => {
            assert!(children.len() >= 2);
            assert!(children.windows(2).all(|pair| pair[0] < pair[1]));
            assert!(
                children
                    .iter()
                    .all(|child| !matches!(child.get(), TransitionNode::Union(_)))
            );
            children
                .iter()
                .copied()
                .for_each(assert_transition_normalized);
        }
        TransitionNode::Intersect(_) | TransitionNode::Not(_) | TransitionNode::Append { .. } => {
            panic!("normalized transition must be DNF conditionals with regex leaves")
        }
    }
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
        panic!("principal head pattern was not compiled as a variable")
    };
    let ComponentPattern::Variable(second_variable) = second.head.principal else {
        panic!("principal head pattern was not compiled as a variable")
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
    let runtime_rule = compile_rule(&mut store, &rule(cycle)).unwrap();

    let event = Event::new("alice", Action::Read, ["a"]);
    let substitution = runtime_rule
        .head
        .match_candidate(&mut store, &event)
        .unwrap();
    let before = store.regex_node_count();
    let mut state = runtime_rule.tail;
    for _ in 0..100 {
        state = derive(&mut store, state, &event, &substitution);
        assert_eq!(state, runtime_rule.tail);
    }
    assert_eq!(store.regex_node_count(), before);
}

#[test]
fn concrete_derivatives_reuse_equal_event_transitions() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let cycle = RegexExpr::star(RegexExpr::union([
        action_regex(Action::Read),
        action_regex(Action::Edit),
    ]));
    let runtime_rule = compile_rule(&mut store, &rule(cycle)).unwrap();
    let first_event = Event::new("alice", Action::Read, ["a"]);
    let equal_event = first_event.clone();
    let substitution = runtime_rule
        .head
        .match_candidate(&mut store, &first_event)
        .unwrap();
    let mut derivatives = DerivativeCache::new();

    let first = derive_cached(
        &mut store,
        runtime_rule.tail,
        &first_event,
        &substitution,
        &mut derivatives,
    );
    let entries = derivatives.len();
    assert!(entries > 1, "recursive derivatives must share the cache");

    let second = derive_cached(
        &mut store,
        runtime_rule.tail,
        &equal_event,
        &substitution,
        &mut derivatives,
    );
    assert_eq!(second, first);
    assert_eq!(derivatives.len(), entries);
}

#[test]
fn boolean_and_regex_normalization_matches_symbolic_specification() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let read = action_regex(Action::Read);
    let edit = action_regex(Action::Edit);

    let absorbed = RegexExpr::test(TestExpr::and([
        match read.clone() {
            RegexExpr::Test(test) => test,
            _ => unreachable!(),
        },
        TestExpr::or([
            match read.clone() {
                RegexExpr::Test(test) => test,
                _ => unreachable!(),
            },
            match edit.clone() {
                RegexExpr::Test(test) => test,
                _ => unreachable!(),
            },
        ]),
    ]));
    let absorbed = compile_rule(&mut store, &rule(absorbed)).unwrap().tail;
    let read = compile_rule(&mut store, &rule(read)).unwrap().tail;
    assert_eq!(absorbed, read);

    let contradiction = RegexExpr::test(TestExpr::and([
        match action_regex(Action::Read) {
            RegexExpr::Test(test) => test,
            _ => unreachable!(),
        },
        match action_regex(Action::Edit) {
            RegexExpr::Test(test) => test,
            _ => unreachable!(),
        },
    ]));
    let contradiction = compile_rule(&mut store, &rule(contradiction)).unwrap().tail;
    assert_eq!(contradiction, store.empty);

    let top_star = RegexExpr::star(RegexExpr::test(TestExpr::true_test()));
    let top_star = compile_rule(&mut store, &rule(top_star)).unwrap().tail;
    assert_eq!(top_star, store.all);
}

#[test]
fn transition_normalization_applies_dnf_and_path_cleaning() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let read_test = action_test(&mut store, Action::Read);
    let edit_test = action_test(&mut store, Action::Edit);
    let not_read = store.test_not(read_test);
    let read_regex = store.regex_test(read_test);

    assert_eq!(
        store.transition_union(vec![store.transition_empty, store.transition_epsilon]),
        store.transition_epsilon
    );
    assert_eq!(
        store.transition_intersect(vec![store.transition_all, store.transition_epsilon]),
        store.transition_epsilon
    );

    let nested = store.transition_if(not_read, store.transition_epsilon, store.transition_all);
    let cleaned = store.transition_if(read_test, nested, store.transition_empty);
    let expected = store.transition_if(read_test, store.transition_all, store.transition_empty);
    assert_eq!(cleaned, expected);

    let read_branch =
        store.transition_if(read_test, store.transition_epsilon, store.transition_empty);
    let edit_branch =
        store.transition_if(edit_test, store.transition_epsilon, store.transition_empty);
    assert_eq!(
        store.transition_intersect(vec![read_branch, edit_branch]),
        store.transition_empty
    );

    let disjunction = store.transition_union(vec![read_branch, edit_branch]);
    assert_eq!(
        store.transition_intersect(vec![disjunction, read_branch]),
        read_branch
    );
    assert_eq!(
        store.transition_append(store.transition_epsilon, &[read_regex]),
        store.transition_const(read_regex)
    );

    let complemented = store.transition_not(expected);
    let expected_complement =
        store.transition_if(not_read, store.transition_all, store.transition_empty);
    assert_eq!(complemented, expected_complement);
    assert_transition_normalized(complemented);
}

#[test]
fn symbolic_derivatives_equal_concrete_derivatives_for_every_regex_form() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let read = action_regex(Action::Read);
    let edit = action_regex(Action::Edit);
    let cases = [
        RegexExpr::empty(),
        RegexExpr::all(),
        RegexExpr::epsilon(),
        read.clone(),
        RegexExpr::union([read.clone(), RegexExpr::star(edit.clone())]),
        RegexExpr::intersect([
            RegexExpr::star(read.clone()),
            RegexExpr::complement(RegexExpr::epsilon()),
        ]),
        RegexExpr::concat([
            RegexExpr::star(read.clone()),
            edit.clone(),
            RegexExpr::all(),
        ]),
        RegexExpr::star(RegexExpr::union([read.clone(), edit.clone()])),
        RegexExpr::complement(RegexExpr::concat([read, edit])),
    ];
    let candidate = Event::new("alice", Action::Read, ["a"]);

    for source in cases {
        let runtime_rule = compile_rule(&mut store, &rule(source)).unwrap();
        let substitution = runtime_rule
            .head
            .match_candidate(&mut store, &candidate)
            .unwrap();
        let mut derivatives = SymbolicDerivativeCache::new();
        let transition = symbolic_derivative(&mut store, &mut derivatives, runtime_rule.tail);
        assert_transition_normalized(transition);
        for action in [Action::Read, Action::Edit, Action::Stage] {
            let event = Event::new("alice", action, ["a"]);
            let concrete = derive(&mut store, runtime_rule.tail, &event, &substitution);
            let symbolic = eval_transition(&mut store, transition, &substitution, &event);
            assert_eq!(symbolic, concrete);
        }
        let history = [
            Event::new("alice", Action::Read, ["a"]),
            Event::new("alice", Action::Edit, ["a"]),
            Event::new("alice", Action::Stage, ["a"]),
        ];
        let direct = accepts_direct(&mut store, runtime_rule.tail, history.iter(), &substitution);
        let symbolic = accepts(
            &mut store,
            &mut derivatives,
            runtime_rule.tail,
            history.iter(),
            &substitution,
        );
        assert_eq!(symbolic, direct);
    }
}

#[test]
fn symbolic_derivative_cache_is_shared_across_events_and_bindings() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let tail = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::variable("action")),
    ));
    let mut runtime_rule = compile_rule(&mut store, &rule(tail)).unwrap();
    let read = Event::new("alice", Action::Read, ["a"]);
    let edit = Event::new("bob", Action::Edit, ["b"]);

    assert_eq!(
        runtime_rule.accepts_history(&mut store, std::slice::from_ref(&read), &read),
        Some(true)
    );
    let derivatives = runtime_rule.derivative_count();
    let transitions = store.transition_node_count();
    assert_eq!(derivatives, 1);

    assert_eq!(
        runtime_rule.accepts_history(&mut store, std::slice::from_ref(&edit), &edit),
        Some(true)
    );
    assert_eq!(runtime_rule.derivative_count(), derivatives);
    assert_eq!(store.transition_node_count(), transitions);
}
