//! Inclusion decisions on small tails whose answers are known, with every counterexample replayed
//! through the runtime's trace policy.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use junco_core::CompileError;

use crate::constraint::{Atom, Constraint, Operand, Universes, steps};
use crate::{Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Action {
    Read,
    Edit,
    Stage,
}

const ACTIONS: [Action; 3] = [Action::Read, Action::Edit, Action::Stage];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Access {
    principal: u32,
    action: Action,
    resource: u32,
}

impl Event for Access {
    type Principal = u32;
    type Action = Action;
    type Resource = u32;

    fn principal(self) -> u32 {
        self.principal
    }

    fn action(self) -> Action {
        self.action
    }

    fn resource(self) -> u32 {
        self.resource
    }
}

/// Resources that tails mention.
const X: u32 = 10;

fn finite_actions() -> Domains<Access> {
    Domains::infinite().with_actions(ACTIONS)
}

fn head() -> Head<Access> {
    Head::new(
        ComponentPattern::variable("p"),
        ComponentPattern::constant(Action::Edit),
        ComponentPattern::variable("r"),
    )
}

fn principal_is_p() -> TestExpr<Access> {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("p")),
    )
}

fn action_is(comparison: Comparison, action: Action) -> TestExpr<Access> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

fn resource_is(comparison: Comparison, resource: Option<u32>) -> TestExpr<Access> {
    let pattern = match resource {
        Some(value) => ComponentPattern::constant(value),
        None => ComponentPattern::variable("r"),
    };
    TestExpr::atom(comparison, AtomPattern::Resource(pattern))
}

fn ever(test: TestExpr<Access>) -> RegexExpr<Access> {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(test), RegexExpr::all()])
}

fn forbid(head: Head<Access>, tail: RegexExpr<Access>) -> Rule<Access> {
    Rule::new(RuleMode::Forbid, head, tail)
}

/// Instantiates counterexample components; fresh values equal no constant the tests use.
fn concrete(components: &Components<Access>) -> Access {
    let value = |value: Value<u32>| match value {
        Value::Constant(value) => value,
        Value::Fresh(number) => 1_000 + u32::try_from(number).unwrap(),
    };
    let Value::Constant(action) = components.action else {
        panic!("declared actions are never fresh");
    };
    Access {
        principal: value(components.principal),
        action,
        resource: value(components.resource),
    }
}

/// Whether some rule of `rules` denies the counterexample's candidate after its history, by the
/// runtime.
fn denied(rules: &[Rule<Access>], counterexample: &Counterexample<Access>) -> bool {
    let store = Arc::new(Store::new().unwrap());
    let rules = rules
        .iter()
        .map(|rule| TraceRule::new(rule.clone(), |_| (String::new(), Vec::new())));
    let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
    let history = History::from_events(store, counterexample.history.iter().map(concrete)).unwrap();
    let candidate = concrete(&counterexample.candidate);
    policy.decide(&history, &candidate).unwrap() != PolicyDecision::Grant
}

/// Decides `left ⊑ right` under `head()` with declared actions, replays a counterexample through
/// the runtime, and returns whether the inclusion holds.
fn included(left: &RegexExpr<Access>, right: &RegexExpr<Access>) -> bool {
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    match analyzer.tail_included(&head(), left, right).unwrap() {
        Inclusion::Holds => true,
        Inclusion::Counterexample(counterexample) => {
            assert!(
                denied(&[forbid(head(), left.clone())], &counterexample),
                "{counterexample:?} is not in the left tail"
            );
            assert!(
                !denied(&[forbid(head(), right.clone())], &counterexample),
                "{counterexample:?} is in the right tail"
            );
            false
        }
        Inclusion::Exhausted => panic!("search exceeded its graph budget"),
    }
}

#[test]
fn since_is_included_in_once_without_a_step() {
    // `Σ*·read·(P ≐ p)*` lies below `Σ*·read·Σ*` factor by factor, so the initial residual is
    // dead.
    let since = RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(action_is(Comparison::Eq, Action::Read)),
        RegexExpr::star(RegexExpr::test(principal_is_p())),
    ]);
    let once = ever(action_is(Comparison::Eq, Action::Read));
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    assert_eq!(
        analyzer.tail_included(&head(), &since, &once).unwrap(),
        Inclusion::Holds
    );
    assert!(!included(&once, &since));
}

#[test]
fn simulation_compares_counting_tails_factor_by_factor() {
    // A read nine events before a final read is a read nine events before the end: `read ≤ ⊤`
    // settles it at the root, where the search would track each pattern of reads among the
    // last ten events.
    let reads_then = |gap: usize, last: TestExpr<Access>| {
        let mut factors = Vec::from([
            RegexExpr::all(),
            RegexExpr::test(action_is(Comparison::Eq, Action::Read)),
        ]);
        factors.extend((0..gap).map(|_| RegexExpr::test(TestExpr::True)));
        factors.push(RegexExpr::test(last));
        RegexExpr::concat(factors)
    };
    let left = reads_then(8, action_is(Comparison::Eq, Action::Read));
    let right = reads_then(8, TestExpr::True);
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    assert_eq!(
        analyzer.tail_included(&head(), &left, &right).unwrap(),
        Inclusion::Holds
    );
    assert!(!included(&right, &left));
}

#[test]
fn simulation_compares_nested_tests() {
    // After a read, the narrow tail keeps every later event off reads and stages of `r`, the
    // broad one off reads of `r`. The narrow keep test's disjunct `A ≠ read ∧ A ≠ stage` lies below
    // the broad one's disjunct `A ≠ read` by a conjunct, so the initial residual is dead.
    let since = |keep: TestExpr<Access>| {
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(action_is(Comparison::Eq, Action::Read)),
            RegexExpr::star(RegexExpr::test(keep)),
        ])
    };
    let narrow = since(TestExpr::or([
        resource_is(Comparison::Neq, None),
        TestExpr::and([
            action_is(Comparison::Neq, Action::Read),
            action_is(Comparison::Neq, Action::Stage),
        ]),
    ]));
    let broad = since(TestExpr::or([
        resource_is(Comparison::Neq, None),
        action_is(Comparison::Neq, Action::Read),
    ]));
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    assert_eq!(
        analyzer.tail_included(&head(), &narrow, &broad).unwrap(),
        Inclusion::Holds
    );
    assert!(!included(&broad, &narrow));
}

#[test]
fn register_comparisons_split_on_the_constants_they_meet() {
    // Under κ_R = x, `R ≐ κ_R` is `R ≐ x`; otherwise it is `R ≐ κ_R ∧ R ≠ x`.
    let own = ever(resource_is(Comparison::Eq, None));
    let by_case = RegexExpr::union([
        ever(resource_is(Comparison::Eq, Some(X))),
        ever(TestExpr::and([
            resource_is(Comparison::Neq, Some(X)),
            resource_is(Comparison::Eq, None),
        ])),
    ]);
    assert!(included(&own, &by_case));
    assert!(!included(&own, &ever(resource_is(Comparison::Eq, Some(X)))));
}

#[test]
fn a_residual_reached_under_two_constraints_is_searched_under_both() {
    // A first event off the candidate's resource splits on whether that resource is x and leaves
    // the same residual either way. Only when it is not x can a second event on it avoid x.
    let tail = RegexExpr::intersect([
        RegexExpr::concat([
            RegexExpr::test(resource_is(Comparison::Neq, None)),
            RegexExpr::test(resource_is(Comparison::Eq, None)),
        ]),
        RegexExpr::complement(ever(resource_is(Comparison::Eq, Some(X)))),
    ]);
    assert!(!included(&tail, &RegexExpr::empty()));
}

#[test]
fn complement_reverses_inclusion() {
    let read = action_is(Comparison::Eq, Action::Read);
    let own_read = TestExpr::and([read.clone(), principal_is_p()]);
    let never_read = RegexExpr::complement(ever(read));
    let never_own_read = RegexExpr::complement(ever(own_read));
    assert!(included(&never_read, &never_own_read));
    assert!(!included(&never_own_read, &never_read));
}

#[test]
fn intersections_on_either_side() {
    let read = ever(action_is(Comparison::Eq, Action::Read));
    let own = ever(principal_is_p());
    let both = RegexExpr::intersect([read.clone(), own.clone()]);
    assert!(included(&both, &read));
    assert!(included(&both, &own));
    assert!(!included(&read, &both));
    assert!(included(
        &RegexExpr::intersect([read.clone(), RegexExpr::complement(own.clone())]),
        &RegexExpr::complement(both),
    ));
}

#[test]
fn concatenation_keeps_one_split_point_for_an_intersection() {
    // No prefix ends in both a read and an edit, so `(…read ∩ …edit)·Σ*` is empty, whereas
    // `…read·Σ* ∩ …edit·Σ*` lets the two conjuncts end at different points.
    let ends_in = |action| {
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(action_is(Comparison::Eq, action)),
        ])
    };
    let together = RegexExpr::concat([
        RegexExpr::intersect([ends_in(Action::Read), ends_in(Action::Edit)]),
        RegexExpr::all(),
    ]);
    let apart = RegexExpr::intersect([
        RegexExpr::concat([ends_in(Action::Read), RegexExpr::all()]),
        RegexExpr::concat([ends_in(Action::Edit), RegexExpr::all()]),
    ]);
    assert!(included(&together, &RegexExpr::empty()));
    assert!(!included(&apart, &RegexExpr::empty()));
    assert!(included(&together, &apart));
    assert!(!included(&apart, &together));
}

#[test]
fn counterexamples_are_shortest() {
    // Histories ending in a read, against histories of length at least two: the read alone is
    // the unique shortest counterexample.
    let ends_in_read = RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(action_is(Comparison::Eq, Action::Read)),
    ]);
    let at_least_two = RegexExpr::concat([
        RegexExpr::test(TestExpr::true_test()),
        RegexExpr::test(TestExpr::true_test()),
        RegexExpr::all(),
    ]);
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let verdict = analyzer
        .tail_included(&head(), &ends_in_read, &at_least_two)
        .unwrap();
    let Inclusion::Counterexample(counterexample) = verdict else {
        panic!("inclusion must fail");
    };
    assert_eq!(counterexample.history.len(), 1);
}

#[test]
fn a_register_and_a_constant_give_five_letters() {
    // `R ≐ κ_R ∨ R ≐ k`: under κ_R = k the resource is k or other; otherwise k, κ_R or other.
    let atoms = [
        Atom {
            component: 2,
            operand: Operand::Register,
        },
        Atom {
            component: 2,
            operand: Operand::Constant(0),
        },
    ];
    let universes: Universes = [None, None, None];
    let constraint = Constraint::head([None; 3], &universes).unwrap();
    let mut counts = steps(&constraint, &atoms, &universes)
        .iter()
        .map(|(_, letters)| letters.len())
        .collect::<Vec<_>>();
    counts.sort_unstable();
    assert_eq!(counts, [2, 3]);
}

#[test]
fn declared_actions_leave_no_other_action() {
    // An event whose action is none of the declared ones exists only if actions are infinite.
    let undeclared = ever(TestExpr::and(
        ACTIONS.map(|action| action_is(Comparison::Neq, action)),
    ));
    assert!(included(&undeclared, &RegexExpr::empty()));

    let mut analyzer = PolicyAnalyzer::new(Domains::infinite());
    let verdict = analyzer
        .tail_included(&head(), &undeclared, &RegexExpr::empty())
        .unwrap();
    let Inclusion::Counterexample(counterexample) = verdict else {
        panic!("an infinite action domain has a fourth action");
    };
    assert!(matches!(counterexample.history[0].action, Value::Fresh(_)));
}

#[test]
fn a_declared_register_takes_each_declared_value() {
    // The candidate's action is one of the declared actions, so its case analysis is exhaustive.
    let head = Head::new(
        ComponentPattern::variable("p"),
        ComponentPattern::variable("a"),
        ComponentPattern::variable("r"),
    );
    let own_action = ever(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::variable("a")),
    ));
    let by_case = RegexExpr::union(ACTIONS.map(|action| ever(action_is(Comparison::Eq, action))));

    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let verdict = analyzer
        .tail_included(&head, &own_action, &by_case)
        .unwrap();
    assert_eq!(verdict, Inclusion::Holds);

    let mut analyzer = PolicyAnalyzer::new(Domains::infinite());
    let verdict = analyzer
        .tail_included(&head, &own_action, &by_case)
        .unwrap();
    let Inclusion::Counterexample(counterexample) = verdict else {
        panic!("an infinite action domain has a fourth action");
    };
    assert!(matches!(counterexample.candidate.action, Value::Fresh(_)));
    assert_eq!(
        counterexample.history[0].action,
        counterexample.candidate.action
    );
}

#[test]
fn added_rules_get_consecutive_ids_and_ill_scoped_rules_are_rejected() {
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let first = analyzer
        .add_rule(&forbid(head(), ever(resource_is(Comparison::Eq, Some(X)))))
        .unwrap();
    let second = analyzer
        .add_rule(&forbid(head(), ever(principal_is_p())))
        .unwrap();
    assert_eq!((first.0, second.0), (0, 1));
    assert_eq!(analyzer.rules.len(), 2);
    assert_eq!(analyzer.rules[0].constants[1], analyzer.rules[1].constants[1]);
    assert!(analyzer.rules[0].constants[0].is_none());

    let unbound = ever(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("q")),
    ));
    assert!(matches!(
        analyzer.add_rule(&forbid(head(), unbound)),
        Err(CompileError::UnboundVariable { .. })
    ));
    assert_eq!(analyzer.rules.len(), 2);
}
