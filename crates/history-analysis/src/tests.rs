//! Inclusion decisions on small tails whose answers are known, with every counterexample replayed
//! through the runtime's trace policy.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Event, Head, N1, N2, N3, N4, N8,
    RegexExpr, Rule, RuleMode, TestExpr,
};
use junco_core::{CompileError, HistoryError};

use crate::constraint::{Atom, Constraint, Operand, Universes, steps};
use crate::{
    Components, Counterexample, DomainError, Domains, Inclusion, PolicyAnalyzer, RuleId, Value,
};
use junco_core::HistoryError;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum AccessComponent {
    Principal(u32),
    Action(Action),
    Resource(u32),
}

impl Event for Access {
    type Component = AccessComponent;
    type Arity = N3;

    fn component(self, index: usize) -> AccessComponent {
        match index {
            0 => AccessComponent::Principal(self.principal),
            1 => AccessComponent::Action(self.action),
            _ => AccessComponent::Resource(self.resource),
        }
    }

    fn coordinate(component: AccessComponent) -> usize {
        match component {
            AccessComponent::Principal(_) => 0,
            AccessComponent::Action(_) => 1,
            AccessComponent::Resource(_) => 2,
        }
    }
}

/// Resources that tails mention.
const X: u32 = 10;

fn finite_actions() -> Domains<Access> {
    Domains::infinite()
        .with_domain(Component(1), &ACTIONS.map(AccessComponent::Action))
        .expect("domain")
}

fn head() -> Head<Access> {
    Head::new([
        ComponentPattern::variable("p"),
        ComponentPattern::constant(AccessComponent::Action(Action::Edit)),
        ComponentPattern::variable("r"),
    ])
}

fn principal_is_p() -> TestExpr<Access> {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::new(Component(0), ComponentPattern::variable("p")),
    )
}

fn action_is(comparison: Comparison, action: Action) -> TestExpr<Access> {
    TestExpr::atom(
        comparison,
        AtomPattern::new(
            Component(1),
            ComponentPattern::constant(AccessComponent::Action(action)),
        ),
    )
}

fn resource_is(comparison: Comparison, resource: Option<u32>) -> TestExpr<Access> {
    let pattern = match resource {
        Some(value) => ComponentPattern::constant(AccessComponent::Resource(value)),
        None => ComponentPattern::variable("r"),
    };
    TestExpr::atom(comparison, AtomPattern::new(Component(2), pattern))
}

fn ever(test: TestExpr<Access>) -> RegexExpr<Access> {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(test), RegexExpr::all()])
}

fn forbid(head: Head<Access>, tail: RegexExpr<Access>) -> Rule<Access> {
    Rule::new(RuleMode::Forbid, head, tail)
}

/// Instantiates counterexample components; fresh values equal no constant the tests use.
fn concrete(components: &Components<Access>) -> Access {
    assert_eq!(components.values.len(), 3);
    let principal = match components.values[0] {
        Value::Constant(AccessComponent::Principal(value)) => value,
        Value::Fresh(number) => 1_000 + u32::try_from(number).unwrap(),
        _ => panic!("principal constant has the wrong coordinate"),
    };
    let Value::Constant(AccessComponent::Action(action)) = components.values[1] else {
        panic!("declared actions are never fresh or another coordinate");
    };
    let resource = match components.values[2] {
        Value::Constant(AccessComponent::Resource(value)) => value,
        Value::Fresh(number) => 1_000 + u32::try_from(number).unwrap(),
        _ => panic!("resource constant has the wrong coordinate"),
    };
    Access {
        principal,
        action,
        resource,
    }
}

/// Whether some rule of `rules` denies the counterexample's candidate after its history, by the
/// runtime.
fn denied<E: Event + 'static>(
    rules: &[Rule<E>],
    counterexample: &Counterexample<E>,
    concrete: impl Fn(&Components<E>) -> E,
) -> bool {
    let store = Arc::new(Store::new().unwrap());
    let rules = rules
        .iter()
        .map(|rule| TraceRule::new(rule.clone(), |_| (String::new(), Vec::new())));
    let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
    let history =
        History::from_events(store, counterexample.history.iter().map(&concrete)).unwrap();
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
                denied(&[forbid(head(), left.clone())], &counterexample, concrete),
                "{counterexample:?} is not in the left tail"
            );
            assert!(
                !denied(&[forbid(head(), right.clone())], &counterexample, concrete),
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
    let universes: Universes = Vec::from([None, None, None]);
    let constraint = Constraint::head(&[None; 3], &universes).unwrap();
    let mut counts = steps(&constraint, &atoms, &universes)
        .unwrap()
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
    assert!(matches!(
        counterexample.history[0].values[1],
        Value::Fresh(_)
    ));
}

#[test]
fn a_declared_register_takes_each_declared_value() {
    // The candidate's action is one of the declared actions, so its case analysis is exhaustive.
    let head = Head::new([
        ComponentPattern::variable("p"),
        ComponentPattern::variable("a"),
        ComponentPattern::variable("r"),
    ]);
    let own_action = ever(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::new(Component(1), ComponentPattern::variable("a")),
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
    assert!(matches!(
        counterexample.candidate.values[1],
        Value::Fresh(_)
    ));
    assert_eq!(
        counterexample.history[0].values[1],
        counterexample.candidate.values[1]
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct IndexedComponent {
    coordinate: usize,
    value: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct IndexedEvent<const N: usize>([u16; N]);

macro_rules! indexed_event {
    ($length:literal, $arity:ty) => {
        impl Event for IndexedEvent<$length> {
            type Component = IndexedComponent;
            type Arity = $arity;

            fn component(self, index: usize) -> IndexedComponent {
                let coordinate = index.min($length - 1);
                IndexedComponent {
                    coordinate,
                    value: self.0[coordinate],
                }
            }

            fn coordinate(component: IndexedComponent) -> usize {
                component.coordinate
            }
        }
    };
}

indexed_event!(1, N1);
indexed_event!(4, N4);
indexed_event!(8, N8);

const VARIABLES: [&str; 8] = ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"];

fn concrete_indexed<const N: usize>(components: &Components<IndexedEvent<N>>) -> IndexedEvent<N>
where
    IndexedEvent<N>: Event<Component = IndexedComponent>,
{
    assert_eq!(components.values.len(), N);
    IndexedEvent(core::array::from_fn(|coordinate| {
        let Value::Constant(component) = components.values[coordinate] else {
            panic!("finite coordinate {coordinate} must reconstruct a constant");
        };
        assert_eq!(component.coordinate, coordinate);
        assert!(component.value <= 1);
        component.value
    }))
}

fn check_non_three_arity<const N: usize>()
where
    IndexedEvent<N>: Event<Component = IndexedComponent>,
{
    let head = Head::<IndexedEvent<N>>::new(
        VARIABLES[..N]
            .iter()
            .map(|&name| ComponentPattern::variable(name)),
    );
    let same = RegexExpr::test(TestExpr::and((0..N).map(|coordinate| {
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::new(
                Component(coordinate as u8),
                ComponentPattern::variable(VARIABLES[coordinate]),
            ),
        )
    })));
    for (different, &different_name) in VARIABLES[..N].iter().enumerate() {
        // Vary two axes at most: exercise every coordinate without a large Cartesian product.
        let mut domains = Domains::<IndexedEvent<N>>::infinite();
        for coordinate in 0..N {
            let count = if coordinate == different || coordinate == (different + 1) % N {
                2
            } else {
                1
            };
            let values: Vec<_> = (0..count)
                .map(|value| IndexedComponent { coordinate, value })
                .collect();
            domains = domains
                .with_domain(Component(coordinate as u8), &values)
                .expect("domain");
        }
        let different_axis = RegexExpr::test(TestExpr::atom(
            Comparison::Neq,
            AtomPattern::new(
                Component(different as u8),
                ComponentPattern::variable(different_name),
            ),
        ));
        let mut analyzer = PolicyAnalyzer::new(domains);
        assert_eq!(
            analyzer
                .tail_included(&head, &same, &RegexExpr::test(TestExpr::True))
                .unwrap(),
            Inclusion::Holds,
        );
        let verdict = analyzer
            .tail_included(&head, &different_axis, &same)
            .unwrap();
        let Inclusion::Counterexample(counterexample) = verdict else {
            panic!("coordinate {different} of arity {N} must distinguish the tails");
        };
        assert_eq!(counterexample.history.len(), 1);
        let candidate = concrete_indexed(&counterexample.candidate);
        let event = concrete_indexed(&counterexample.history[0]);
        assert_ne!(event.0[different], candidate.0[different]);
        assert!(denied(
            &[Rule::new(RuleMode::Forbid, head.clone(), different_axis)],
            &counterexample,
            concrete_indexed,
        ));
        assert!(!denied(
            &[Rule::new(RuleMode::Forbid, head.clone(), same.clone())],
            &counterexample,
            concrete_indexed,
        ));
    }
}

#[test]
fn one_coordinate_inclusion_and_counterexamples() {
    check_non_three_arity::<1>();
}

#[test]
fn four_coordinate_inclusion_and_counterexamples() {
    check_non_three_arity::<4>();
}

#[test]
fn eight_coordinate_inclusion_and_counterexamples() {
    check_non_three_arity::<8>();
}

#[test]
fn overflowing_eight_coordinate_register_product_is_an_index_error() {
    // 256^8 exceeds usize::MAX on both 32- and 64-bit targets. The analyzer must check
    // the whole product before reserving or enumerating any of its rows, and an overflow is
    // `GraphIndex`, never the budget verdict `Exhausted`.
    let mut domains = Domains::<IndexedEvent<8>>::infinite();
    for coordinate in 0..8 {
        let values: Vec<_> = (0..256)
            .map(|value| IndexedComponent { coordinate, value })
            .collect();
        domains = domains
            .with_domain(Component(coordinate as u8), &values)
            .expect("domain");
    }
    let head = Head::new(VARIABLES.map(ComponentPattern::variable));
    let tail = RegexExpr::test(TestExpr::and((0..8).map(|coordinate| {
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::new(
                Component(coordinate as u8),
                ComponentPattern::variable(VARIABLES[coordinate]),
            ),
        )
    })));
    let mut analyzer = PolicyAnalyzer::new(domains);
    assert_eq!(
        analyzer.tail_included(&head, &tail, &RegexExpr::empty()),
        Err(CompileError::Runtime(HistoryError::GraphIndex)),
    );
}

#[derive(Clone, Copy, Debug)]
struct UntaggedEqualityComponent {
    coordinate: usize,
    value: u16,
}

impl PartialEq for UntaggedEqualityComponent {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Eq for UntaggedEqualityComponent {}

impl core::hash::Hash for UntaggedEqualityComponent {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        core::hash::Hash::hash(&self.value, state);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct UntaggedEqualityEvent([u16; 2]);

impl Event for UntaggedEqualityEvent {
    type Component = UntaggedEqualityComponent;
    type Arity = N2;

    fn component(self, index: usize) -> UntaggedEqualityComponent {
        let coordinate = index.min(1);
        UntaggedEqualityComponent {
            coordinate,
            value: self.0[coordinate],
        }
    }

    fn coordinate(component: UntaggedEqualityComponent) -> usize {
        component.coordinate
    }
}

#[test]
fn constants_remain_coordinate_separated_when_equality_ignores_tags() {
    let constant = |coordinate, value| UntaggedEqualityComponent { coordinate, value };
    assert_eq!(constant(0, 7), constant(1, 7));
    let domains = Domains::<UntaggedEqualityEvent>::infinite()
        .with_domain(Component(0), &[constant(0, 7), constant(0, 9)])
        .expect("domain")
        .with_domain(Component(1), &[constant(1, 7), constant(1, 9)])
        .expect("domain");
    let head =
        Head::new((0..2).map(|coordinate| ComponentPattern::constant(constant(coordinate, 7))));
    let tail = RegexExpr::test(TestExpr::and((0..2).map(|coordinate| {
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::new(
                Component(coordinate as u8),
                ComponentPattern::constant(constant(coordinate, 9)),
            ),
        )
    })));
    let mut analyzer = PolicyAnalyzer::new(domains);
    let verdict = analyzer
        .tail_included(&head, &tail, &RegexExpr::empty())
        .unwrap();
    let Inclusion::Counterexample(counterexample) = verdict else {
        panic!("the two-coordinate constant tail is inhabited");
    };
    assert_eq!(counterexample.history.len(), 1);
    let concrete = |components: &Components<UntaggedEqualityEvent>| {
        assert_eq!(components.values.len(), 2);
        UntaggedEqualityEvent(core::array::from_fn(|coordinate| {
            let Value::Constant(component) = components.values[coordinate] else {
                panic!("a finite component must reconstruct a constant");
            };
            // Comparing components with Eq would miss a representative from the wrong axis.
            assert_eq!(component.coordinate, coordinate);
            component.value
        }))
    };
    assert_eq!(
        concrete(&counterexample.candidate),
        UntaggedEqualityEvent([7, 7])
    );
    assert_eq!(
        concrete(&counterexample.history[0]),
        UntaggedEqualityEvent([9, 9])
    );
    assert!(denied(
        &[Rule::new(RuleMode::Forbid, head.clone(), tail)],
        &counterexample,
        concrete,
    ));
    assert!(!denied(
        &[Rule::new(RuleMode::Forbid, head, RegexExpr::empty())],
        &counterexample,
        concrete,
    ));
}

#[test]
fn declared_domains_reject_empty_foreign_and_out_of_arity() {
    let domains = Domains::<Access>::infinite();
    assert_eq!(
        domains.clone().with_domain(Component(1), &[]).err(),
        Some(DomainError::Empty)
    );
    assert_eq!(
        domains
            .clone()
            .with_domain(Component(1), &[AccessComponent::Resource(1)])
            .err(),
        Some(DomainError::WrongCoordinate)
    );
    assert_eq!(
        domains
            .with_domain(Component(3), &[AccessComponent::Resource(1)])
            .err(),
        Some(DomainError::OutOfArity)
    );
}

#[test]
fn rule_ids_belong_to_their_analyzer() {
    let rule = forbid(head(), ever(action_is(Comparison::Eq, Action::Edit)));
    let mut first = PolicyAnalyzer::new(Domains::infinite());
    let mut second = PolicyAnalyzer::new(Domains::infinite());
    let id = first.add_rule(&rule).unwrap();
    second.add_rule(&rule).unwrap();
    assert_eq!(first.covered(id, &[id]).unwrap(), Inclusion::Holds);
    assert!(matches!(
        second.covered(id, &[]),
        Err(HistoryError::UnknownId {
            domain: "rule",
            id: 0
        })
    ));
    assert!(matches!(
        first.redundant(RuleId(1, id.1), &[id]),
        Err(HistoryError::UnknownId {
            domain: "rule",
            id: 1
        })
    ));
}
