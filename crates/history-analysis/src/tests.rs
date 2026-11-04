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

use crate::constraint::{Atom, Constraint, Operand, Universes, steps};
use crate::{
    Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, SearchOptions, Value,
};

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
const NET: u32 = 20;

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
    match analyzer
        .tail_included(&head(), left, right)
        .unwrap()
        .inclusion
    {
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
        Inclusion::Exhausted => panic!("no budget was set"),
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
    let verdict = analyzer.tail_included(&head(), &since, &once).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
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
    let verdict = analyzer.tail_included(&head(), &left, &right).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
    assert!(!included(&right, &left));
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
    let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
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

fn rule(mode: RuleMode, resource: Option<u32>, tail: RegexExpr<Access>) -> Rule<Access> {
    let resource = match resource {
        Some(value) => ComponentPattern::constant(value),
        None => ComponentPattern::variable("r"),
    };
    Rule::new(
        mode,
        Head::new(
            ComponentPattern::variable("p"),
            ComponentPattern::constant(Action::Edit),
            resource,
        ),
        tail,
    )
}

#[test]
fn a_forbid_all_rule_makes_a_narrower_rule_redundant_without_a_step() {
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let read = TestExpr::and([principal_is_p(), action_is(Comparison::Eq, Action::Read)]);
    let narrow = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some(NET), ever(read)))
        .unwrap();
    let broad = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some(NET), RegexExpr::all()))
        .unwrap();
    let verdict = analyzer.redundant(narrow, &[narrow, broad]).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
    assert!(!analyzer.redundant(broad, &[narrow, broad]).unwrap().holds());
}

#[test]
fn coverage_splits_on_the_head_constants_of_the_covering_rules() {
    let read = ever(action_is(Comparison::Eq, Action::Read));
    let any_resource = rule(RuleMode::Forbid, None, RegexExpr::all());
    let only_x = rule(RuleMode::Forbid, Some(X), RegexExpr::all());
    let after_read = rule(RuleMode::Forbid, None, read.clone());
    let without_read = rule(RuleMode::Require, None, read);

    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let target = analyzer.add_rule(&any_resource).unwrap();
    let ids = [&only_x, &after_read, &without_read].map(|rule| analyzer.add_rule(rule).unwrap());

    let verdict = analyzer.covered(target, &ids[..2]).unwrap();
    let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
        panic!("resources other than x without a read are not covered");
    };
    assert!(denied(
        core::slice::from_ref(&any_resource),
        &counterexample
    ));
    assert!(!denied(&[only_x, after_read], &counterexample));
    assert!(
        verdict.stats.searches >= 2,
        "κ_R = x and κ_R ≠ x are separate cases"
    );

    assert!(analyzer.covered(target, &ids).unwrap().holds());
    assert!(
        analyzer
            .at_least_as_strict(&ids, &[target])
            .unwrap()
            .holds()
    );
    // Every rule of `ids` denies a subset of what `target` denies.
    assert!(
        analyzer
            .at_least_as_strict(&[target], &ids)
            .unwrap()
            .holds()
    );
}

/// The document edits that the approval policy guards, and a secret.
const DOC: u32 = 30;
const SECRET: u32 = 31;

/// Forbid rules on edits of `DOC`: `H` once the principal has done anything but edit or stage,
/// which with the declared actions means read; for each program `i`, `S_i` while an edit of
/// `100 + i` by the principal awaits a stage of `200 + i`; and the narrower `H'` once the principal
/// has read `SECRET`. Returns `H'` and the policy, which holds it. Stated this way, `H` covers `H'`
/// only through the domain, which simulation does not see, so the search must step past the root.
fn approval_policy(analyzer: &mut PolicyAnalyzer<Access>, programs: u32) -> (RuleId, Vec<RuleId>) {
    let mut tails = Vec::from([ever(TestExpr::and([
        principal_is_p(),
        action_is(Comparison::Neq, Action::Edit),
        action_is(Comparison::Neq, Action::Stage),
    ]))]);
    for program in 0..programs {
        let edit = TestExpr::and([
            principal_is_p(),
            action_is(Comparison::Eq, Action::Edit),
            resource_is(Comparison::Eq, Some(100 + program)),
        ]);
        let unapproved = TestExpr::or([
            action_is(Comparison::Neq, Action::Stage),
            resource_is(Comparison::Neq, Some(200 + program)),
        ]);
        tails.push(RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(edit),
            RegexExpr::star(RegexExpr::test(unapproved)),
        ]));
    }
    tails.push(ever(TestExpr::and([
        principal_is_p(),
        action_is(Comparison::Eq, Action::Read),
        resource_is(Comparison::Eq, Some(SECRET)),
    ])));
    let policy = tails
        .into_iter()
        .map(|tail| {
            analyzer
                .add_rule(&rule(RuleMode::Forbid, Some(DOC), tail))
                .unwrap()
        })
        .collect::<Vec<_>>();
    (*policy.last().unwrap(), policy)
}

#[test]
fn a_policy_covers_its_own_rule_without_a_step() {
    // The rule's tail is among the pieces that the residual avoids, so the residual is dead.
    // Searched, it would track every set of pending approvals of the other rules.
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let (_, policy) = approval_policy(&mut analyzer, 12);
    let verdict = analyzer.covered(policy[1], &policy).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
}

#[test]
fn the_initial_state_subsumes_every_set_of_pending_approvals() {
    // A residual of `H' ∩ ¬(H ∪ S_0 ∪ …)` avoids the initial residual's pieces and, for each
    // pending approval, `η_i*`, so the initial state subsumes all of them: one expansion where
    // the search would otherwise expand one state per set of pending approvals.
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let (narrow, policy) = approval_policy(&mut analyzer, 12);
    let verdict = analyzer.redundant(narrow, &policy).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 1);
    assert!(verdict.stats.subsumed > 0);
}

#[test]
fn simulation_settles_a_narrower_rule_at_the_root() {
    // `P ≐ p ∧ A ≐ read ∧ R ≐ secret` implies `P ≐ p ∧ A ≐ read` by its conjuncts, so the narrow
    // tail lies below the broad one and the initial residual is dead.
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let reads = TestExpr::and([principal_is_p(), action_is(Comparison::Eq, Action::Read)]);
    let broad = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some(DOC), ever(reads.clone())))
        .unwrap();
    let secret = TestExpr::and([reads, resource_is(Comparison::Eq, Some(SECRET))]);
    let narrow = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some(DOC), ever(secret)))
        .unwrap();
    let verdict = analyzer.redundant(narrow, &[broad, narrow]).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
    assert!(!analyzer.redundant(broad, &[broad, narrow]).unwrap().holds());
}

#[test]
fn vacuity_distinguishes_rules_that_never_or_always_fire() {
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    let read = ever(action_is(Comparison::Eq, Action::Read));
    let never = analyzer
        .add_rule(&rule(
            RuleMode::Forbid,
            None,
            RegexExpr::intersect([read.clone(), RegexExpr::complement(read.clone())]),
        ))
        .unwrap();
    let always = analyzer
        .add_rule(&rule(RuleMode::Require, None, RegexExpr::empty()))
        .unwrap();
    let sometimes = analyzer
        .add_rule(&rule(RuleMode::Require, None, read))
        .unwrap();
    assert!(analyzer.never_fires(never).unwrap().holds());
    assert!(!analyzer.always_fires(never).unwrap().holds());
    assert!(analyzer.always_fires(always).unwrap().holds());
    assert!(!analyzer.never_fires(always).unwrap().holds());
    assert!(!analyzer.never_fires(sometimes).unwrap().holds());
    assert!(!analyzer.always_fires(sometimes).unwrap().holds());
}

#[test]
fn a_budget_stops_the_search() {
    let options = SearchOptions {
        max_items: Some(0),
        ..SearchOptions::default()
    };
    let mut analyzer = PolicyAnalyzer::with_options(finite_actions(), options);
    let verdict = analyzer
        .tail_included(
            &head(),
            &ever(action_is(Comparison::Eq, Action::Read)),
            &ever(principal_is_p()),
        )
        .unwrap();
    assert_eq!(verdict.inclusion, Inclusion::Exhausted);
}

#[test]
fn the_graph_budget_bounds_each_search() {
    // Both sides end in a read ten events back, but the right side tests its later events against
    // the declared actions instead of `⊤`. The sides are equal under the domain, yet no state is
    // dead or subsumed: the search tracks each pattern of reads among the last ten events, 2^10
    // states, more than the runtime's graph budget for one rule holds.
    let ten_back = |later: TestExpr<Access>| {
        let mut parts = Vec::from([
            RegexExpr::all(),
            RegexExpr::test(action_is(Comparison::Eq, Action::Read)),
        ]);
        parts.extend((0..10).map(|_| RegexExpr::test(later.clone())));
        RegexExpr::concat(parts)
    };
    let left = ten_back(TestExpr::True);
    let right = ten_back(TestExpr::or(
        ACTIONS.map(|action| action_is(Comparison::Eq, action)),
    ));
    let runtime_budget = SearchOptions {
        graph_bytes: junco_core::limits::MAX_GRAPH_BYTES,
        ..SearchOptions::default()
    };
    let mut analyzer = PolicyAnalyzer::with_options(finite_actions(), runtime_budget);
    let verdict = analyzer.tail_included(&head(), &left, &right).unwrap();
    assert_eq!(verdict.inclusion, Inclusion::Exhausted);
    let mut analyzer = PolicyAnalyzer::new(finite_actions());
    assert!(
        analyzer
            .tail_included(&head(), &left, &right)
            .unwrap()
            .holds()
    );
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
    let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
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
    assert!(verdict.holds(), "{verdict:?}");

    let mut analyzer = PolicyAnalyzer::new(Domains::infinite());
    let verdict = analyzer
        .tail_included(&head, &own_action, &by_case)
        .unwrap();
    let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
        panic!("an infinite action domain has a fourth action");
    };
    assert!(matches!(counterexample.candidate.action, Value::Fresh(_)));
    assert_eq!(
        counterexample.history[0].action,
        counterexample.candidate.action
    );
}

#[test]
fn a_head_constant_outside_a_declared_domain_matches_no_candidate() {
    let domains = Domains::infinite().with_actions([Action::Read, Action::Edit]);
    let staging = Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("p"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("r"),
        ),
        RegexExpr::all(),
    );
    let mut analyzer = PolicyAnalyzer::new(domains);
    let staging = analyzer.add_rule(&staging).unwrap();
    let editing = analyzer
        .add_rule(&rule(RuleMode::Forbid, None, RegexExpr::all()))
        .unwrap();
    assert!(analyzer.never_fires(staging).unwrap().holds());
    assert!(analyzer.covered(staging, &[]).unwrap().holds());
    assert!(!analyzer.covered(editing, &[staging]).unwrap().holds());
}
