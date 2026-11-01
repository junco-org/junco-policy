//! Inclusion decisions on small tails whose answers are known, with every counterexample replayed
//! through the runtime matcher.

use bumpalo::Bump;

use super::super::compile::compile_head_and_tail;
use super::super::node::RegexKind;
use super::super::store::CanonicalStore;
use super::constraint::{Constraint, steps};
use super::term::test_atoms;
use super::{Alphabet, Inclusion, PolicyAnalyzer, SearchOptions, Strategy, Subsumption};
use crate::policy::{PolicyDecision, TracePolicy, TraceRule};
use crate::{
    Action, AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode,
    TestExpr,
};

fn head() -> Head {
    Head::new(
        ComponentPattern::variable("p"),
        ComponentPattern::constant(Action::Edit),
        ComponentPattern::variable("r"),
    )
}

fn principal_is_p() -> TestExpr {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("p")),
    )
}

fn action_is(action: Action) -> TestExpr {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

fn resource_is(comparison: Comparison, resource: Option<&str>) -> TestExpr {
    let pattern = match resource {
        Some(name) => ComponentPattern::constant([name]),
        None => ComponentPattern::variable("r"),
    };
    TestExpr::atom(comparison, AtomPattern::Resource(pattern))
}

fn ever(test: TestExpr) -> RegexExpr {
    RegexExpr::concat([RegexExpr::all(), RegexExpr::test(test), RegexExpr::all()])
}

/// Every search configuration, so that each test checks that all of them agree. The simple
/// strategy ignores subsumption and pruning, so it varies only its alphabet.
fn configurations() -> Vec<SearchOptions> {
    let mut all = Vec::new();
    for strategy in [
        Strategy::Residual,
        Strategy::Antichain,
        Strategy::Brzozowski,
    ] {
        for subsumption in [Subsumption::Identity, Subsumption::Implication] {
            for prune_visited in [false, true] {
                for alphabet in [Alphabet::Letters, Alphabet::Minterms] {
                    all.push(SearchOptions {
                        strategy,
                        subsumption,
                        prune_visited,
                        alphabet,
                        max_items: None,
                    });
                }
            }
        }
    }
    for alphabet in [Alphabet::Letters, Alphabet::Minterms] {
        all.push(SearchOptions {
            strategy: Strategy::Simple,
            alphabet,
            ..SearchOptions::default()
        });
    }
    all
}

/// Whether `head` matches `candidate` and `history` is in `tail`, by the runtime matcher.
fn in_tail(head: &Head, tail: &RegexExpr, candidate: &Event, history: &[Event]) -> bool {
    let arena = Bump::new();
    let rule = TraceRule::new(
        Rule::new(RuleMode::Forbid, head.clone(), tail.clone()),
        |_| (String::new(), Vec::new()),
    );
    let mut policy = TracePolicy::new(&arena, [rule]).expect("test tails compile");
    policy.decide(history, candidate) != PolicyDecision::Grant
}

/// Decides `left ⊑ right` under every configuration, checks that they agree, replays every
/// counterexample, and returns whether the inclusion holds.
fn included(left: &RegexExpr, right: &RegexExpr) -> bool {
    let head = head();
    let mut verdicts = Vec::new();
    for options in configurations() {
        let arena = Bump::new();
        let mut analyzer = PolicyAnalyzer::with_options(&arena, options);
        let verdict = analyzer
            .tail_included(&head, left, right)
            .expect("test tails compile");
        match verdict.inclusion {
            Inclusion::Holds => verdicts.push(true),
            Inclusion::Counterexample(counterexample) => {
                assert!(
                    in_tail(
                        &head,
                        left,
                        &counterexample.candidate,
                        &counterexample.history
                    ),
                    "{options:?}: counterexample {counterexample:?} is not in the left tail"
                );
                assert!(
                    !in_tail(
                        &head,
                        right,
                        &counterexample.candidate,
                        &counterexample.history
                    ),
                    "{options:?}: counterexample {counterexample:?} is in the right tail"
                );
                verdicts.push(false);
            }
            Inclusion::Exhausted => panic!("no budget was set"),
        }
    }
    assert!(
        verdicts.windows(2).all(|pair| pair[0] == pair[1]),
        "configurations disagree: {verdicts:?}"
    );
    verdicts[0]
}

#[test]
fn since_is_included_in_once_but_not_conversely() {
    let since = RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(action_is(Action::Read)),
        RegexExpr::star(RegexExpr::test(principal_is_p())),
    ]);
    let once = ever(action_is(Action::Read));
    assert!(included(&since, &once));
    assert!(!included(&once, &since));
}

#[test]
fn simple_derivatives_prove_since_in_once_with_one_expansion() {
    // On a read, the left side becomes `since ∪ p*` and the right side `Σ*`, so the difference is
    // empty; on any other event both sides are unchanged and the state repeats.
    let since = RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(action_is(Action::Read)),
        RegexExpr::star(RegexExpr::test(principal_is_p())),
    ]);
    let once = ever(action_is(Action::Read));
    let arena = Bump::new();
    let mut analyzer = PolicyAnalyzer::with_options(
        &arena,
        SearchOptions {
            strategy: Strategy::Simple,
            ..SearchOptions::default()
        },
    );
    let verdict = analyzer.tail_included(&head(), &since, &once).unwrap();
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 1);
}

#[test]
fn register_comparisons_split_on_the_constants_they_meet() {
    // Under κ_R = x, `R ≐ κ_R` is `R ≐ x`; otherwise it is `R ≐ κ_R ∧ R ≠ x`.
    let own = ever(resource_is(Comparison::Eq, None));
    let by_case = RegexExpr::union([
        ever(resource_is(Comparison::Eq, Some("x"))),
        ever(TestExpr::and([
            resource_is(Comparison::Neq, Some("x")),
            resource_is(Comparison::Eq, None),
        ])),
    ]);
    assert!(included(&own, &by_case));
    assert!(!included(
        &own,
        &ever(resource_is(Comparison::Eq, Some("x")))
    ));
}

#[test]
fn complements_are_compared_without_determinising_them() {
    let read = action_is(Action::Read);
    let own_read = TestExpr::and([read.clone(), principal_is_p()]);
    let never_read = RegexExpr::complement(ever(read));
    let never_own_read = RegexExpr::complement(ever(own_read));
    assert!(included(&never_read, &never_own_read));
    assert!(!included(&never_own_read, &never_read));
}

#[test]
fn intersections_on_either_side_are_unfolded() {
    let read = ever(action_is(Action::Read));
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
    let ends_in =
        |action| RegexExpr::concat([RegexExpr::all(), RegexExpr::test(action_is(action))]);
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
fn breadth_first_counterexamples_are_shortest() {
    // Histories ending in a read, against histories of length at least two: the read alone is
    // the unique shortest counterexample.
    let ends_in_read =
        RegexExpr::concat([RegexExpr::all(), RegexExpr::test(action_is(Action::Read))]);
    let at_least_two = RegexExpr::concat([
        RegexExpr::test(TestExpr::true_test()),
        RegexExpr::test(TestExpr::true_test()),
        RegexExpr::all(),
    ]);
    for options in configurations()
        .into_iter()
        .filter(|options| !options.prune_visited)
    {
        let arena = Bump::new();
        let mut analyzer = PolicyAnalyzer::with_options(&arena, options);
        let verdict = analyzer
            .tail_included(&head(), &ends_in_read, &at_least_two)
            .unwrap();
        let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
            panic!("{options:?}: inclusion must fail");
        };
        assert_eq!(counterexample.history.len(), 1, "{options:?}");
    }
}

/// Atoms of the test tail of a compiled one-test rule.
fn compiled_atoms<'arena>(
    store: &mut CanonicalStore<'arena>,
    test: TestExpr,
) -> Vec<super::super::component::CompiledAtomPattern<'arena>> {
    let rule = Rule::new(RuleMode::Forbid, head(), RegexExpr::test(test));
    let (_, tail) = compile_head_and_tail(store, &rule).unwrap();
    let RegexKind::Test(test) = tail.get().kind else {
        panic!("a nonconstant test compiles to a test regex");
    };
    let mut atoms = Vec::new();
    test_atoms(test, &mut atoms);
    atoms
}

#[test]
fn a_register_and_a_constant_give_five_steps_by_either_alphabet() {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);
    let atoms = compiled_atoms(
        &mut store,
        TestExpr::or([
            resource_is(Comparison::Eq, None),
            resource_is(Comparison::Eq, Some("k")),
        ]),
    );
    let letters = steps(&Constraint::unconstrained(), &atoms, Alphabet::Letters);
    let mut counts = letters
        .iter()
        .map(|(_, letters)| letters.len())
        .collect::<Vec<_>>();
    counts.sort_unstable();
    assert_eq!(counts, [2, 3], "κ_R = k gives two letters, κ_R ≠ k three");
    let minterms = steps(&Constraint::unconstrained(), &atoms, Alphabet::Minterms);
    for ((constraint, letters), (other_constraint, other_letters)) in letters.iter().zip(&minterms)
    {
        assert_eq!(constraint, other_constraint);
        let mut letters = letters.clone();
        let mut other_letters = other_letters.clone();
        let key = |letter: &super::constraint::Letter<'_>| format!("{letter:?}");
        letters.sort_by_key(key);
        other_letters.sort_by_key(key);
        assert_eq!(letters, other_letters);
    }
}

fn rule(mode: RuleMode, resource: Option<&str>, tail: RegexExpr) -> Rule {
    let resource = match resource {
        Some(name) => ComponentPattern::constant([name]),
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

/// Whether some rule of `rules` denies `candidate` after `history`, by the runtime matcher.
fn denied(rules: &[&Rule], candidate: &Event, history: &[Event]) -> bool {
    let arena = Bump::new();
    let rules = rules
        .iter()
        .map(|rule| TraceRule::new((*rule).clone(), |_| (String::new(), Vec::new())));
    let mut policy = TracePolicy::new(&arena, rules).unwrap();
    policy.decide(history, candidate) != PolicyDecision::Grant
}

#[test]
fn a_forbid_all_rule_makes_a_narrower_rule_redundant_without_a_step() {
    let arena = Bump::new();
    let mut analyzer = PolicyAnalyzer::new(&arena);
    let read = TestExpr::and([principal_is_p(), action_is(Action::Read)]);
    let narrow = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some("net"), ever(read)))
        .unwrap();
    let broad = analyzer
        .add_rule(&rule(RuleMode::Forbid, Some("net"), RegexExpr::all()))
        .unwrap();
    let verdict = analyzer.redundant(narrow, &[narrow, broad]);
    assert!(verdict.holds());
    assert_eq!(verdict.stats.expanded, 0);
    assert!(!analyzer.redundant(broad, &[narrow, broad]).holds());
}

#[test]
fn coverage_splits_on_the_head_constants_of_the_covering_rules() {
    let read = ever(action_is(Action::Read));
    let any_resource = rule(RuleMode::Forbid, None, RegexExpr::all());
    let only_a = rule(RuleMode::Forbid, Some("a"), RegexExpr::all());
    let after_read = rule(RuleMode::Forbid, None, read.clone());
    let without_read = rule(RuleMode::Require, None, read);

    let arena = Bump::new();
    let mut analyzer = PolicyAnalyzer::new(&arena);
    let target = analyzer.add_rule(&any_resource).unwrap();
    let ids = [&only_a, &after_read, &without_read].map(|rule| analyzer.add_rule(rule).unwrap());

    let verdict = analyzer.covered(target, &ids[..2]);
    let Inclusion::Counterexample(counterexample) = verdict.inclusion else {
        panic!("resources other than `a` without a read are not covered");
    };
    assert!(denied(
        &[&any_resource],
        &counterexample.candidate,
        &counterexample.history
    ));
    assert!(!denied(
        &[&only_a, &after_read],
        &counterexample.candidate,
        &counterexample.history
    ));
    assert!(
        verdict.stats.searches >= 2,
        "κ_R = a and κ_R ≠ a are separate cases"
    );

    assert!(analyzer.covered(target, &ids).holds());
    assert!(analyzer.at_least_as_strict(&ids, &[target]).holds());
    // Every rule of `ids` denies a subset of what `target` denies.
    assert!(analyzer.at_least_as_strict(&[target], &ids).holds());
}

#[test]
fn vacuity_distinguishes_rules_that_never_or_always_fire() {
    let arena = Bump::new();
    let mut analyzer = PolicyAnalyzer::new(&arena);
    let read = ever(action_is(Action::Read));
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
    assert!(analyzer.never_fires(never).holds());
    assert!(!analyzer.always_fires(never).holds());
    assert!(analyzer.always_fires(always).holds());
    assert!(!analyzer.never_fires(always).holds());
    assert!(!analyzer.never_fires(sometimes).holds());
    assert!(!analyzer.always_fires(sometimes).holds());
}

#[test]
fn a_budget_stops_the_search() {
    let arena = Bump::new();
    let mut analyzer = PolicyAnalyzer::with_options(
        &arena,
        SearchOptions {
            max_items: Some(0),
            ..SearchOptions::default()
        },
    );
    let verdict = analyzer
        .tail_included(
            &head(),
            &ever(action_is(Action::Read)),
            &ever(principal_is_p()),
        )
        .unwrap();
    assert_eq!(verdict.inclusion, Inclusion::Exhausted);
}
