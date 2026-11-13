//! Differential tests of tail inclusion and policy queries against a source interpreter.
//!
//! Brute force visits bounded histories over finite event domains, merging events only when
//! every source atom has the same value on them. Returned witnesses are checked against both
//! the interpreter and the runtime, with every admissible decoding in the small test domains.
//! Each randomized campaign has its own fixed seed and analyzer instances.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use history_analysis::{
    Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, Value,
};
use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, Component, Component2, ComponentPattern, Event, Head, N3, RegexExpr,
    Rule, RuleMode, TestExpr,
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

/// The one resource constant tails mention. No tail mentions a principal constant, so candidate
/// principal 1 stands for every principal.
const MENTIONED: u32 = 10;

/// Random tail pairs of each kind.
const CASES: usize = 150;

/// Most histories the brute force visits per set of letters.
const BUDGET: usize = 2_000;

#[test]
fn inclusion_agrees_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0001);
    for _ in 0..CASES {
        let setup = Setup::random(&mut rng);
        let tail = setup.regex(&mut rng, 3);
        // Independent tails mostly part after a short history, a mutant agrees with the original
        // on more histories, and a rewrite has the same language.
        check(&setup, &tail, &setup.regex(&mut rng, 3));
        check(&setup, &tail, &setup.mutate(&mut rng, &tail));
        let rewritten = rewrite(&mut rng, &tail);
        assert_eq!(
            check(&setup, &tail, &rewritten),
            [true; 2],
            "{tail:?} and its rewrite {rewritten:?} differ"
        );
    }
}

/// All components are declared, so each returned symbolic witness has exactly one admissible
/// decoding. Unlike the tail campaign, policies vary their heads as well as their modes.
#[test]
fn policy_queries_agree_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0002);
    let setup = policy_setup();
    for case in 0..48 {
        let rules = (0..4)
            .map(|index| {
                let mut source = policy_setup();
                source.principal_register = rng.below(2) == 0;
                source.action_register = rng.below(2) == 0;
                source.resource_register = rng.below(2) == 0;
                source.head = Head::new([
                    if source.principal_register {
                        ComponentPattern::variable("p")
                    } else {
                        ComponentPattern::constant(AccessComponent::Principal(
                            1 + rng.below(2) as u32,
                        ))
                    },
                    if source.action_register {
                        ComponentPattern::variable("a")
                    } else {
                        ComponentPattern::constant(AccessComponent::Action(
                            ACTIONS[rng.below(ACTIONS.len())],
                        ))
                    },
                    if source.resource_register {
                        ComponentPattern::variable("r")
                    } else {
                        ComponentPattern::constant(AccessComponent::Resource(
                            MENTIONED + rng.below(2) as u32,
                        ))
                    },
                ]);
                let mode = if case >> index & 1 == 0 {
                    RuleMode::Forbid
                } else {
                    RuleMode::Require
                };
                Rule::new(mode, source.head.clone(), source.regex(&mut rng, 2))
            })
            .collect::<Vec<_>>();
        let mut analyzer = PolicyAnalyzer::new(setup.domains.clone());
        let ids = rules
            .iter()
            .map(|rule| analyzer.add_rule(rule).unwrap())
            .collect::<Vec<_>>();
        let p = [ids[0], ids[1]];
        let q = [ids[2], ids[3]];
        check_policy(
            &setup,
            &rules,
            &[0, 1],
            &[2],
            analyzer.covered(ids[2], &p).unwrap(),
        );
        check_policy(
            &setup,
            &rules,
            &[0, 1],
            &[2, 3],
            analyzer.at_least_as_strict(&p, &q).unwrap(),
        );
        check_policy(
            &setup,
            &rules,
            &[2, 3],
            &[0, 1],
            analyzer.at_least_as_strict(&q, &p).unwrap(),
        );
        // Removing a redundant rule removes every occurrence, not just the first.
        check_policy(
            &setup,
            &rules,
            &[0, 1],
            &[2],
            analyzer
                .redundant(ids[2], &[ids[2], ids[0], ids[2], ids[1]])
                .unwrap(),
        );
        assert!(check_policy(
            &setup,
            &rules,
            &[0, 1],
            &[0, 1],
            analyzer.at_least_as_strict(&p, &p).unwrap(),
        ));
        assert!(check_policy(
            &setup,
            &rules,
            &[2],
            &[2],
            analyzer.covered(ids[2], &[ids[2], ids[2]]).unwrap(),
        ));
        check_policy(
            &setup,
            &rules,
            &[],
            &[2],
            analyzer.redundant(ids[2], &[ids[2], ids[2]]).unwrap(),
        );
        check_policy(
            &setup,
            &rules,
            &[],
            &[2],
            analyzer.covered(ids[2], &[]).unwrap(),
        );
        assert!(check_policy(
            &setup,
            &rules,
            &[],
            &[],
            analyzer.at_least_as_strict(&[], &[]).unwrap(),
        ));
    }
}

#[test]
fn complementary_modes_and_disjoint_heads_cover() {
    let setup = policy_setup();
    let read = RegexExpr::Test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::new(
            Component(1),
            ComponentPattern::constant(AccessComponent::Action(Action::Read)),
        ),
    ));
    let mut rules = vec![
        Rule::new(RuleMode::Forbid, setup.head.clone(), RegexExpr::All),
        Rule::new(RuleMode::Forbid, setup.head.clone(), read.clone()),
        Rule::new(RuleMode::Require, setup.head.clone(), read),
    ];
    // Finite domains let these three disjoint heads cover the unrestricted head.
    for principal in [1, 2, 3] {
        let mut head = setup.head.clone();
        head.0[0] = ComponentPattern::constant(AccessComponent::Principal(principal));
        rules.push(Rule::new(RuleMode::Forbid, head, RegexExpr::All));
    }
    // A head outside the declared domain never fires, even when Require(Empty) would deny.
    let mut impossible = setup.head.clone();
    impossible.0[0] = ComponentPattern::constant(AccessComponent::Principal(99));
    rules.push(Rule::new(RuleMode::Require, impossible, RegexExpr::Empty));
    let mut analyzer = PolicyAnalyzer::new(setup.domains.clone());
    let ids = rules
        .iter()
        .map(|rule| analyzer.add_rule(rule).unwrap())
        .collect::<Vec<_>>();
    assert!(check_policy(
        &setup,
        &rules,
        &[1, 2],
        &[0],
        analyzer.covered(ids[0], &ids[1..3]).unwrap(),
    ));
    assert!(check_policy(
        &setup,
        &rules,
        &[3, 4, 5],
        &[0],
        analyzer.covered(ids[0], &ids[3..6]).unwrap(),
    ));
    assert!(check_policy(
        &setup,
        &rules,
        &[],
        &[6],
        analyzer.covered(ids[6], &[]).unwrap(),
    ));
    assert!(check_policy(
        &setup,
        &rules,
        &[1, 2],
        &[0, 6],
        analyzer
            .at_least_as_strict(&ids[1..3], &[ids[0], ids[6]])
            .unwrap(),
    ));
}

/// Splitting only on the left rule's head misses Bob: Alice is covered by R1, but Bob needs R2.
/// Run with both a declared principal domain and unrestricted principals. In the latter case,
/// check every admissible assignment of fresh principals in the small domain {Alice, Bob, Carol}.
#[test]
fn alice_bob_coverage_regression() {
    const ALICE: u32 = 1;
    const BOB: u32 = 2;
    for finite in [true, false] {
        for history_in_r2 in [false, true] {
            let mut setup = policy_setup();
            if !finite {
                setup.domains = Domains::infinite()
                    .with_domain(Component(1), &ACTIONS.map(AccessComponent::Action))
                    .expect("domain")
                    .with_domain(
                        Component(2),
                        &[MENTIONED, MENTIONED + 1].map(AccessComponent::Resource),
                    )
                    .expect("domain");
                setup.principal_domain = None;
            }
            let head = Head::new([
                ComponentPattern::variable("p"),
                ComponentPattern::constant(AccessComponent::Action(Action::Edit)),
                ComponentPattern::variable("r"),
            ]);
            let r = RegexExpr::Test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::new(
                    Component(1),
                    ComponentPattern::constant(AccessComponent::Action(Action::Read)),
                ),
            ));
            let rules = vec![
                Rule::new(RuleMode::Forbid, head.clone(), r.clone()),
                Rule::new(
                    RuleMode::Forbid,
                    Head::new([
                        ComponentPattern::constant(AccessComponent::Principal(ALICE)),
                        ComponentPattern::constant(AccessComponent::Action(Action::Edit)),
                        ComponentPattern::variable("r"),
                    ]),
                    r.clone(),
                ),
                Rule::new(
                    RuleMode::Forbid,
                    head,
                    if history_in_r2 { r } else { RegexExpr::Empty },
                ),
            ];
            let mut analyzer = PolicyAnalyzer::new(setup.domains.clone());
            let ids = rules
                .iter()
                .map(|rule| analyzer.add_rule(rule).unwrap())
                .collect::<Vec<_>>();
            let verdict = analyzer.covered(ids[0], &ids[1..]).unwrap();
            if let Inclusion::Counterexample(witness) = &verdict {
                let instances = policy_instances(&setup, witness);
                assert!(
                    instances
                        .iter()
                        .all(|(candidate, _)| candidate.principal != ALICE)
                );
                assert!(
                    instances
                        .iter()
                        .any(|(candidate, _)| candidate.principal == BOB)
                );
                assert!(instances.iter().all(|(_, history)| history.len() == 1));
            }
            assert_eq!(
                check_policy(&setup, &rules, &[1, 2], &[0], verdict),
                history_in_r2,
            );
            assert_eq!(
                check_policy(
                    &setup,
                    &rules,
                    &[1, 2],
                    &[0],
                    analyzer.at_least_as_strict(&ids[1..], &ids[..1]).unwrap(),
                ),
                history_in_r2,
            );
        }
    }
}

fn policy_setup() -> Setup {
    let mut setup = Setup {
        head: Head::new([
            ComponentPattern::variable("p"),
            ComponentPattern::variable("a"),
            ComponentPattern::variable("r"),
        ]),
        domains: Domains::infinite()
            .with_domain(Component(0), &[1, 2, 3].map(AccessComponent::Principal))
            .expect("domain")
            .with_domain(Component(1), &ACTIONS.map(AccessComponent::Action))
            .expect("domain")
            .with_domain(
                Component(2),
                &[MENTIONED, MENTIONED + 1].map(AccessComponent::Resource),
            )
            .expect("domain"),
        principal_register: true,
        action_register: true,
        resource_register: true,
        principal_domain: Some(vec![1, 2, 3]),
        resource_domain: Some(vec![MENTIONED, MENTIONED + 1]),
        candidates: Vec::new(),
    };
    setup.candidates = setup.events().collect();
    setup
}

fn head_matches(head: &Head<Access>, candidate: Access) -> bool {
    fn matches<T: PartialEq>(pattern: &ComponentPattern<T>, value: T) -> bool {
        match pattern {
            ComponentPattern::Constant(constant) => *constant == value,
            ComponentPattern::Variable(_) => true,
        }
    }
    head.0
        .iter()
        .enumerate()
        .all(|(index, pattern)| matches(pattern, candidate.component(index)))
}

/// The complete denial language at a fixed candidate, including mode and head matching.
fn denials(rules: &[Rule<Access>], policy: &[usize], candidate: Access) -> RegexExpr<Access> {
    RegexExpr::Union(
        policy
            .iter()
            .filter_map(|&index| {
                let rule = &rules[index];
                head_matches(&rule.head, candidate).then(|| match rule.mode {
                    RuleMode::Forbid => rule.tail.clone(),
                    RuleMode::Require => RegexExpr::Not(Box::new(rule.tail.clone())),
                })
            })
            .collect(),
    )
}

fn runtime_denies(
    rules: &[Rule<Access>],
    policy: &[usize],
    history: &[Access],
    candidate: Access,
) -> bool {
    let store = Arc::new(Store::new().unwrap());
    let rules = policy
        .iter()
        .map(|&index| TraceRule::new(rules[index].clone(), |_| (String::new(), Vec::new())))
        .collect::<Vec<_>>();
    let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
    let history = History::from_events(store, history.iter().copied()).unwrap();
    policy.decide(&history, &candidate).unwrap() != PolicyDecision::Grant
}

/// Check P ⊑ Q, equivalently that P covers every rule of Q. This deliberately does not assert
/// global shortestness: policy queries return the first failing head case/rule, not the shortest.
fn check_policy(
    setup: &Setup,
    rules: &[Rule<Access>],
    p: &[usize],
    q: &[usize],
    verdict: Inclusion<Access>,
) -> bool {
    let brute = setup
        .candidates
        .iter()
        .map(|&candidate| {
            let tails = [denials(rules, q, candidate), denials(rules, p, candidate)];
            let mut interpreter = Interpreter::default();
            let roots = tails.each_ref().map(|tail| interpreter.add(tail));
            let letters = interpreter.letters(setup, candidate);
            let bound = bound(letters.len());
            (
                candidate,
                bound,
                interpreter.shortest(roots, &letters, bound)[0],
            )
        })
        .collect::<Vec<_>>();
    let context = || format!("P={p:?}, Q={q:?}, rules={rules:?}, setup={setup:?}");
    match verdict {
        Inclusion::Holds => {
            assert!(
                brute.iter().all(|(_, _, shortest)| shortest.is_none()),
                "holds despite a bounded failing history: {brute:?}; {}",
                context(),
            );
            true
        }
        Inclusion::Counterexample(witness) => {
            let instances = policy_instances(setup, &witness);
            assert!(
                !instances.is_empty(),
                "no admissible small-domain instance: {witness:?}"
            );
            for (candidate, history) in instances {
                let tails = [denials(rules, q, candidate), denials(rules, p, candidate)];
                let mut interpreter = Interpreter::default();
                let roots = tails.each_ref().map(|tail| interpreter.add(tail));
                assert!(
                    interpreter.accepts(roots[0], &history, candidate)
                        && !interpreter.accepts(roots[1], &history, candidate),
                    "source interpreter rejects {witness:?}, decoded as {candidate:?}/{history:?}: {}",
                    context(),
                );
                assert!(
                    runtime_denies(rules, q, &history, candidate)
                        && !runtime_denies(rules, p, &history, candidate),
                    "runtime rejects {witness:?}, decoded as {candidate:?}/{history:?}: {}",
                    context(),
                );
                let (_, bound, shortest) = brute
                    .iter()
                    .find(|(searched, _, _)| *searched == candidate)
                    .expect("every decoded candidate is enumerated");
                if history.len() <= *bound {
                    assert!(
                        shortest.is_some_and(|length| length <= history.len()),
                        "brute force misses {witness:?}: {}",
                        context(),
                    );
                }
            }
            false
        }
        Inclusion::Exhausted => panic!("policy search exhausted: {}", context()),
    }
}

/// Declared components must decode to declared constants. Only the unrestricted regression
/// uses fresh principals; Alice is its only known principal, so enumerate all injective choices
/// for its fresh numbers from {Bob, Carol}, shared consistently by candidate and history.
fn policy_instances(setup: &Setup, witness: &Counterexample<Access>) -> Vec<(Access, Vec<Access>)> {
    if setup.principal_domain.is_some() {
        return vec![(
            setup.concrete(&witness.candidate),
            witness
                .history
                .iter()
                .map(|event| setup.concrete(event))
                .collect(),
        )];
    }
    let mut fresh = Vec::new();
    for event in std::iter::once(&witness.candidate).chain(&witness.history) {
        if let Value::Fresh(number) = event.values[0]
            && !fresh.contains(&number)
        {
            fresh.push(number);
        }
    }
    fn assignments(
        fresh: &[usize],
        current: &mut HashMap<usize, u32>,
        result: &mut Vec<HashMap<usize, u32>>,
    ) {
        let Some((&number, rest)) = fresh.split_first() else {
            result.push(current.clone());
            return;
        };
        for value in [2, 3] {
            if !current.values().any(|&used| used == value) {
                current.insert(number, value);
                assignments(rest, current, result);
                current.remove(&number);
            }
        }
    }
    let mut choices = Vec::new();
    assignments(&fresh, &mut HashMap::new(), &mut choices);
    choices
        .into_iter()
        .map(|choice| {
            let decode = |event: &Components<Access>| {
                let mut event = event.clone();
                if let Value::Fresh(number) = event.values[0] {
                    event.values[0] = Value::Constant(AccessComponent::Principal(choice[&number]));
                }
                setup.concrete(&event)
            };
            (
                decode(&witness.candidate),
                witness.history.iter().map(decode).collect(),
            )
        })
        .collect()
}

/// Decides `left ⊑ right` and `right ⊑ left` under `setup`, checks both verdicts against brute
/// force, and returns whether each holds.
fn check(setup: &Setup, left: &RegexExpr<Access>, right: &RegexExpr<Access>) -> [bool; 2] {
    let tails = [left, right];
    let mut interpreter = Interpreter::default();
    let roots = tails.map(|tail| interpreter.add(tail));
    // Per candidate, the length bound and, per direction, the shortest history within it in one
    // tail and not the other. Both depend on the candidate only through its letters.
    let mut searched = HashMap::new();
    let brute = setup
        .candidates
        .iter()
        .map(|&candidate| {
            let mut letters = interpreter.letters(setup, candidate);
            letters.sort_unstable();
            let (bound, shortest) = *searched.entry(letters).or_insert_with_key(|letters| {
                let bound = bound(letters.len());
                (bound, interpreter.shortest(roots, letters, bound))
            });
            (candidate, bound, shortest)
        })
        .collect::<Vec<_>>();

    [0, 1].map(|direction| {
        let (smaller, larger) = (tails[direction], tails[1 - direction]);
        let mut analyzer = PolicyAnalyzer::new(setup.domains.clone());
        let verdict = analyzer
            .tail_included(&setup.head, smaller, larger)
            .unwrap();
        let context = || format!("{smaller:?}\n⊑ {larger:?}\nunder {setup:?}");
        match verdict {
            Inclusion::Holds => {
                for (candidate, _, shortest) in &brute {
                    assert!(
                        shortest[direction].is_none(),
                        "holds, but {candidate:?} fails after {:?} events: {}",
                        shortest[direction],
                        context()
                    );
                }
                true
            }
            Inclusion::Counterexample(counterexample) => {
                let candidate = setup.concrete(&counterexample.candidate);
                let history = counterexample
                    .history
                    .iter()
                    .map(|components| setup.concrete(components))
                    .collect::<Vec<_>>();
                assert!(
                    interpreter.accepts(roots[direction], &history, candidate)
                        && !interpreter.accepts(roots[1 - direction], &history, candidate),
                    "{counterexample:?} does not fail: {}",
                    context()
                );
                assert!(
                    setup.denied(smaller, &history, candidate)
                        && !setup.denied(larger, &history, candidate),
                    "the runtime disagrees on {counterexample:?}: {}",
                    context()
                );
                let length = history.len();
                for (candidate, _, shortest) in &brute {
                    assert!(
                        shortest[direction].is_none_or(|shortest| length <= shortest),
                        "{counterexample:?} is longer than a history failing for {candidate:?}: {}",
                        context()
                    );
                }
                if brute.iter().all(|(_, bound, _)| length <= *bound) {
                    assert!(
                        brute
                            .iter()
                            .any(|(_, _, shortest)| shortest[direction] == Some(length)),
                        "brute force misses {counterexample:?}: {}",
                        context()
                    );
                }
                false
            }
            Inclusion::Exhausted => panic!("the search exhausted its budget: {}", context()),
        }
    })
}

/// The longest history length whose histories over `letters` letters fit [`BUDGET`].
fn bound(letters: usize) -> usize {
    let (mut bound, mut histories, mut total) = (0, 1, 1);
    while bound < 8 {
        histories *= letters;
        if total + histories > BUDGET {
            break;
        }
        total += histories;
        bound += 1;
    }
    bound
}

/// SplitMix64 with a fixed seed, so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

/// A head, declared domains, and the concrete values the brute force ranges over.
#[derive(Debug)]
struct Setup {
    head: Head<Access>,
    domains: Domains<Access>,
    /// Whether the head binds the principal.
    principal_register: bool,
    /// Whether the head binds the action, so tails may compare actions with the candidate's.
    action_register: bool,
    /// Whether the head binds the resource, so tails may compare resources with the candidate's.
    resource_register: bool,
    principal_domain: Option<Vec<u32>>,
    resource_domain: Option<Vec<u32>>,
    /// Candidates that the head matches, one per way their components can compare with the
    /// constants and the declared values.
    candidates: Vec<Access>,
}

impl Setup {
    fn random(rng: &mut Rng) -> Self {
        let action_register = rng.below(2) == 0;
        let resource_register = rng.below(4) != 0;
        let principal_domain = [None, Some(vec![1, 2]), Some(vec![1])][rng.below(3)].clone();
        // The last domain leaves out the mentioned constant.
        let resource_domain = [
            None,
            Some(vec![MENTIONED, 11]),
            Some(vec![MENTIONED]),
            Some(vec![11, 12]),
        ][rng.below(4)]
        .clone();
        let mut domains = Domains::infinite()
            .with_domain(Component(1), &ACTIONS.map(AccessComponent::Action))
            .expect("domain");
        if let Some(values) = &principal_domain {
            let values: Vec<_> = values
                .iter()
                .copied()
                .map(AccessComponent::Principal)
                .collect();
            domains = domains.with_domain(Component(0), &values).expect("domain");
        }
        if let Some(values) = &resource_domain {
            let values: Vec<_> = values
                .iter()
                .copied()
                .map(AccessComponent::Resource)
                .collect();
            domains = domains.with_domain(Component(2), &values).expect("domain");
        }
        let head = Head::new([
            ComponentPattern::variable("p"),
            if action_register {
                ComponentPattern::variable("a")
            } else {
                ComponentPattern::constant(AccessComponent::Action(Action::Edit))
            },
            if resource_register {
                ComponentPattern::variable("r")
            } else {
                ComponentPattern::constant(AccessComponent::Resource(MENTIONED))
            },
        ]);
        let actions = if action_register {
            ACTIONS.to_vec()
        } else {
            vec![Action::Edit]
        };
        let resources = resource_domain
            .clone()
            .unwrap_or_else(|| vec![MENTIONED, 11])
            .into_iter()
            .filter(|resource| resource_register || *resource == MENTIONED)
            .collect::<Vec<_>>();
        let candidates = actions
            .iter()
            .flat_map(|&action| {
                resources.iter().map(move |&resource| Access {
                    principal: 1,
                    action,
                    resource,
                })
            })
            .collect();
        Self {
            head,
            domains,
            principal_register: true,
            action_register,
            resource_register,
            principal_domain,
            resource_domain,
            candidates,
        }
    }

    /// Every concrete event the brute force considers: each declared value of a finite
    /// component, and otherwise the constants, the candidates' values and one more.
    fn events(&self) -> impl Iterator<Item = Access> + '_ {
        let principals = self.principal_domain.clone().unwrap_or_else(|| vec![1, 2]);
        let resources = self
            .resource_domain
            .clone()
            .unwrap_or_else(|| vec![MENTIONED, 11, 12]);
        principals.into_iter().flat_map(move |principal| {
            let resources = resources.clone();
            ACTIONS.into_iter().flat_map(move |action| {
                resources.clone().into_iter().map(move |resource| Access {
                    principal,
                    action,
                    resource,
                })
            })
        })
    }

    fn test(&self, rng: &mut Rng, depth: usize) -> TestExpr<Access> {
        if depth > 0 && rng.below(3) == 0 {
            let children = vec![self.test(rng, depth - 1), self.test(rng, depth - 1)];
            return if rng.below(2) == 0 {
                TestExpr::And(children)
            } else {
                TestExpr::Or(children)
            };
        }
        let pattern = match rng.below(6) {
            0 if self.principal_register => {
                AtomPattern::new(Component(0), ComponentPattern::variable("p"))
            }
            0 => AtomPattern::new(
                Component(0),
                ComponentPattern::constant(AccessComponent::Principal(1)),
            ),
            1 if self.action_register => {
                AtomPattern::new(Component(1), ComponentPattern::variable("a"))
            }
            1 | 2 => AtomPattern::new(
                Component(1),
                ComponentPattern::constant(AccessComponent::Action(
                    [Action::Read, Action::Edit][rng.below(2)],
                )),
            ),
            3 if self.resource_register => {
                AtomPattern::new(Component(2), ComponentPattern::variable("r"))
            }
            3 | 4 => AtomPattern::new(
                Component(2),
                ComponentPattern::constant(AccessComponent::Resource(MENTIONED)),
            ),
            _ if rng.below(4) == 0 => return TestExpr::False,
            _ => return TestExpr::True,
        };
        let comparison = if rng.below(3) == 0 {
            Comparison::Neq
        } else {
            Comparison::Eq
        };
        TestExpr::atom(comparison, pattern)
    }

    fn regex(&self, rng: &mut Rng, depth: usize) -> RegexExpr<Access> {
        if depth == 0 || rng.below(4) == 0 {
            let test = |rng: &mut Rng| RegexExpr::Test(self.test(rng, 1));
            return match rng.below(20) {
                0 => RegexExpr::Empty,
                1 | 2 => RegexExpr::Epsilon,
                3 | 4 => RegexExpr::All,
                5..=7 => RegexExpr::Star(Box::new(test(rng))),
                // `Σ*·t·Σ*` and `Σ*·t·s*`, the shapes of "ever" and "since".
                8..=10 => RegexExpr::Concat(vec![RegexExpr::All, test(rng), RegexExpr::All]),
                11..=13 => RegexExpr::Concat(vec![
                    RegexExpr::All,
                    test(rng),
                    RegexExpr::Star(Box::new(test(rng))),
                ]),
                _ => test(rng),
            };
        }
        let child = |rng: &mut Rng| self.regex(rng, depth - 1);
        match rng.below(5) {
            0 => RegexExpr::Union(vec![child(rng), child(rng)]),
            1 => RegexExpr::Intersect(vec![child(rng), child(rng)]),
            2 => {
                let count = 2 + rng.below(2);
                RegexExpr::Concat((0..count).map(|_| child(rng)).collect())
            }
            3 => RegexExpr::Star(Box::new(child(rng))),
            _ => RegexExpr::Not(Box::new(child(rng))),
        }
    }

    /// Changes one random subexpression of `regex` slightly, or replaces it.
    fn mutate(&self, rng: &mut Rng, regex: &RegexExpr<Access>) -> RegexExpr<Access> {
        let mut regex = regex.clone();
        match &mut regex {
            RegexExpr::Union(children)
            | RegexExpr::Intersect(children)
            | RegexExpr::Concat(children)
                if !children.is_empty() && rng.below(3) != 0 =>
            {
                let index = rng.below(children.len());
                children[index] = self.mutate(rng, &children[index]);
                return regex;
            }
            RegexExpr::Star(child) | RegexExpr::Not(child) if rng.below(3) != 0 => {
                **child = self.mutate(rng, child);
                return regex;
            }
            _ => {}
        }
        if rng.below(4) == 0 {
            return self.regex(rng, 2);
        }
        match regex {
            RegexExpr::Test(test) => RegexExpr::Test(self.mutate_test(rng, test)),
            RegexExpr::Union(children) => RegexExpr::Intersect(children),
            RegexExpr::Intersect(children) => RegexExpr::Union(children),
            RegexExpr::Concat(mut children) if children.len() > 1 => {
                let index = rng.below(children.len() - 1);
                if rng.below(2) == 0 {
                    children.remove(index);
                } else {
                    children.swap(index, index + 1);
                }
                RegexExpr::Concat(children)
            }
            RegexExpr::Star(child) if rng.below(2) == 0 => *child,
            RegexExpr::Star(child) => {
                RegexExpr::Concat(vec![(*child).clone(), RegexExpr::Star(child)])
            }
            RegexExpr::Not(child) => *child,
            _ => self.regex(rng, 2),
        }
    }

    /// Flips one comparison of `test`, or replaces one of its leaves.
    fn mutate_test(&self, rng: &mut Rng, test: TestExpr<Access>) -> TestExpr<Access> {
        match test {
            TestExpr::And(mut tests) if !tests.is_empty() => {
                let index = rng.below(tests.len());
                tests[index] = self.mutate_test(rng, tests[index].clone());
                TestExpr::And(tests)
            }
            TestExpr::Or(mut tests) if !tests.is_empty() => {
                let index = rng.below(tests.len());
                tests[index] = self.mutate_test(rng, tests[index].clone());
                TestExpr::Or(tests)
            }
            atom @ TestExpr::Atom { .. } if rng.below(2) == 0 => negate(&atom),
            _ => self.test(rng, 0),
        }
    }

    /// The concrete value of each component, checking it against the declared domains; fresh
    /// values are numbered above every constant.
    fn concrete(&self, components: &Components<Access>) -> Access {
        assert_eq!(components.values.len(), 3);
        let principal = match components.values[0] {
            Value::Constant(AccessComponent::Principal(value)) => Value::Constant(value),
            Value::Fresh(number) => Value::Fresh(number),
            _ => panic!("principal constant has the wrong coordinate"),
        };
        let Value::Constant(AccessComponent::Action(action)) = components.values[1] else {
            panic!("declared actions have no fresh values or other coordinates");
        };
        let resource = match components.values[2] {
            Value::Constant(AccessComponent::Resource(value)) => Value::Constant(value),
            Value::Fresh(number) => Value::Fresh(number),
            _ => panic!("resource constant has the wrong coordinate"),
        };
        Access {
            principal: concrete(principal, self.principal_domain.as_deref()),
            action,
            resource: concrete(resource, self.resource_domain.as_deref()),
        }
    }

    /// Whether the runtime denies `candidate` after `history` by the rule forbidding `tail`.
    fn denied(&self, tail: &RegexExpr<Access>, history: &[Access], candidate: Access) -> bool {
        let store = Arc::new(Store::new().unwrap());
        let rule = Rule::new(RuleMode::Forbid, self.head.clone(), tail.clone());
        let rules = [TraceRule::new(rule, |_| (String::new(), Vec::new()))];
        let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
        let history = History::from_events(store, history.iter().copied()).unwrap();
        policy.decide(&history, &candidate).unwrap() != PolicyDecision::Grant
    }
}

fn concrete(value: Value<u32>, domain: Option<&[u32]>) -> u32 {
    match (value, domain) {
        (Value::Constant(value), Some(domain)) => {
            assert!(domain.contains(&value), "{value} is not declared");
            value
        }
        (Value::Constant(value), None) => value,
        (Value::Fresh(_), Some(_)) => panic!("declared components have no fresh values"),
        (Value::Fresh(number), None) => 100 + u32::try_from(number).unwrap(),
    }
}

/// Rewrites random subexpressions of `regex` without changing its language.
fn rewrite(rng: &mut Rng, regex: &RegexExpr<Access>) -> RegexExpr<Access> {
    let mut children = |children: &[RegexExpr<Access>]| {
        children
            .iter()
            .map(|child| rewrite(rng, child))
            .collect::<Vec<_>>()
    };
    let regex = match regex {
        RegexExpr::Union(items) => RegexExpr::Union(children(items)),
        RegexExpr::Intersect(items) => RegexExpr::Intersect(children(items)),
        RegexExpr::Concat(items) => RegexExpr::Concat(children(items)),
        RegexExpr::Star(child) => RegexExpr::Star(Box::new(rewrite(rng, child))),
        RegexExpr::Not(child) => RegexExpr::Not(Box::new(rewrite(rng, child))),
        leaf => leaf.clone(),
    };
    if rng.below(3) == 0 {
        rewrite_root(rng, regex)
    } else {
        regex
    }
}

/// One language-preserving rewrite at the root of `regex`.
fn rewrite_root(rng: &mut Rng, regex: RegexExpr<Access>) -> RegexExpr<Access> {
    let not = |regex| RegexExpr::Not(Box::new(regex));
    if rng.below(4) == 0 {
        return not(not(regex));
    }
    match regex {
        RegexExpr::Empty => RegexExpr::Test(TestExpr::False),
        RegexExpr::Epsilon => RegexExpr::Star(Box::new(RegexExpr::Empty)),
        RegexExpr::All => RegexExpr::Star(Box::new(RegexExpr::Test(TestExpr::True))),
        RegexExpr::Test(TestExpr::Or(tests)) => {
            RegexExpr::Union(tests.into_iter().map(RegexExpr::Test).collect())
        }
        // An empty conjunction is one arbitrary event, but an empty intersection is `Σ*`.
        RegexExpr::Test(TestExpr::And(tests)) if !tests.is_empty() => {
            RegexExpr::Intersect(tests.into_iter().map(RegexExpr::Test).collect())
        }
        // One event, and not one event failing the test.
        RegexExpr::Test(test) => RegexExpr::Intersect(vec![
            RegexExpr::Test(TestExpr::True),
            not(RegexExpr::Test(negate(&test))),
        ]),
        RegexExpr::Union(children) => not(RegexExpr::Intersect(
            children.into_iter().map(not).collect(),
        )),
        RegexExpr::Intersect(children) => {
            not(RegexExpr::Union(children.into_iter().map(not).collect()))
        }
        RegexExpr::Concat(mut children) => match children.pop() {
            Some(RegexExpr::Union(last)) => RegexExpr::Union(
                last.into_iter()
                    .map(|piece| {
                        let mut pieces = children.clone();
                        pieces.push(piece);
                        RegexExpr::Concat(pieces)
                    })
                    .collect(),
            ),
            Some(last) => {
                children.insert(0, RegexExpr::Epsilon);
                children.push(last);
                RegexExpr::Concat(children)
            }
            None => RegexExpr::Epsilon,
        },
        RegexExpr::Star(child) => match rng.below(3) {
            0 => RegexExpr::Union(vec![
                RegexExpr::Epsilon,
                RegexExpr::Concat(vec![(*child).clone(), RegexExpr::Star(child)]),
            ]),
            1 => RegexExpr::Star(Box::new(RegexExpr::Star(child))),
            _ => RegexExpr::Concat(vec![RegexExpr::Star(child.clone()), RegexExpr::Star(child)]),
        },
        RegexExpr::Not(child) => RegexExpr::Intersect(vec![RegexExpr::All, RegexExpr::Not(child)]),
    }
}

fn negate(test: &TestExpr<Access>) -> TestExpr<Access> {
    match test {
        TestExpr::True => TestExpr::False,
        TestExpr::False => TestExpr::True,
        TestExpr::Atom {
            comparison,
            pattern,
        } => TestExpr::atom(
            match comparison {
                Comparison::Eq => Comparison::Neq,
                Comparison::Neq => Comparison::Eq,
            },
            pattern.clone(),
        ),
        TestExpr::And(tests) => TestExpr::Or(tests.iter().map(negate).collect()),
        TestExpr::Or(tests) => TestExpr::And(tests.iter().map(negate).collect()),
    }
}

/// Whether `test` holds of `event` when tail variables take the candidate's values.
fn holds(test: &TestExpr<Access>, event: Access, candidate: Access) -> bool {
    fn resolve<T: Copy>(pattern: &ComponentPattern<T>, register: T) -> T {
        match pattern {
            ComponentPattern::Constant(value) => *value,
            ComponentPattern::Variable(_) => register,
        }
    }
    match test {
        TestExpr::True => true,
        TestExpr::False => false,
        TestExpr::And(tests) => tests.iter().all(|test| holds(test, event, candidate)),
        TestExpr::Or(tests) => tests.iter().any(|test| holds(test, event, candidate)),
        TestExpr::Atom {
            comparison,
            pattern,
        } => {
            let coordinate = pattern.component.index();
            let equal = event.component(coordinate)
                == resolve(&pattern.pattern, candidate.component(coordinate));
            equal == matches!(comparison, Comparison::Eq)
        }
    }
}

/// Start positions as bits; histories stay below 16 events.
type Starts = u16;

/// A subexpression whose children precede it.
enum Node {
    Empty,
    All,
    Epsilon,
    Test(usize),
    Union(Vec<usize>),
    Intersect(Vec<usize>),
    Not(usize),
    Concat(usize, usize),
    Star(usize),
}

/// Direct interpreter of source expressions. For a history `w` and each subexpression `e`, it
/// keeps per end position `j` the starts `i` with `w[i..j] ∈ L(e)`, one column per `j`.
#[derive(Default)]
struct Interpreter<'a> {
    nodes: Vec<Node>,
    tests: Vec<&'a TestExpr<Access>>,
}

impl<'a> Interpreter<'a> {
    fn add(&mut self, regex: &'a RegexExpr<Access>) -> usize {
        let node = match regex {
            RegexExpr::Empty => Node::Empty,
            RegexExpr::All => Node::All,
            RegexExpr::Epsilon => Node::Epsilon,
            RegexExpr::Test(test) => {
                self.tests.push(test);
                Node::Test(self.tests.len() - 1)
            }
            RegexExpr::Union(children) => {
                Node::Union(children.iter().map(|child| self.add(child)).collect())
            }
            RegexExpr::Intersect(children) => {
                Node::Intersect(children.iter().map(|child| self.add(child)).collect())
            }
            RegexExpr::Not(child) => Node::Not(self.add(child)),
            RegexExpr::Star(child) => Node::Star(self.add(child)),
            RegexExpr::Concat(children) => {
                let Some((first, rest)) = children.split_first() else {
                    return self.push(Node::Epsilon);
                };
                let mut prefix = self.add(first);
                for child in rest {
                    let child = self.add(child);
                    prefix = self.push(Node::Concat(prefix, child));
                }
                return prefix;
            }
        };
        self.push(node)
    }

    fn push(&mut self, node: Node) -> usize {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    /// The column for the end after `stack`; `truth` holds the tests' values on the event
    /// before that end, and is absent for the empty history.
    fn column(&self, stack: &[Vec<Starts>], truth: Option<&[bool]>) -> Vec<Starts> {
        let end = stack.len();
        let every: Starts = (1 << (end + 1)) - 1;
        let mut column: Vec<Starts> = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            let starts = match node {
                Node::Empty => 0,
                Node::All => every,
                Node::Epsilon => 1 << end,
                Node::Test(test) => match truth {
                    Some(truth) if truth[*test] => 1 << (end - 1),
                    _ => 0,
                },
                Node::Union(children) => {
                    let mut starts = 0;
                    for &child in children {
                        starts |= column[child];
                    }
                    starts
                }
                Node::Intersect(children) => {
                    let mut starts = every;
                    for &child in children {
                        starts &= column[child];
                    }
                    starts
                }
                Node::Not(child) => every & !column[*child],
                // A match of `first` ending where a match of `second` ending here starts.
                Node::Concat(first, second) => {
                    let splits = column[*second];
                    let mut starts = if splits >> end & 1 == 1 {
                        column[*first]
                    } else {
                        0
                    };
                    for (split, earlier) in stack.iter().enumerate() {
                        if splits >> split & 1 == 1 {
                            starts |= earlier[*first];
                        }
                    }
                    starts
                }
                // An iteration ending where a non-empty last one ending here starts.
                Node::Star(child) => {
                    let splits = column[*child];
                    let mut starts = 1 << end;
                    for (split, earlier) in stack.iter().enumerate() {
                        if splits >> split & 1 == 1 {
                            starts |= earlier[index];
                        }
                    }
                    starts
                }
            };
            column.push(starts);
        }
        column
    }

    /// The tests' values on each event, keeping one event per distinct assignment.
    fn letters(&self, setup: &Setup, candidate: Access) -> Vec<Vec<bool>> {
        let mut seen = HashSet::new();
        setup
            .events()
            .map(|event| {
                self.tests
                    .iter()
                    .map(|test| holds(test, event, candidate))
                    .collect::<Vec<_>>()
            })
            .filter(|truth| seen.insert(truth.clone()))
            .collect()
    }

    fn accepts(&self, root: usize, history: &[Access], candidate: Access) -> bool {
        let mut stack = vec![self.column(&[], None)];
        for &event in history {
            let truth = self
                .tests
                .iter()
                .map(|test| holds(test, event, candidate))
                .collect::<Vec<_>>();
            let column = self.column(&stack, Some(&truth));
            stack.push(column);
        }
        stack[history.len()][root] & 1 == 1
    }

    /// For each direction, the length of the shortest history of at most `bound` letters in the
    /// language of one root and not of the other.
    fn shortest(
        &self,
        roots: [usize; 2],
        letters: &[Vec<bool>],
        bound: usize,
    ) -> [Option<usize>; 2] {
        let mut shortest = [None; 2];
        let mut stack = vec![self.column(&[], None)];
        self.descend(&mut stack, roots, letters, bound, &mut shortest);
        shortest
    }

    fn descend(
        &self,
        stack: &mut Vec<Vec<Starts>>,
        roots: [usize; 2],
        letters: &[Vec<bool>],
        bound: usize,
        shortest: &mut [Option<usize>; 2],
    ) {
        let length = stack.len() - 1;
        let accepted = roots.map(|root| stack[length][root] & 1 == 1);
        for direction in 0..2 {
            if accepted[direction]
                && !accepted[1 - direction]
                && shortest[direction].is_none_or(|shortest| length < shortest)
            {
                shortest[direction] = Some(length);
            }
        }
        let improvable = shortest
            .iter()
            .any(|shortest| shortest.is_none_or(|shortest| length + 1 < shortest));
        if length == bound || !improvable {
            return;
        }
        for truth in letters {
            let column = self.column(stack, Some(truth));
            stack.push(column);
            self.descend(stack, roots, letters, bound, shortest);
            stack.pop();
        }
    }
}

// ===== Random small policies over `(u8, u8)` with declared domains, every pair enumerated =====

/// Declared values per coordinate; every candidate and history event is enumerated from these.
const PAIR_D0: [u8; 3] = [0, 1, 2];
const PAIR_D1: [u8; 2] = [0, 1];
/// Longest history the brute force enumerates.
const PAIR_BOUND: usize = 3;
/// Random policies per query kind.
const PAIR_CASES: usize = 30;

type Pair = (u8, u8);
type PairComponent = Component2<u8, u8>;

fn pair_domains() -> Domains<Pair> {
    Domains::infinite()
        .with_domain(Component(0), &PAIR_D0.map(Component2::C0))
        .expect("domain")
        .with_domain(Component(1), &PAIR_D1.map(Component2::C1))
        .expect("domain")
}

fn pair_events() -> Vec<Pair> {
    PAIR_D0
        .iter()
        .flat_map(|&a| PAIR_D1.iter().map(move |&b| (a, b)))
        .collect()
}

/// Every history of length at most `PAIR_BOUND`, shortest first.
fn pair_histories() -> Vec<Vec<Pair>> {
    let events = pair_events();
    let mut all = vec![Vec::new()];
    let mut layer = vec![Vec::new()];
    for _ in 0..PAIR_BOUND {
        layer = layer
            .iter()
            .flat_map(|history: &Vec<Pair>| {
                events.iter().map(move |&event| {
                    let mut longer = history.clone();
                    longer.push(event);
                    longer
                })
            })
            .collect();
        all.extend(layer.iter().cloned());
    }
    all
}

fn pair_constant(rng: &mut Rng, coordinate: usize) -> PairComponent {
    if coordinate == 0 {
        Component2::C0(PAIR_D0[rng.below(PAIR_D0.len())])
    } else {
        Component2::C1(PAIR_D1[rng.below(PAIR_D1.len())])
    }
}

fn pair_head(rng: &mut Rng) -> Head<Pair> {
    Head::new((0..2).map(|coordinate| {
        if rng.below(2) == 0 {
            ComponentPattern::variable(["x", "y"][coordinate])
        } else {
            ComponentPattern::constant(pair_constant(rng, coordinate))
        }
    }))
}

/// A test on one coordinate; a variable is used only where the head binds one.
fn pair_test(rng: &mut Rng, head: &Head<Pair>) -> TestExpr<Pair> {
    let coordinate = rng.below(2);
    let bound = matches!(head.0[coordinate], ComponentPattern::Variable(_));
    let pattern = if bound && rng.below(2) == 0 {
        ComponentPattern::variable(["x", "y"][coordinate])
    } else {
        ComponentPattern::constant(pair_constant(rng, coordinate))
    };
    let comparison = if rng.below(2) == 0 {
        Comparison::Eq
    } else {
        Comparison::Neq
    };
    TestExpr::atom(
        comparison,
        AtomPattern::new(Component(coordinate as u8), pattern),
    )
}

fn pair_regex(rng: &mut Rng, head: &Head<Pair>, depth: usize) -> RegexExpr<Pair> {
    if depth == 0 {
        return match rng.below(4) {
            0 => RegexExpr::Epsilon,
            1 => RegexExpr::All,
            _ => RegexExpr::Test(pair_test(rng, head)),
        };
    }
    let kind = rng.below(6);
    let mut child = || pair_regex(rng, head, depth - 1);
    match kind {
        0 => RegexExpr::Union(vec![child()]),
        1 => RegexExpr::Concat(vec![child(), child()]),
        2 => RegexExpr::Union(vec![child(), child()]),
        3 => RegexExpr::Intersect(vec![child(), child()]),
        4 => RegexExpr::Star(Box::new(child())),
        5 => RegexExpr::Not(Box::new(child())),
        _ => RegexExpr::Concat(vec![RegexExpr::All, child()]),
    }
}

fn pair_rule(rng: &mut Rng) -> Rule<Pair> {
    let head = pair_head(rng);
    let tail = pair_regex(rng, &head, 2);
    let mode = if rng.below(2) == 0 {
        RuleMode::Forbid
    } else {
        RuleMode::Require
    };
    Rule::new(mode, head, tail)
}

fn pair_component(event: Pair, coordinate: usize) -> PairComponent {
    event.component(coordinate)
}

fn pair_head_matches(head: &Head<Pair>, candidate: Pair) -> bool {
    head.0.iter().enumerate().all(|(i, pattern)| match pattern {
        ComponentPattern::Constant(c) => *c == pair_component(candidate, i),
        ComponentPattern::Variable(_) => true,
    })
}

/// `test_sem`: a variable resolves only to the candidate's binding at the same coordinate.
fn pair_test_holds(test: &TestExpr<Pair>, head: &Head<Pair>, candidate: Pair, event: Pair) -> bool {
    match test {
        TestExpr::True => true,
        TestExpr::False => false,
        TestExpr::Atom {
            comparison,
            pattern,
        } => {
            let i = pattern.component.index();
            let expected = match &pattern.pattern {
                ComponentPattern::Constant(c) => Some(*c),
                ComponentPattern::Variable(name) => match &head.0[i] {
                    ComponentPattern::Variable(bound) if bound == name => {
                        Some(pair_component(candidate, i))
                    }
                    _ => None,
                },
            };
            let actual = pair_component(event, i);
            match (comparison, expected) {
                (_, None) => false,
                (Comparison::Eq, Some(value)) => actual == value,
                (Comparison::Neq, Some(value)) => actual != value,
            }
        }
        TestExpr::And(children) => children
            .iter()
            .all(|child| pair_test_holds(child, head, candidate, event)),
        TestExpr::Or(children) => children
            .iter()
            .any(|child| pair_test_holds(child, head, candidate, event)),
    }
}

/// `lang` by enumeration of the splits of `history`.
fn pair_lang(
    regex: &RegexExpr<Pair>,
    head: &Head<Pair>,
    candidate: Pair,
    history: &[Pair],
) -> bool {
    fn concat(
        children: &[RegexExpr<Pair>],
        head: &Head<Pair>,
        candidate: Pair,
        history: &[Pair],
    ) -> bool {
        match children.split_first() {
            None => history.is_empty(),
            Some((first, rest)) => (0..=history.len()).any(|k| {
                pair_lang(first, head, candidate, &history[..k])
                    && concat(rest, head, candidate, &history[k..])
            }),
        }
    }
    fn star(child: &RegexExpr<Pair>, head: &Head<Pair>, candidate: Pair, history: &[Pair]) -> bool {
        history.is_empty()
            || (1..=history.len()).any(|k| {
                pair_lang(child, head, candidate, &history[..k])
                    && star(child, head, candidate, &history[k..])
            })
    }
    match regex {
        RegexExpr::Empty => false,
        RegexExpr::All => true,
        RegexExpr::Epsilon => history.is_empty(),
        RegexExpr::Test(test) => {
            history.len() == 1 && pair_test_holds(test, head, candidate, history[0])
        }
        RegexExpr::Union(children) => children
            .iter()
            .any(|child| pair_lang(child, head, candidate, history)),
        RegexExpr::Intersect(children) => children
            .iter()
            .all(|child| pair_lang(child, head, candidate, history)),
        RegexExpr::Concat(children) => concat(children, head, candidate, history),
        RegexExpr::Star(child) => star(child, head, candidate, history),
        RegexExpr::Not(child) => !pair_lang(child, head, candidate, history),
    }
}

/// `rule_violated`.
fn pair_violated(rule: &Rule<Pair>, candidate: Pair, history: &[Pair]) -> bool {
    pair_head_matches(&rule.head, candidate)
        && match rule.mode {
            RuleMode::Forbid => pair_lang(&rule.tail, &rule.head, candidate, history),
            RuleMode::Require => !pair_lang(&rule.tail, &rule.head, candidate, history),
        }
}

/// `policy_denies` for the rules selected by index.
fn pair_denies(rules: &[Rule<Pair>], policy: &[usize], candidate: Pair, history: &[Pair]) -> bool {
    policy
        .iter()
        .any(|&index| pair_violated(&rules[index], candidate, history))
}

/// All domains are declared, so a witness has exactly one real instance.
fn pair_instance(witness: &Counterexample<Pair>) -> (Pair, Vec<Pair>) {
    fn event(components: &Components<Pair>) -> Pair {
        let value = |index: usize| match components.values[index] {
            Value::Constant(c) => c,
            Value::Fresh(_) => panic!("declared components have no fresh values: {components:?}"),
        };
        match (value(0), value(1)) {
            (Component2::C0(a), Component2::C1(b)) => (a, b),
            other => panic!("components out of order: {other:?}"),
        }
    }
    (
        event(&witness.candidate),
        witness.history.iter().map(event).collect(),
    )
}

/// `verdict` against brute force over every pair with a history of length at most `PAIR_BOUND`:
/// `Holds` iff no enumerated pair `fails`; a counterexample instantiates to a pair that `fails`,
/// and is no longer than the bound only if the brute force found a failing pair too.
fn pair_check(
    verdict: Inclusion<Pair>,
    fails: impl Fn(Pair, &[Pair]) -> bool,
    context: &dyn Fn() -> String,
) {
    let brute = pair_events()
        .into_iter()
        .flat_map(|candidate| {
            pair_histories()
                .into_iter()
                .map(move |history| (candidate, history))
        })
        .find(|(candidate, history)| fails(*candidate, history));
    match verdict {
        Inclusion::Holds => assert!(
            brute.is_none(),
            "holds despite the failing pair {brute:?}: {}",
            context()
        ),
        Inclusion::Counterexample(witness) => {
            let (candidate, history) = pair_instance(&witness);
            assert!(
                fails(candidate, &history),
                "{witness:?} decodes to {candidate:?}/{history:?}, which does not fail: {}",
                context()
            );
            assert!(
                brute.is_some() || history.len() > PAIR_BOUND,
                "brute force found no failing pair but {witness:?} is short: {}",
                context()
            );
        }
        Inclusion::Exhausted => panic!("search exhausted: {}", context()),
    }
}

fn pair_setup(rng: &mut Rng, count: usize) -> (PolicyAnalyzer<Pair>, Vec<Rule<Pair>>, Vec<RuleId>) {
    let rules = (0..count).map(|_| pair_rule(rng)).collect::<Vec<_>>();
    let mut analyzer = PolicyAnalyzer::new(pair_domains());
    let ids = rules
        .iter()
        .map(|rule| analyzer.add_rule(rule).unwrap())
        .collect::<Vec<_>>();
    (analyzer, rules, ids)
}

#[test]
fn pair_covered_agrees_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0011);
    for _ in 0..PAIR_CASES {
        let (analyzer, rules, ids) = pair_setup(&mut rng, 3);
        let verdict = analyzer.covered(ids[0], &ids[1..]).unwrap();
        pair_check(
            verdict,
            |c, h| pair_violated(&rules[0], c, h) && !pair_denies(&rules, &[1, 2], c, h),
            &|| format!("covered: {rules:?}"),
        );
    }
}

#[test]
fn pair_redundant_agrees_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0012);
    for _ in 0..PAIR_CASES {
        let (analyzer, rules, ids) = pair_setup(&mut rng, 3);
        let verdict = analyzer.redundant(ids[0], &ids).unwrap();
        pair_check(
            verdict,
            |c, h| pair_denies(&rules, &[0, 1, 2], c, h) != pair_denies(&rules, &[1, 2], c, h),
            &|| format!("redundant: {rules:?}"),
        );
    }
}

#[test]
fn pair_at_least_as_strict_agrees_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0013);
    for _ in 0..PAIR_CASES {
        let (analyzer, rules, ids) = pair_setup(&mut rng, 4);
        let verdict = analyzer.at_least_as_strict(&ids[..2], &ids[2..]).unwrap();
        pair_check(
            verdict,
            |c, h| pair_denies(&rules, &[2, 3], c, h) && !pair_denies(&rules, &[0, 1], c, h),
            &|| format!("at_least_as_strict: {rules:?}"),
        );
    }
}

#[test]
fn pair_tail_included_agrees_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0014);
    for _ in 0..PAIR_CASES {
        let head = pair_head(&mut rng);
        let left = pair_regex(&mut rng, &head, 2);
        let right = pair_regex(&mut rng, &head, 2);
        let mut analyzer = PolicyAnalyzer::new(pair_domains());
        let verdict = analyzer.tail_included(&head, &left, &right).unwrap();
        let fails = |c: Pair, h: &[Pair]| {
            pair_head_matches(&head, c)
                && pair_lang(&left, &head, c, h)
                && !pair_lang(&right, &head, c, h)
        };
        if let Inclusion::Counterexample(witness) = &verdict {
            // Tail counterexamples have globally minimum length (`shortest`).
            let (_, history) = pair_instance(witness);
            let shortest = pair_histories()
                .into_iter()
                .find(|h| pair_events().into_iter().any(|c| fails(c, h)))
                .map(|h| h.len());
            assert_eq!(
                shortest.unwrap_or(PAIR_BOUND + 1).min(history.len()),
                history.len(),
                "{witness:?} is not shortest: {head:?} {left:?} {right:?}"
            );
        }
        pair_check(verdict, fails, &|| {
            format!("tail_included: {head:?} {left:?} {right:?}")
        });
    }
}
