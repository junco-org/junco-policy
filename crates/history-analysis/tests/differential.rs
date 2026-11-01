//! Differential test of tail inclusion against a direct interpreter of the source expressions.
//!
//! Random tail pairs are decided by the analyzer and by brute force over every history up to a
//! length bound. The brute force ranges over concrete events and merges two of them only when
//! every atom of the pair has the same value on both, which cannot merge events that the tails
//! tell apart. A counterexample must fail by the interpreter and by the runtime, and no shorter
//! history within the bound may fail. A search that exhausts the runtime's graph budget has no
//! verdict to check, but a rewrite must never be refuted.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use history_analysis::{Components, Domains, Inclusion, PolicyAnalyzer, Value};
use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
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
        let verdicts = check(&setup, &tail, &rewritten);
        assert!(
            !verdicts.contains(&Some(false)),
            "{tail:?} and its rewrite {rewritten:?} differ"
        );
    }
}

/// Decides `left ⊑ right` and `right ⊑ left` under `setup`, checks both verdicts against brute
/// force, and returns whether each holds, or `None` if its search was exhausted.
fn check(setup: &Setup, left: &RegexExpr<Access>, right: &RegexExpr<Access>) -> [Option<bool>; 2] {
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
        match verdict.inclusion {
            Inclusion::Holds => {
                for (candidate, _, shortest) in &brute {
                    assert!(
                        shortest[direction].is_none(),
                        "holds, but {candidate:?} fails after {:?} events: {}",
                        shortest[direction],
                        context()
                    );
                }
                Some(true)
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
                Some(false)
            }
            Inclusion::Exhausted => None,
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
        let mut domains = Domains::infinite().with_actions(ACTIONS);
        if let Some(values) = &principal_domain {
            domains = domains.with_principals(values.iter().copied());
        }
        if let Some(values) = &resource_domain {
            domains = domains.with_resources(values.iter().copied());
        }
        let head = Head::new(
            ComponentPattern::variable("p"),
            if action_register {
                ComponentPattern::variable("a")
            } else {
                ComponentPattern::constant(Action::Edit)
            },
            if resource_register {
                ComponentPattern::variable("r")
            } else {
                ComponentPattern::constant(MENTIONED)
            },
        );
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
            0 => AtomPattern::Principal(ComponentPattern::variable("p")),
            1 if self.action_register => AtomPattern::Action(ComponentPattern::variable("a")),
            1 | 2 => AtomPattern::Action(ComponentPattern::constant(
                [Action::Read, Action::Edit][rng.below(2)],
            )),
            3 if self.resource_register => AtomPattern::Resource(ComponentPattern::variable("r")),
            3 | 4 => AtomPattern::Resource(ComponentPattern::constant(MENTIONED)),
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
        let Value::Constant(action) = components.action else {
            panic!("declared actions have no fresh values");
        };
        Access {
            principal: concrete(components.principal, self.principal_domain.as_deref()),
            action,
            resource: concrete(components.resource, self.resource_domain.as_deref()),
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
            let equal = match pattern {
                AtomPattern::Principal(pattern) => {
                    event.principal == resolve(pattern, candidate.principal)
                }
                AtomPattern::Action(pattern) => event.action == resolve(pattern, candidate.action),
                AtomPattern::Resource(pattern) => {
                    event.resource == resolve(pattern, candidate.resource)
                }
            };
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
