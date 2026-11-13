// ----- policy queries: `covered`, `redundant`, `at_least_as_strict` -----

/// Random policies decided by each policy query.
const POLICY_CASES: usize = 40;

/// Principal constants that rules mention; principal 1 plays Alice.
const PRINCIPALS: [u32; 2] = [1, 2];

/// Resource constants that rules mention.
const RESOURCES: [u32; 2] = [MENTIONED, 11];

#[test]
fn policy_queries_agree_with_brute_force() {
    let mut rng = Rng(0x6a75_6e63_6f00_0002);
    for _ in 0..POLICY_CASES {
        let world = World::random(&mut rng);
        let count = 2 + rng.below(3);
        let rules = (0..count).map(|_| world.rule(&mut rng)).collect::<Vec<_>>();
        let mut analyzer = PolicyAnalyzer::new(world.domains.clone());
        let ids = rules
            .iter()
            .map(|rule| analyzer.add_rule(rule).unwrap())
            .collect::<Vec<_>>();
        let brute = Brute::new(&world, &rules);
        for rule in 0..count {
            let others = (0..count).filter(|&other| other != rule).collect::<Vec<_>>();
            let by = others.iter().map(|&other| ids[other]).collect::<Vec<_>>();
            let covered = analyzer.covered(ids[rule], &by).unwrap();
            brute.check_covered(rule, &others, &covered);
            // Redundancy in the whole policy is coverage by the other rules.
            let redundant = analyzer.redundant(ids[rule], &ids).unwrap();
            assert_eq!(
                matches!(redundant, Inclusion::Holds),
                matches!(covered, Inclusion::Holds),
                "redundant and covered disagree on rule {rule} of {rules:?}"
            );
            brute.check_covered(rule, &others, &redundant);
        }
        let split = 1 + rng.below(count - 1);
        let first = (0..split).collect::<Vec<_>>();
        let second = (split..count).collect::<Vec<_>>();
        for (stricter, than) in [(&first, &second), (&second, &first)] {
            let stricter_ids = stricter.iter().map(|&rule| ids[rule]).collect::<Vec<_>>();
            let than_ids = than.iter().map(|&rule| ids[rule]).collect::<Vec<_>>();
            let verdict = analyzer.at_least_as_strict(&stricter_ids, &than_ids).unwrap();
            brute.check_strict(stricter, than, &verdict);
        }
    }
}

/// The running example of the paper's reduction to inclusion (`inclusion.tex`): `R` forbids
/// `(a, edit, f)` after a history in `r`; `P` forbids `("Alice", edit, f)` after `r1` and
/// `(a, edit, f)` after `r2`. With a history in `r` and `r1` but not in `r2`, `P` does not cover
/// `R`, and the counterexample's agent is not Alice; once `r2` contains that history, `P` covers
/// `R`.
#[test]
fn covered_refutes_for_agents_other_than_alice() {
    let alice = PRINCIPALS[0];
    let head = |principal| {
        Head::<Access>::new(
            principal,
            ComponentPattern::constant(Action::Edit),
            ComponentPattern::variable("f"),
        )
    };
    let read_f = TestExpr::And(vec![
        TestExpr::atom(Comparison::Eq, AtomPattern::Action(ComponentPattern::constant(Action::Read))),
        TestExpr::atom(Comparison::Eq, AtomPattern::Resource(ComponentPattern::variable("f"))),
    ]);
    let ever = |test: TestExpr<Access>| {
        RegexExpr::Concat(vec![RegexExpr::All, RegexExpr::Test(test), RegexExpr::All])
    };
    let r = ever(read_f);
    let staged = ever(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Stage)),
    ));
    for (r2, covered) in [(staged, false), (r.clone(), true)] {
        let mut analyzer = PolicyAnalyzer::new(Domains::infinite().with_actions(ACTIONS));
        let anyone = || ComponentPattern::variable("a");
        let rule = analyzer
            .add_rule(&Rule::new(RuleMode::Forbid, head(anyone()), r.clone()))
            .unwrap();
        let by = [
            analyzer
                .add_rule(&Rule::new(RuleMode::Forbid, head(ComponentPattern::constant(alice)), r.clone()))
                .unwrap(),
            analyzer
                .add_rule(&Rule::new(RuleMode::Forbid, head(anyone()), r2))
                .unwrap(),
        ];
        match analyzer.covered(rule, &by).unwrap() {
            Inclusion::Holds => assert!(covered, "covered although r2 misses the history"),
            Inclusion::Counterexample(counterexample) => {
                assert!(!covered, "refuted although r2 contains r: {counterexample:?}");
                assert_ne!(
                    counterexample.candidate.principal,
                    Value::Constant(alice),
                    "Alice's own rule covers her: {counterexample:?}"
                );
                assert_eq!(counterexample.candidate.action, Value::Constant(Action::Edit));
                assert_eq!(counterexample.history.len(), 1, "{counterexample:?} is not shortest");
            }
            Inclusion::Exhausted => panic!("the search exhausted its budget"),
        }
    }
}

/// Declared domains, for random policies, and the concrete values the brute force ranges over.
#[derive(Debug)]
struct World {
    domains: Domains<Access>,
    principal_domain: Option<Vec<u32>>,
    resource_domain: Option<Vec<u32>>,
}

impl World {
    fn random(rng: &mut Rng) -> Self {
        let principal_domain = [None, Some(vec![1, 2]), Some(vec![1, 3])][rng.below(3)].clone();
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
        Self {
            domains,
            principal_domain,
            resource_domain,
        }
    }

    /// Candidates the brute force considers: each declared value of a finite component, and
    /// otherwise the constants and one value no rule mentions.
    fn candidates(&self) -> Vec<Access> {
        let principals = self.principal_domain.clone().unwrap_or_else(|| vec![1, 2, 3]);
        let resources = self
            .resource_domain
            .clone()
            .unwrap_or_else(|| vec![MENTIONED, 11, 12]);
        product(&principals, &resources)
    }

    /// History events the brute force considers for `candidate`: each declared value of a
    /// finite component, and otherwise the constants, the candidate's value, and two values no
    /// rule mentions, so some value differs from the candidate's and from every constant.
    fn events(&self, candidate: Access) -> Vec<Access> {
        let values = |domain: &Option<Vec<u32>>, base: [u32; 4], own: u32| match domain {
            Some(values) => values.clone(),
            None => {
                let mut values = base.to_vec();
                if !values.contains(&own) {
                    values.push(own);
                }
                values
            }
        };
        product(
            &values(&self.principal_domain, [1, 2, 3, 4], candidate.principal),
            &values(&self.resource_domain, [MENTIONED, 11, 12, 13], candidate.resource),
        )
    }

    /// A random rule: each head component is a constant or a variable, and the tail compares
    /// only bound components with the candidate's.
    fn rule(&self, rng: &mut Rng) -> Rule<Access> {
        let principal = if rng.below(3) == 0 {
            ComponentPattern::constant(PRINCIPALS[rng.below(2)])
        } else {
            ComponentPattern::variable("p")
        };
        let action = if rng.below(3) == 0 {
            ComponentPattern::variable("a")
        } else {
            ComponentPattern::constant([Action::Read, Action::Edit][rng.below(2)])
        };
        let resource = if rng.below(3) == 0 {
            ComponentPattern::constant(RESOURCES[rng.below(2)])
        } else {
            ComponentPattern::variable("r")
        };
        let head = Head::new(principal, action, resource);
        let mode = if rng.below(3) == 0 {
            RuleMode::Require
        } else {
            RuleMode::Forbid
        };
        let tail = self.regex(rng, &head, 2);
        Rule::new(mode, head, tail)
    }

    fn test(&self, rng: &mut Rng, head: &Head<Access>, depth: usize) -> TestExpr<Access> {
        if depth > 0 && rng.below(3) == 0 {
            let children = vec![self.test(rng, head, depth - 1), self.test(rng, head, depth - 1)];
            return if rng.below(2) == 0 {
                TestExpr::And(children)
            } else {
                TestExpr::Or(children)
            };
        }
        let pattern = match rng.below(7) {
            0 if is_variable(&head.principal) => AtomPattern::Principal(ComponentPattern::variable("p")),
            0 | 1 => AtomPattern::Principal(ComponentPattern::constant(PRINCIPALS[rng.below(2)])),
            2 if is_variable(&head.action) => AtomPattern::Action(ComponentPattern::variable("a")),
            2 | 3 => AtomPattern::Action(ComponentPattern::constant(
                [Action::Read, Action::Edit][rng.below(2)],
            )),
            4 if is_variable(&head.resource) => AtomPattern::Resource(ComponentPattern::variable("r")),
            4 | 5 => AtomPattern::Resource(ComponentPattern::constant(RESOURCES[rng.below(2)])),
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

    fn regex(&self, rng: &mut Rng, head: &Head<Access>, depth: usize) -> RegexExpr<Access> {
        if depth == 0 || rng.below(4) == 0 {
            let test = |rng: &mut Rng| RegexExpr::Test(self.test(rng, head, 1));
            return match rng.below(16) {
                0 => RegexExpr::Empty,
                1 => RegexExpr::Epsilon,
                2 => RegexExpr::All,
                3..=5 => RegexExpr::Star(Box::new(test(rng))),
                6..=10 => RegexExpr::Concat(vec![RegexExpr::All, test(rng), RegexExpr::All]),
                11 | 12 => RegexExpr::Concat(vec![
                    RegexExpr::All,
                    test(rng),
                    RegexExpr::Star(Box::new(test(rng))),
                ]),
                _ => test(rng),
            };
        }
        let child = |rng: &mut Rng| self.regex(rng, head, depth - 1);
        match rng.below(5) {
            0 => RegexExpr::Union(vec![child(rng), child(rng)]),
            1 => RegexExpr::Intersect(vec![child(rng), child(rng)]),
            2 => RegexExpr::Concat(vec![child(rng), child(rng)]),
            3 => RegexExpr::Star(Box::new(child(rng))),
            _ => RegexExpr::Not(Box::new(child(rng))),
        }
    }

    /// The concrete value of each component, checking it against the declared domains.
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

    /// Whether `a` and `b` agree on equality with every constant the analyzer may know: a
    /// refinement of the analyzer's candidate cases, so per-case minimality applies within it.
    fn same_profile(&self, a: Access, b: Access) -> bool {
        let principals = PRINCIPALS
            .iter()
            .chain(self.principal_domain.iter().flatten())
            .all(|&k| (a.principal == k) == (b.principal == k));
        let resources = RESOURCES
            .iter()
            .chain(self.resource_domain.iter().flatten())
            .all(|&k| (a.resource == k) == (b.resource == k));
        principals && a.action == b.action && resources
    }
}

fn product(principals: &[u32], resources: &[u32]) -> Vec<Access> {
    let mut events = Vec::new();
    for &principal in principals {
        for action in ACTIONS {
            for &resource in resources {
                events.push(Access {
                    principal,
                    action,
                    resource,
                });
            }
        }
    }
    events
}

fn is_variable<T>(pattern: &ComponentPattern<T>) -> bool {
    matches!(pattern, ComponentPattern::Variable(_))
}

fn head_matches(head: &Head<Access>, candidate: Access) -> bool {
    fn component<T: PartialEq + Copy>(pattern: &ComponentPattern<T>, value: T) -> bool {
        match pattern {
            ComponentPattern::Constant(constant) => *constant == value,
            ComponentPattern::Variable(_) => true,
        }
    }
    component(&head.principal, candidate.principal)
        && component(&head.action, candidate.action)
        && component(&head.resource, candidate.resource)
}

/// Whether the runtime denies `candidate` after `history` by some rule of `rules`.
fn runtime_denies(rules: &[&Rule<Access>], history: &[Access], candidate: Access) -> bool {
    let store = Arc::new(Store::new().unwrap());
    let rules = rules
        .iter()
        .map(|rule| TraceRule::new((*rule).clone(), |_| (String::new(), Vec::new())))
        .collect::<Vec<_>>();
    let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
    let history = History::from_events(store, history.iter().copied()).unwrap();
    policy.decide(&history, &candidate).unwrap() != PolicyDecision::Grant
}

/// What a candidate's denials depend on: the classes of events its tails' tests tell apart, and
/// which heads match it.
type Key = (Vec<Vec<bool>>, Vec<bool>);

/// Brute-force denials of a policy's rules over every history of the world's events up to a
/// length bound.
struct Brute<'a> {
    world: &'a World,
    rules: &'a [Rule<Access>],
    interpreter: Interpreter<'a>,
    roots: Vec<usize>,
    candidates: Vec<(Access, Key)>,
}

impl<'a> Brute<'a> {
    fn new(world: &'a World, rules: &'a [Rule<Access>]) -> Self {
        let mut interpreter = Interpreter::default();
        let roots = rules.iter().map(|rule| interpreter.add(&rule.tail)).collect();
        let mut brute = Self {
            world,
            rules,
            interpreter,
            roots,
            candidates: Vec::new(),
        };
        brute.candidates = world
            .candidates()
            .into_iter()
            .map(|candidate| (candidate, brute.key(candidate)))
            .collect();
        brute
    }

    fn key(&self, candidate: Access) -> Key {
        let mut seen = HashSet::new();
        let mut letters = self
            .world
            .events(candidate)
            .into_iter()
            .map(|event| {
                self.interpreter
                    .tests
                    .iter()
                    .map(|test| holds(test, event, candidate))
                    .collect::<Vec<_>>()
            })
            .filter(|truth| seen.insert(truth.clone()))
            .collect::<Vec<_>>();
        letters.sort_unstable();
        let matches = self
            .rules
            .iter()
            .map(|rule| head_matches(&rule.head, candidate))
            .collect();
        (letters, matches)
    }

    /// Whether each rule denies, given which heads match and which tails accept the history.
    fn denials(&self, matches: &[bool], accepted: &[bool]) -> Vec<bool> {
        self.rules
            .iter()
            .enumerate()
            .map(|(rule, source)| {
                matches[rule]
                    && match source.mode {
                        RuleMode::Forbid => accepted[rule],
                        RuleMode::Require => !accepted[rule],
                    }
            })
            .collect()
    }

    /// The denials of `candidate` after `history`, by the interpreter.
    fn denials_of(&self, history: &[Access], candidate: Access) -> Vec<bool> {
        let accepted = self
            .roots
            .iter()
            .map(|&root| self.interpreter.accepts(root, history, candidate))
            .collect::<Vec<_>>();
        let matches = self
            .rules
            .iter()
            .map(|rule| head_matches(&rule.head, candidate))
            .collect::<Vec<_>>();
        self.denials(&matches, &accepted)
    }

    /// Per candidate key, the length bound and the shortest history within it whose denials
    /// fail.
    fn shortest(&self, key: &Key, fails: &dyn Fn(&[bool]) -> bool) -> (usize, Option<usize>) {
        let (letters, matches) = key;
        let bound = bound(letters.len());
        let mut best = None;
        let mut stack = vec![self.interpreter.column(&[], None)];
        self.descend(&mut stack, letters, matches, bound, fails, &mut best);
        (bound, best)
    }

    fn descend(
        &self,
        stack: &mut Vec<Vec<Starts>>,
        letters: &[Vec<bool>],
        matches: &[bool],
        bound: usize,
        fails: &dyn Fn(&[bool]) -> bool,
        best: &mut Option<usize>,
    ) {
        let length = stack.len() - 1;
        let accepted = self
            .roots
            .iter()
            .map(|&root| stack[length][root] & 1 == 1)
            .collect::<Vec<_>>();
        if fails(&self.denials(matches, &accepted)) && best.is_none_or(|best| length < best) {
            *best = Some(length);
        }
        if length == bound || best.is_some_and(|best| length + 1 >= best) {
            return;
        }
        for truth in letters {
            let column = self.interpreter.column(stack, Some(truth));
            stack.push(column);
            self.descend(stack, letters, matches, bound, fails, best);
            stack.pop();
        }
    }

    /// Per candidate, the bound and shortest failing length, computed once per key.
    fn table(&self, fails: &dyn Fn(&[bool]) -> bool) -> Vec<(Access, usize, Option<usize>)> {
        let mut searched = HashMap::new();
        self.candidates
            .iter()
            .map(|(candidate, key)| {
                let (bound, shortest) = *searched
                    .entry(key.clone())
                    .or_insert_with_key(|key| self.shortest(key, fails));
                (*candidate, bound, shortest)
            })
            .collect()
    }

    /// The counterexample's concrete candidate and history.
    fn concrete(&self, counterexample: &Counterexample<Access>) -> (Access, Vec<Access>) {
        let candidate = self.world.concrete(&counterexample.candidate);
        let history = counterexample
            .history
            .iter()
            .map(|components| self.world.concrete(components))
            .collect();
        (candidate, history)
    }

    /// Whether no candidate with the profile of `candidate` fails, by `fails`, within a history
    /// shorter than `length`.
    fn shortest_in_case(&self, candidate: Access, length: usize, fails: &dyn Fn(&[bool]) -> bool) -> bool {
        let key = self.key(candidate);
        let (bound, own) = self.shortest(&key, fails);
        (length > bound || own == Some(length))
            && self.table(fails).iter().all(|&(other, _, shortest)| {
                !self.world.same_profile(candidate, other) || shortest.is_none_or(|shortest| length <= shortest)
            })
    }

    /// Checks a verdict on whether `fails` never holds: `Holds` means no candidate fails within
    /// the bound; a counterexample fails by the interpreter and by the runtime, and no candidate
    /// with its constant profile fails sooner.
    fn check(
        &self,
        verdict: &Inclusion<Access>,
        fails: &dyn Fn(&[bool]) -> bool,
        runtime_fails: &dyn Fn(&[Access], Access) -> bool,
        context: &dyn Fn() -> String,
    ) {
        match verdict {
            Inclusion::Holds => {
                for (candidate, _, shortest) in self.table(fails) {
                    assert!(
                        shortest.is_none(),
                        "holds, but {candidate:?} fails after {shortest:?} events: {}",
                        context()
                    );
                }
            }
            Inclusion::Counterexample(counterexample) => {
                let (candidate, history) = self.concrete(counterexample);
                assert!(
                    fails(&self.denials_of(&history, candidate)),
                    "{counterexample:?} does not fail: {}",
                    context()
                );
                assert!(
                    runtime_fails(&history, candidate),
                    "the runtime disagrees on {counterexample:?}: {}",
                    context()
                );
                assert!(
                    self.shortest_in_case(candidate, history.len(), fails),
                    "{counterexample:?} is not shortest within its case: {}",
                    context()
                );
            }
            Inclusion::Exhausted => panic!("the search exhausted its budget: {}", context()),
        }
    }

    fn check_covered(&self, rule: usize, by: &[usize], verdict: &Inclusion<Access>) {
        let fails = |denials: &[bool]| denials[rule] && !by.iter().any(|&other| denials[other]);
        let runtime_fails = |history: &[Access], candidate: Access| {
            let by = by.iter().map(|&other| &self.rules[other]).collect::<Vec<_>>();
            runtime_denies(&[&self.rules[rule]], history, candidate)
                && !runtime_denies(&by, history, candidate)
        };
        let context = || {
            let by = by.iter().map(|&other| &self.rules[other]).collect::<Vec<_>>();
            format!("covered({:?}, {by:?}) in {:?}", self.rules[rule], self.world)
        };
        self.check(verdict, &fails, &runtime_fails, &context);
    }

    fn check_strict(&self, stricter: &[usize], than: &[usize], verdict: &Inclusion<Access>) {
        let permits = |denials: &[bool]| !stricter.iter().any(|&rule| denials[rule]);
        let fails = |denials: &[bool]| permits(denials) && than.iter().any(|&rule| denials[rule]);
        let runtime_fails = |history: &[Access], candidate: Access| {
            let stricter = stricter.iter().map(|&rule| &self.rules[rule]).collect::<Vec<_>>();
            let than = than.iter().map(|&rule| &self.rules[rule]).collect::<Vec<_>>();
            !runtime_denies(&stricter, history, candidate) && runtime_denies(&than, history, candidate)
        };
        let context = || {
            format!(
                "at_least_as_strict({stricter:?}, {than:?}) of {:?} in {:?}",
                self.rules, self.world
            )
        };
        let Inclusion::Counterexample(counterexample) = verdict else {
            return self.check(verdict, &fails, &runtime_fails, &context);
        };
        let (candidate, history) = self.concrete(counterexample);
        let denials = self.denials_of(&history, candidate);
        assert!(fails(&denials), "{counterexample:?} does not fail: {}", context());
        assert!(
            runtime_fails(&history, candidate),
            "the runtime disagrees on {counterexample:?}: {}",
            context()
        );
        // Minimality holds within the case for a rule of `than` that the counterexample shows
        // uncovered.
        assert!(
            than.iter().any(|&rule| {
                denials[rule]
                    && self.shortest_in_case(candidate, history.len(), &|denials: &[bool]| {
                        permits(denials) && denials[rule]
                    })
            }),
            "{counterexample:?} is not shortest within its case for any rule: {}",
            context()
        );
    }
}
