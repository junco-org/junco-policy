//! Differential test for tail inclusion: random tails with registers, decided by every search
//! configuration and checked against an independent reference semantics.
//!
//! Every reported counterexample is replayed through the reference semantics. Inclusion is also
//! refuted by brute force over all valuations and all histories up to a bound, drawn from
//! representative values: the constants, the candidate's values, and one further fresh value per
//! component, which together realise every class of events the tests can distinguish. The brute
//! force therefore finds the shortest counterexample up to the bound, which the simple strategy's
//! counterexamples must match.

use junco_policy::{
    Action, Alphabet, AtomPattern, Bump, Comparison, ComponentPattern, Event, Head, Inclusion,
    PolicyAnalyzer, RegexExpr, Resource, SearchOptions, Strategy, Subsumption, TestExpr,
};

const CASES: usize = 400;
const MAX_HISTORY: usize = 2;
/// Nesting depth of generated tails.
const DEPTH: usize = 3;

/// Deterministic xorshift generator.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

fn head() -> Head {
    Head::new(
        ComponentPattern::variable("p"),
        ComponentPattern::constant(Action::Edit),
        ComponentPattern::variable("r"),
    )
}

fn random_atom(rng: &mut Rng) -> TestExpr {
    let comparison = if rng.below(3) == 0 {
        Comparison::Neq
    } else {
        Comparison::Eq
    };
    let pattern = match rng.below(6) {
        0 => AtomPattern::Principal(ComponentPattern::constant("a")),
        1 => AtomPattern::Principal(ComponentPattern::variable("p")),
        2 => AtomPattern::Action(ComponentPattern::constant(Action::Read)),
        3 => AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
        4 => AtomPattern::Resource(ComponentPattern::constant(["x"])),
        _ => AtomPattern::Resource(ComponentPattern::variable("r")),
    };
    TestExpr::atom(comparison, pattern)
}

fn random_test(rng: &mut Rng, depth: usize) -> TestExpr {
    match (depth, rng.below(8)) {
        (0, _) | (_, 0..=3) => random_atom(rng),
        (_, 4 | 5) => TestExpr::and([random_test(rng, depth - 1), random_test(rng, depth - 1)]),
        (_, 6) => TestExpr::or([random_test(rng, depth - 1), random_test(rng, depth - 1)]),
        _ => TestExpr::true_test(),
    }
}

fn random_regex(rng: &mut Rng, depth: usize) -> RegexExpr {
    if depth == 0 {
        return match rng.below(6) {
            0 => RegexExpr::all(),
            1 => RegexExpr::epsilon(),
            _ => RegexExpr::test(random_test(rng, 2)),
        };
    }
    let child = |rng: &mut Rng| random_regex(rng, depth - 1);
    match rng.below(10) {
        0 => RegexExpr::test(random_test(rng, 2)),
        1 => RegexExpr::all(),
        2 | 3 => RegexExpr::concat([child(rng), child(rng)]),
        4 => RegexExpr::concat([RegexExpr::all(), child(rng), RegexExpr::all()]),
        5 => RegexExpr::union([child(rng), child(rng)]),
        6 => RegexExpr::star(child(rng)),
        7 => RegexExpr::intersect([child(rng), child(rng)]),
        8 => RegexExpr::complement(child(rng)),
        _ => RegexExpr::empty(),
    }
}

/// Values of the candidate's principal and resource.
#[derive(Clone, Debug)]
struct Valuation {
    principal: String,
    resource: Resource,
}

fn atom_holds(pattern: &AtomPattern, event: &Event, valuation: &Valuation) -> bool {
    match pattern {
        AtomPattern::Principal(ComponentPattern::Constant(value)) => event.principal == *value,
        AtomPattern::Principal(ComponentPattern::Variable(_)) => {
            event.principal.as_str() == valuation.principal
        }
        AtomPattern::Action(ComponentPattern::Constant(value)) => event.action == *value,
        AtomPattern::Action(ComponentPattern::Variable(_)) => event.action == Action::Edit,
        AtomPattern::Resource(ComponentPattern::Constant(value)) => event.resource == *value,
        AtomPattern::Resource(ComponentPattern::Variable(_)) => {
            event.resource == valuation.resource
        }
    }
}

fn test_holds(test: &TestExpr, event: &Event, valuation: &Valuation) -> bool {
    match test {
        TestExpr::True => true,
        TestExpr::False => false,
        TestExpr::Atom {
            comparison,
            pattern,
        } => atom_holds(pattern, event, valuation) == (*comparison == Comparison::Eq),
        TestExpr::And(children) => children
            .iter()
            .all(|child| test_holds(child, event, valuation)),
        TestExpr::Or(children) => children
            .iter()
            .any(|child| test_holds(child, event, valuation)),
    }
}

fn accepts(regex: &RegexExpr, history: &[Event], valuation: &Valuation) -> bool {
    match regex {
        RegexExpr::Empty => false,
        RegexExpr::All => true,
        RegexExpr::Epsilon => history.is_empty(),
        RegexExpr::Test(test) => history.len() == 1 && test_holds(test, &history[0], valuation),
        RegexExpr::Union(children) => children
            .iter()
            .any(|child| accepts(child, history, valuation)),
        RegexExpr::Intersect(children) => children
            .iter()
            .all(|child| accepts(child, history, valuation)),
        RegexExpr::Not(inner) => !accepts(inner, history, valuation),
        RegexExpr::Concat(factors) => match factors.split_first() {
            None => history.is_empty(),
            Some((first, rest)) => (0..=history.len()).any(|split| {
                accepts(first, &history[..split], valuation)
                    && accepts(
                        &RegexExpr::Concat(rest.to_vec()),
                        &history[split..],
                        valuation,
                    )
            }),
        },
        RegexExpr::Star(inner) => {
            history.is_empty()
                || (1..=history.len()).any(|split| {
                    accepts(inner, &history[..split], valuation)
                        && accepts(regex, &history[split..], valuation)
                })
        }
    }
}

fn representative_events() -> Vec<Event> {
    let mut events = Vec::new();
    for principal in ["a", "f1", "f2"] {
        for action in [Action::Read, Action::Edit, Action::commit("m")] {
            for resource in ["x", "f1", "f2"] {
                events.push(Event::new(principal, action.clone(), [resource]));
            }
        }
    }
    events
}

fn histories(events: &[Event], max: usize) -> Vec<Vec<Event>> {
    let mut all = vec![Vec::new()];
    let mut frontier = vec![Vec::new()];
    for _ in 0..max {
        let mut next = Vec::new();
        for history in &frontier {
            for event in events {
                let mut longer: Vec<Event> = history.clone();
                longer.push(event.clone());
                next.push(longer);
            }
        }
        all.extend(next.iter().cloned());
        frontier = next;
    }
    all
}

fn valuations() -> Vec<Valuation> {
    let mut all = Vec::new();
    for principal in ["a", "f1"] {
        for resource in ["x", "f1"] {
            all.push(Valuation {
                principal: principal.to_owned(),
                resource: Resource::new([resource]),
            });
        }
    }
    all
}

fn configurations() -> Vec<SearchOptions> {
    let options = |strategy, subsumption, prune_visited, alphabet| SearchOptions {
        strategy,
        subsumption,
        prune_visited,
        alphabet,
        max_items: None,
    };
    vec![
        SearchOptions::default(),
        options(
            Strategy::Residual,
            Subsumption::Identity,
            false,
            Alphabet::Minterms,
        ),
        options(
            Strategy::Antichain,
            Subsumption::Identity,
            false,
            Alphabet::Letters,
        ),
        options(
            Strategy::Antichain,
            Subsumption::Implication,
            true,
            Alphabet::Letters,
        ),
        options(
            Strategy::Antichain,
            Subsumption::Identity,
            true,
            Alphabet::Minterms,
        ),
        options(
            Strategy::Brzozowski,
            Subsumption::Identity,
            false,
            Alphabet::Letters,
        ),
        options(
            Strategy::Brzozowski,
            Subsumption::Implication,
            true,
            Alphabet::Letters,
        ),
        options(
            Strategy::Simple,
            Subsumption::Identity,
            false,
            Alphabet::Letters,
        ),
        options(
            Strategy::Simple,
            Subsumption::Identity,
            false,
            Alphabet::Minterms,
        ),
    ]
}

#[test]
fn random_inclusions_agree_with_the_reference_semantics() {
    let events = representative_events();
    let histories = histories(&events, MAX_HISTORY);
    let valuations = valuations();
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut refuted = 0;
    for case in 0..CASES {
        let left = random_regex(&mut rng, DEPTH);
        let right = random_regex(&mut rng, DEPTH);
        let shortest = histories
            .iter()
            .filter(|history| {
                valuations.iter().any(|valuation| {
                    accepts(&left, history, valuation) && !accepts(&right, history, valuation)
                })
            })
            .map(Vec::len)
            .min();
        let mut verdicts = Vec::new();
        for options in configurations() {
            let arena = Bump::new();
            let mut analyzer = PolicyAnalyzer::with_options(&arena, options);
            let verdict = analyzer
                .tail_included(&head(), &left, &right)
                .expect("generated tails compile");
            let holds = match verdict.inclusion {
                Inclusion::Holds => true,
                Inclusion::Counterexample(counterexample) => {
                    let candidate = &counterexample.candidate;
                    assert_eq!(candidate.action, Action::Edit, "case {case}: head constant");
                    let valuation = Valuation {
                        principal: candidate.principal.as_str().to_owned(),
                        resource: candidate.resource.clone(),
                    };
                    assert!(
                        accepts(&left, &counterexample.history, &valuation)
                            && !accepts(&right, &counterexample.history, &valuation),
                        "case {case}, {options:?}: {counterexample:?} does not refute\n\
                         left = {left:?}\nright = {right:?}"
                    );
                    if options.strategy == Strategy::Simple {
                        let length = counterexample.history.len();
                        assert!(
                            shortest.map_or(length > MAX_HISTORY, |shortest| length == shortest),
                            "case {case}, {options:?}: {counterexample:?} is not shortest\n\
                             left = {left:?}\nright = {right:?}"
                        );
                    }
                    false
                }
                Inclusion::Exhausted => panic!("no budget was set"),
            };
            verdicts.push(holds);
        }
        assert!(
            verdicts.windows(2).all(|pair| pair[0] == pair[1]),
            "case {case}: configurations disagree {verdicts:?}\nleft = {left:?}\nright = {right:?}"
        );
        if shortest.is_some() {
            assert!(
                !verdicts[0],
                "case {case}: brute force refutes an inclusion the search accepts\n\
                 left = {left:?}\nright = {right:?}"
            );
        }
        refuted += usize::from(!verdicts[0]);
    }
    // Both outcomes must be exercised for the comparison to mean anything.
    assert!(
        refuted > CASES / 10 && refuted < CASES - CASES / 10,
        "refuted {refuted}"
    );
}
