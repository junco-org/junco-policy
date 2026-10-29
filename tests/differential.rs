use junco_core::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Request, Rule, RuleMode,
    Store, TestExpr, Validator,
};
use junco_policy::{Action, LockEvent};
use std::sync::Arc;

/// Principal of committed history events versus the rule-probing candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Actor {
    History,
    Probe,
}

/// Resource of committed history events versus the rule-probing candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Path {
    History,
    Probe,
}

#[derive(Clone, Debug)]
enum RefTest {
    True,
    False,
    Action(Comparison, Action),
    And(Vec<RefTest>),
    Or(Vec<RefTest>),
}

#[derive(Clone, Debug)]
enum RefRegex {
    Empty,
    All,
    Epsilon,
    Test(RefTest),
    Union(Vec<RefRegex>),
    Concat(Vec<RefRegex>),
    Star(Box<RefRegex>),
    Intersect(Vec<RefRegex>),
    Not(Box<RefRegex>),
}

/// A committed event that never matches the probe-only rule head.
fn event(action: Action) -> LockEvent<Actor, Path> {
    LockEvent::new(Actor::History, action, Path::History)
}

fn eval_test(test: &RefTest, event: &LockEvent<Actor, Path>) -> bool {
    match test {
        RefTest::True => true,
        RefTest::False => false,
        RefTest::Action(Comparison::Eq, expected) => event.action() == *expected,
        RefTest::Action(Comparison::Neq, expected) => event.action() != *expected,
        RefTest::And(children) => children.iter().all(|child| eval_test(child, event)),
        RefTest::Or(children) => children.iter().any(|child| eval_test(child, event)),
    }
}

fn accepts(regex: &RefRegex, history: &[LockEvent<Actor, Path>]) -> bool {
    match regex {
        RefRegex::Empty => false,
        RefRegex::All => true,
        RefRegex::Epsilon => history.is_empty(),
        RefRegex::Test(test) => history.len() == 1 && eval_test(test, &history[0]),
        RefRegex::Union(children) => children.iter().any(|child| accepts(child, history)),
        RefRegex::Intersect(children) => children.iter().all(|child| accepts(child, history)),
        RefRegex::Not(inner) => !accepts(inner, history),
        RefRegex::Concat(factors) => accepts_concat(factors, history),
        RefRegex::Star(inner) => {
            history.is_empty()
                || (1..=history.len()).any(|split| {
                    accepts(inner, &history[..split]) && accepts(regex, &history[split..])
                })
        }
    }
}

fn accepts_concat(factors: &[RefRegex], history: &[LockEvent<Actor, Path>]) -> bool {
    match factors {
        [] => history.is_empty(),
        [only] => accepts(only, history),
        [first, rest @ ..] => (0..=history.len()).any(|split| {
            accepts(first, &history[..split]) && accepts_concat(rest, &history[split..])
        }),
    }
}

fn source_test(source: &RefTest) -> TestExpr<LockEvent<Actor, Path>> {
    match source {
        RefTest::True => TestExpr::true_test(),
        RefTest::False => TestExpr::false_test(),
        RefTest::Action(comparison, action) => TestExpr::atom(
            *comparison,
            AtomPattern::Action(ComponentPattern::constant(*action)),
        ),
        RefTest::And(children) => TestExpr::and(children.iter().map(source_test)),
        RefTest::Or(children) => TestExpr::or(children.iter().map(source_test)),
    }
}

fn source_regex(source: &RefRegex) -> RegexExpr<LockEvent<Actor, Path>> {
    match source {
        RefRegex::Empty => RegexExpr::empty(),
        RefRegex::All => RegexExpr::all(),
        RefRegex::Epsilon => RegexExpr::epsilon(),
        RefRegex::Test(test) => RegexExpr::test(source_test(test)),
        RefRegex::Union(children) => RegexExpr::union(children.iter().map(source_regex)),
        RefRegex::Concat(children) => RegexExpr::concat(children.iter().map(source_regex)),
        RefRegex::Star(inner) => RegexExpr::star(source_regex(inner)),
        RefRegex::Intersect(children) => RegexExpr::intersect(children.iter().map(source_regex)),
        RefRegex::Not(inner) => RegexExpr::complement(source_regex(inner)),
    }
}

struct Generator(u64);

impl Generator {
    fn next(&mut self, upper: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 32) as usize) % upper
    }

    fn action(&mut self) -> Action {
        match self.next(3) {
            0 => Action::Read,
            1 => Action::Edit,
            _ => Action::Release,
        }
    }

    fn test(&mut self, depth: usize) -> RefTest {
        if depth == 0 {
            return match self.next(5) {
                0 => RefTest::True,
                1 => RefTest::False,
                2 => RefTest::Action(Comparison::Eq, self.action()),
                3 => RefTest::Action(Comparison::Neq, self.action()),
                _ => RefTest::And(vec![
                    RefTest::Action(Comparison::Eq, self.action()),
                    RefTest::Action(Comparison::Neq, self.action()),
                ]),
            };
        }
        match self.next(4) {
            0 => RefTest::And(vec![self.test(depth - 1), self.test(depth - 1)]),
            1 => RefTest::Or(vec![self.test(depth - 1), self.test(depth - 1)]),
            _ => self.test(0),
        }
    }

    fn regex(&mut self, depth: usize) -> RefRegex {
        if depth == 0 {
            return match self.next(5) {
                0 => RefRegex::Empty,
                1 => RefRegex::All,
                2 => RefRegex::Epsilon,
                _ => RefRegex::Test(self.test(1)),
            };
        }
        match self.next(9) {
            0 => RefRegex::Empty,
            1 => RefRegex::All,
            2 => RefRegex::Epsilon,
            3 => RefRegex::Test(self.test(1)),
            4 => RefRegex::Union(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            5 => RefRegex::Concat(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            6 => RefRegex::Star(Box::new(self.regex(depth - 1))),
            7 => RefRegex::Intersect(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            _ => RefRegex::Not(Box::new(self.regex(depth - 1))),
        }
    }
}

/// Drives every prefix of `word` through one retained validator for `regex`.
///
/// At each prefix the probe is checked twice with `permits` (cold or suffix-resumed, then warm)
/// against the reference interpreter; the next word event is then appended through `check`.
fn assert_prefixes_match_reference(regex: &RefRegex, word: &[LockEvent<Actor, Path>]) {
    let store = Arc::new(Store::new().unwrap());
    let probe = LockEvent::new(Actor::Probe, Action::Remove, Path::Probe);
    let mut builder = Validator::builder(Arc::clone(&store));
    builder
        .add_rule(Rule::new(
            RuleMode::Require,
            Head::new(
                ComponentPattern::constant(Actor::Probe),
                ComponentPattern::constant(Action::Remove),
                ComponentPattern::constant(Path::Probe),
            ),
            source_regex(regex),
        ))
        .unwrap();
    let mut validator = builder.finish().unwrap();
    for split in 0..=word.len() {
        let prefix = &word[..split];
        let expected = accepts(regex, prefix);
        for pass in ["first", "repeat"] {
            assert_eq!(
                validator.permits(&probe).unwrap(),
                expected,
                "{pass} permits: {regex:?} over {prefix:?}"
            );
        }
        if let Some(next) = word.get(split) {
            assert!(validator.check(Request::new(*next, ())).unwrap().is_grant());
        }
    }
}

#[test]
fn derivatives_match_an_independent_language_interpreter() {
    let mut generator = Generator(0x5eed_cafe_f00d_beef);
    for _ in 0..500 {
        let regex = generator.regex(3);
        let word: Vec<_> = (0..generator.next(5))
            .map(|_| event(generator.action()))
            .collect();
        assert_prefixes_match_reference(&regex, &word);
    }
}

fn histories(max_len: usize) -> Vec<Vec<LockEvent<Actor, Path>>> {
    fn extend(
        prefix: &mut Vec<LockEvent<Actor, Path>>,
        remaining: usize,
        output: &mut Vec<Vec<LockEvent<Actor, Path>>>,
    ) {
        output.push(prefix.clone());
        if remaining == 0 {
            return;
        }
        for action in [Action::Read, Action::Edit, Action::Release] {
            prefix.push(event(action));
            extend(prefix, remaining - 1, output);
            prefix.pop();
        }
    }

    let mut output = Vec::new();
    extend(&mut Vec::new(), max_len, &mut output);
    output
}

#[test]
fn every_short_word_matches_the_reference_for_boundary_expressions() {
    let read = RefRegex::Test(RefTest::Action(Comparison::Eq, Action::Read));
    let edit = RefRegex::Test(RefTest::Action(Comparison::Eq, Action::Edit));
    let release = RefRegex::Test(RefTest::Action(Comparison::Eq, Action::Release));
    let read_or_edit = RefRegex::Union(vec![read.clone(), edit.clone()]);
    let contains_edit = RefRegex::Concat(vec![RefRegex::All, edit.clone(), RefRegex::All]);
    let corpus = vec![
        RefRegex::Empty,
        RefRegex::All,
        RefRegex::Epsilon,
        read.clone(),
        RefRegex::Not(Box::new(read.clone())),
        read_or_edit.clone(),
        RefRegex::Concat(vec![read.clone(), edit.clone()]),
        RefRegex::Concat(vec![RefRegex::Epsilon, read.clone(), RefRegex::Epsilon]),
        RefRegex::Star(Box::new(read.clone())),
        RefRegex::Star(Box::new(read_or_edit.clone())),
        RefRegex::Intersect(vec![read_or_edit.clone(), read.clone()]),
        RefRegex::Intersect(vec![read.clone(), RefRegex::Not(Box::new(read.clone()))]),
        contains_edit.clone(),
        RefRegex::Not(Box::new(contains_edit)),
        RefRegex::Union(vec![release, RefRegex::Not(Box::new(read_or_edit))]),
    ];

    for expression in &corpus {
        for word in histories(4) {
            assert_prefixes_match_reference(expression, &word);
        }
    }
}
