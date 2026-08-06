use rust_validator::{
    Action, Bump, ComponentPattern, Event, Head, Regex, Request, Rule, RuleMode, Test, Validator,
};

fn event(action: Action) -> Event {
    Event::new("history", action, ["history"])
}

fn eval_test(test: &Test, event: &Event) -> bool {
    match test {
        Test::True => true,
        Test::False => false,
        Test::EqAction(ComponentPattern::Constant(expected)) => &event.action == expected,
        Test::NeAction(ComponentPattern::Constant(expected)) => &event.action != expected,
        Test::And(children) => children.iter().all(|child| eval_test(child, event)),
        Test::Or(children) => children.iter().any(|child| eval_test(child, event)),
        Test::EqPrincipal(_)
        | Test::NePrincipal(_)
        | Test::EqResource(_)
        | Test::NeResource(_)
        | Test::EqAction(ComponentPattern::Variable(_))
        | Test::NeAction(ComponentPattern::Variable(_)) => {
            panic!("generator emitted a test outside its reference fragment")
        }
    }
}

fn accepts(regex: &Regex, history: &[Event]) -> bool {
    match regex {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => history.is_empty(),
        Regex::Test(test) => history.len() == 1 && eval_test(test, &history[0]),
        Regex::Union(children) => children.iter().any(|child| accepts(child, history)),
        Regex::Intersect(children) => children.iter().all(|child| accepts(child, history)),
        Regex::Not(inner) => !accepts(inner, history),
        Regex::Concat(factors) => accepts_concat(factors, history),
        Regex::Star(inner) => {
            history.is_empty()
                || (1..=history.len()).any(|split| {
                    accepts(inner, &history[..split]) && accepts(regex, &history[split..])
                })
        }
    }
}

fn accepts_concat(factors: &[Regex], history: &[Event]) -> bool {
    match factors {
        [] => history.is_empty(),
        [only] => accepts(only, history),
        [first, rest @ ..] => (0..=history.len()).any(|split| {
            accepts(first, &history[..split]) && accepts_concat(rest, &history[split..])
        }),
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
            _ => Action::Stage,
        }
    }

    fn test(&mut self, depth: usize) -> Test {
        if depth == 0 {
            return match self.next(5) {
                0 => Test::True,
                1 => Test::False,
                2 => Test::EqAction(ComponentPattern::constant(self.action())),
                3 => Test::NeAction(ComponentPattern::constant(self.action())),
                _ => Test::and([
                    Test::EqAction(ComponentPattern::constant(self.action())),
                    Test::NeAction(ComponentPattern::constant(self.action())),
                ]),
            };
        }
        match self.next(4) {
            0 => Test::and([self.test(depth - 1), self.test(depth - 1)]),
            1 => Test::or([self.test(depth - 1), self.test(depth - 1)]),
            _ => self.test(0),
        }
    }

    fn regex(&mut self, depth: usize) -> Regex {
        if depth == 0 {
            return match self.next(5) {
                0 => Regex::Empty,
                1 => Regex::All,
                2 => Regex::Epsilon,
                _ => Regex::test(self.test(1)),
            };
        }
        match self.next(9) {
            0 => Regex::Empty,
            1 => Regex::All,
            2 => Regex::Epsilon,
            3 => Regex::test(self.test(1)),
            4 => Regex::union([self.regex(depth - 1), self.regex(depth - 1)]),
            5 => Regex::concat([self.regex(depth - 1), self.regex(depth - 1)]),
            6 => Regex::star(self.regex(depth - 1)),
            7 => Regex::intersect([self.regex(depth - 1), self.regex(depth - 1)]),
            _ => Regex::not(self.regex(depth - 1)),
        }
    }
}

fn implementation_accepts(regex: Regex, history: &[Event]) -> bool {
    let arena = Bump::new();
    let probe = Event::new("probe", Action::History, ["probe"]);
    let rule = Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::constant("probe"),
            ComponentPattern::constant(Action::History),
            ComponentPattern::constant(["probe"]),
        ),
        regex,
    );
    let mut validator = Validator::compile(&arena, [rule]).unwrap();
    for event in history {
        assert!(validator.check(Request::new(event.clone(), ())).is_grant());
    }
    validator.check(Request::new(probe, ())).is_grant()
}

#[test]
fn derivatives_match_an_independent_language_interpreter() {
    let mut generator = Generator(0x5eed_cafe_f00d_beef);
    for case in 0..500 {
        let regex = generator.regex(3);
        let history: Vec<Event> = (0..generator.next(5))
            .map(|_| event(generator.action()))
            .collect();
        let expected = accepts(&regex, &history);
        let actual = implementation_accepts(regex.clone(), &history);
        assert_eq!(actual, expected, "case {case}: {regex:?} over {history:?}");
    }
}

fn histories(max_len: usize) -> Vec<Vec<Event>> {
    fn extend(prefix: &mut Vec<Event>, remaining: usize, output: &mut Vec<Vec<Event>>) {
        output.push(prefix.clone());
        if remaining == 0 {
            return;
        }
        for action in [Action::Read, Action::Edit, Action::Stage] {
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
    let read = Regex::test(Test::EqAction(ComponentPattern::constant(Action::Read)));
    let edit = Regex::test(Test::EqAction(ComponentPattern::constant(Action::Edit)));
    let stage = Regex::test(Test::EqAction(ComponentPattern::constant(Action::Stage)));
    let read_or_edit = Regex::union([read.clone(), edit.clone()]);
    let contains_edit = Regex::concat([Regex::All, edit.clone(), Regex::All]);
    let corpus = vec![
        Regex::Empty,
        Regex::All,
        Regex::Epsilon,
        read.clone(),
        Regex::not(read.clone()),
        read_or_edit.clone(),
        Regex::concat([read.clone(), edit.clone()]),
        Regex::concat([Regex::Epsilon, read.clone(), Regex::Epsilon]),
        Regex::star(read.clone()),
        Regex::star(read_or_edit.clone()),
        Regex::intersect([read_or_edit.clone(), read.clone()]),
        Regex::intersect([read.clone(), Regex::not(read.clone())]),
        contains_edit.clone(),
        Regex::not(contains_edit),
        Regex::union([stage, Regex::not(read_or_edit)]),
    ];

    for (expression, history) in corpus.into_iter().flat_map(|expression| {
        histories(4)
            .into_iter()
            .map(move |history| (expression.clone(), history))
    }) {
        assert_eq!(
            implementation_accepts(expression.clone(), &history),
            accepts(&expression, &history),
            "{expression:?} over {history:?}"
        );
    }
}
