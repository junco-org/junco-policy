use string_interner::DefaultSymbol;

use crate::model::Event;

use super::node::{CompiledAction, RegexId, RegexNode, TestId, TestNode};
use super::pattern::{AtomPattern, Comparison, ComponentPattern};
use super::scope::{Bindings, BoundValue, resource_matches};
use super::storage::SyntaxContext;

fn eval_component_pattern<'event, Constant: Copy, Actual>(
    pattern: ComponentPattern<Constant, DefaultSymbol>,
    actual: &Actual,
    bound: BoundValue<'event>,
    bindings: &Bindings<'event>,
    constant_matches: impl FnOnce(Constant, &Actual) -> bool,
) -> bool {
    match pattern {
        ComponentPattern::Constant(expected) => constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => bindings.get(symbol).equals(bound),
    }
}

fn eval_atom<'arena, 'event>(
    pattern: AtomPattern<&'arena str, CompiledAction<'arena>, &'arena [&'arena str], DefaultSymbol>,
    event: &'event Event,
    bindings: &Bindings<'event>,
) -> bool {
    match pattern {
        AtomPattern::Principal(pattern) => eval_component_pattern(
            pattern,
            &event.principal,
            BoundValue::Principal(&event.principal),
            bindings,
            |expected, actual| actual.as_str() == expected,
        ),
        AtomPattern::Action(pattern) => eval_component_pattern(
            pattern,
            &event.action,
            BoundValue::Action(&event.action),
            bindings,
            |expected, actual| expected.matches(actual),
        ),
        AtomPattern::Resource(pattern) => eval_component_pattern(
            pattern,
            &event.resource,
            BoundValue::Resource(&event.resource),
            bindings,
            resource_matches,
        ),
    }
}

impl<'a> SyntaxContext<'a> {
    pub(crate) fn accepts<'event>(
        &mut self,
        root: RegexId<'a>,
        history: impl IntoIterator<Item = &'event Event>,
        bindings: &Bindings<'event>,
    ) -> bool {
        let mut state = root;
        for event in history {
            state = self.derive(state, event, bindings);
        }
        self.nullable(state)
    }

    pub(super) fn derive<'event>(
        &mut self,
        regex: RegexId<'a>,
        event: &'event Event,
        bindings: &Bindings<'event>,
    ) -> RegexId<'a> {
        match *regex.get() {
            RegexNode::Empty | RegexNode::Epsilon => self.empty,
            RegexNode::All => self.all,
            RegexNode::Test(test) => {
                if self.eval_test(test, event, bindings) {
                    self.epsilon
                } else {
                    self.empty
                }
            }
            RegexNode::Union(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_union(derivatives)
            }
            RegexNode::Intersect(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_intersect(derivatives)
            }
            RegexNode::Not(inner) => {
                let derivative = self.derive(inner, event, bindings);
                self.regex_not(derivative)
            }
            RegexNode::Concat(factors) => {
                let mut alternatives = Vec::new();
                for (index, factor) in factors.iter().enumerate() {
                    let derivative = self.derive(*factor, event, bindings);
                    let mut product = Vec::with_capacity(factors.len() - index);
                    product.push(derivative);
                    product.extend_from_slice(&factors[index + 1..]);
                    alternatives.push(self.regex_concat(product));
                    if !self.nullable(*factor) {
                        break;
                    }
                }
                self.regex_union(alternatives)
            }
            RegexNode::Star(inner) => {
                let derivative = self.derive(inner, event, bindings);
                self.regex_concat(vec![derivative, regex])
            }
        }
    }

    fn eval_test<'event>(
        &self,
        test: TestId<'a>,
        event: &'event Event,
        bindings: &Bindings<'event>,
    ) -> bool {
        match *test.get() {
            TestNode::True => true,
            TestNode::False => false,
            TestNode::Atom {
                comparison,
                pattern,
            } => {
                let equal = eval_atom(pattern, event, bindings);
                match comparison {
                    Comparison::Eq => equal,
                    Comparison::Neq => !equal,
                }
            }
            TestNode::And(children) => children
                .iter()
                .all(|child| self.eval_test(*child, event, bindings)),
            TestNode::Or(children) => children
                .iter()
                .any(|child| self.eval_test(*child, event, bindings)),
        }
    }
}
