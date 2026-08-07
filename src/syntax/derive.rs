//! Exact Brzozowski derivatives and complete-history membership.
//!
//! A rule tail is evaluated by repeatedly deriving its canonical root by committed events in
//! source order, then reading the residual node's cached nullability. The candidate event is used
//! only to bind the rule head and is never included in this fold.

use crate::model::{Action, Event, Principal, Resource};

use super::component::{CompiledAtomPattern, CompiledPattern, Match};
use super::node::{RegexId, RegexKind, TestId, TestNode};
use super::pattern::{AtomPattern, Comparison, ComponentPattern};
use super::scope::Bindings;
use super::storage::SyntaxContext;

/// Evaluates one typed constant-or-variable component pattern.
fn eval_component_pattern<'arena, 'event, ComponentType: Match<'arena>>(
    pattern: CompiledPattern<'arena, ComponentType>,
    actual: &'event ComponentType,
    bindings: &Bindings<'event>,
) -> bool {
    match pattern {
        ComponentPattern::Constant(expected) => ComponentType::constant_matches(expected, actual),
        ComponentPattern::Variable(symbol) => {
            bindings.get(symbol).equals(ComponentType::bound(actual))
        }
    }
}

/// Evaluates the statically typed atom enum without trait-object dispatch.
fn eval_atom<'arena, 'event>(
    pattern: CompiledAtomPattern<'arena>,
    event: &'event Event,
    bindings: &Bindings<'event>,
) -> bool {
    match pattern {
        AtomPattern::Principal(pattern) => {
            eval_component_pattern::<Principal>(pattern, &event.principal, bindings)
        }
        AtomPattern::Action(pattern) => {
            eval_component_pattern::<Action>(pattern, &event.action, bindings)
        }
        AtomPattern::Resource(pattern) => {
            eval_component_pattern::<Resource>(pattern, &event.resource, bindings)
        }
    }
}

impl<'arena> SyntaxContext<'arena> {
    /// Accepts exactly when the complete event sequence belongs to `root` under `bindings`.
    pub(crate) fn accepts<'event>(
        &mut self,
        root: RegexId<'arena>,
        history: impl IntoIterator<Item = &'event Event>,
        bindings: &Bindings<'event>,
    ) -> bool {
        let mut state = root;
        for event in history {
            state = self.derive(state, event, bindings);
        }
        self.nullable(state)
    }

    /// Computes one exact derivative and normalizes every constructed residual.
    pub(super) fn derive<'event>(
        &mut self,
        regex: RegexId<'arena>,
        event: &'event Event,
        bindings: &Bindings<'event>,
    ) -> RegexId<'arena> {
        match regex.get().kind {
            RegexKind::Empty | RegexKind::Epsilon => self.empty,
            RegexKind::All => self.all,
            RegexKind::Test(test) => {
                if self.eval_test(test, event, bindings) {
                    self.epsilon
                } else {
                    self.empty
                }
            }
            RegexKind::Union(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_union(derivatives)
            }
            RegexKind::Intersect(children) => {
                let derivatives = children
                    .iter()
                    .map(|child| self.derive(*child, event, bindings))
                    .collect();
                self.regex_intersect(derivatives)
            }
            RegexKind::Not(inner) => {
                let derivative = self.derive(inner, event, bindings);
                self.regex_not(derivative)
            }
            RegexKind::Concat(factors) => {
                // D_e(r1...rn) is the union of each factor's derivative followed by its suffix,
                // stopping after the first non-nullable prefix factor.
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
            RegexKind::Star(inner) => {
                // D_e(r*) = D_e(r) r*. `regex` is already the canonical r* handle.
                let derivative = self.derive(inner, event, bindings);
                self.regex_concat(vec![derivative, regex])
            }
        }
    }

    /// Evaluates a normalized one-event boolean test.
    fn eval_test<'event>(
        &self,
        test: TestId<'arena>,
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
