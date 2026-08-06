use bumpalo::Bump;
use thiserror::Error;

use crate::model::{Event, Grant, Request};
use crate::syntax::{CompiledHead, RegexId, Rule, RuleMode, SyntaxContext};

#[derive(Debug, Error, PartialEq, Eq)]
pub enum CompileError {
    #[error("rule {rule}: variable {name:?} occurs in different product components")]
    VariableComponentConflict { rule: usize, name: String },
    #[error("rule {rule}: tail variable {name:?} is not bound by the head")]
    UnboundVariable { rule: usize, name: String },
    #[error("rule {rule}: more than 65535 head variables are not supported")]
    TooManyVariables { rule: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial {
    pub rule_index: usize,
    pub mode: RuleMode,
    pub event: Event,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<M> {
    Grant(Grant<M>),
    Denied(Denial),
}

impl<M> Decision<M> {
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

#[derive(Clone, Copy)]
struct CompiledRule<'a> {
    mode: RuleMode,
    head: CompiledHead<'a>,
    tail: RegexId<'a>,
}

pub struct Validator<'a> {
    syntax: SyntaxContext<'a>,
    rules: Vec<CompiledRule<'a>>,
    history: Vec<Event>,
}

impl<'a> Validator<'a> {
    pub fn compile(
        arena: &'a Bump,
        rules: impl IntoIterator<Item = Rule>,
    ) -> Result<Self, CompileError> {
        let mut syntax = SyntaxContext::new(arena);
        let mut compiled = Vec::new();
        for (index, rule) in rules.into_iter().enumerate() {
            let rule_index = index + 1;
            let (head, tail) = syntax.compile_rule_parts(rule_index, &rule.head, &rule.tail)?;
            compiled.push(CompiledRule {
                mode: rule.mode,
                head,
                tail,
            });
        }
        Ok(Self {
            syntax,
            rules: compiled,
            history: Vec::new(),
        })
    }

    pub fn check<M>(&mut self, request: Request<M>) -> Decision<M> {
        for (index, rule) in self.rules.iter().copied().enumerate() {
            let Some(bindings) = rule.head.matches(&request.event) else {
                continue;
            };
            let accepts = self
                .syntax
                .accepts(rule.tail, self.history.iter(), &bindings);
            let violated = match rule.mode {
                RuleMode::Require => !accepts,
                RuleMode::Forbid => accepts,
            };
            if violated {
                let rule_index = index + 1;
                let relation = match rule.mode {
                    RuleMode::Require => "does not satisfy required",
                    RuleMode::Forbid => "satisfies forbidden",
                };
                return Decision::Denied(Denial {
                    rule_index,
                    mode: rule.mode,
                    event: request.event,
                    message: format!("committed history {relation} past-regex rule {rule_index}"),
                });
            }
        }

        self.history.push(request.event.clone());
        Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        })
    }

    pub fn history(&self) -> &[Event] {
        &self.history
    }

    pub fn checkpoint(&self) -> usize {
        self.history.len()
    }

    pub fn rollback(&mut self, checkpoint: usize) {
        assert!(
            checkpoint <= self.history.len(),
            "invalid validator checkpoint"
        );
        self.history.truncate(checkpoint);
    }
}
