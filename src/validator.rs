//! Policy compilation, stateful authorization, and rollback.
//!
//! A `ValidatorBuilder` compiles rules into one shared syntax context. A finished [`Validator`]
//! owns a single append-only committed history. Each check binds a candidate against rule heads,
//! evaluates matching tails over the pre-candidate history, and appends exactly once only when no
//! rule is violated.

use std::fmt;

use bumpalo::Bump;
use thiserror::Error;

use crate::model::{Event, Grant, Request};
use crate::syntax::{
    CompiledHead, ContextId, Head, Regex, RegexId, RuleMode, RuleSyntax, SyntaxContext,
};

/// One-based source position of a policy rule.
///
/// This newtype prevents a rule ordinal from being confused with a history position or another
/// table index. Internally it is `usize`, matching the `Vec` that stores compiled rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleIndex(usize);

impl RuleIndex {
    /// Creates a one-based rule index, returning `None` for zero.
    pub const fn new(one_based: usize) -> Option<Self> {
        if one_based == 0 {
            None
        } else {
            Some(Self(one_based))
        }
    }

    /// Returns the one-based numeric position used in diagnostics.
    pub const fn get(self) -> usize {
        self.0
    }

    /// Converts a zero-based `Vec` position to a checked one-based diagnostic index.
    fn from_zero_based(zero_based: usize) -> Self {
        Self(
            zero_based
                .checked_add(1)
                .expect("rule index space exhausted"),
        )
    }
}

impl fmt::Display for RuleIndex {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Rule-construction failure detected before a validator can execute.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum CompileError {
    /// One variable name occurs in different product components in the same rule.
    #[error("rule {rule}: variable {name:?} occurs in different product components")]
    VariableComponentConflict {
        /// One-based source rule position.
        rule: RuleIndex,
        /// Conflicting variable name.
        name: String,
    },
    /// A tail references a variable that its head does not bind.
    #[error("rule {rule}: tail variable {name:?} is not bound by the head")]
    UnboundVariable {
        /// One-based source rule position.
        rule: RuleIndex,
        /// Missing variable name.
        name: String,
    },
    /// A rule callback returned a syntax handle created by another rule or validator.
    #[error("rule {rule}: returned syntax was built for another rule scope")]
    ForeignRuleHandle {
        /// One-based source rule position.
        rule: RuleIndex,
    },
}

/// Diagnostic returned when the first matching rule is violated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial {
    /// One-based source position of the violated rule.
    pub rule_index: RuleIndex,
    /// Whether the violated rule required or forbade its tail language.
    pub mode: RuleMode,
    /// Candidate event that was denied and was not appended to history.
    pub event: Event,
    /// Human-readable explanation of the failed history relation.
    pub message: String,
}

/// Result of checking one capability request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<M> {
    /// Request was accepted and appended to committed history.
    Grant(Grant<M>),
    /// Request was rejected atomically; committed history is unchanged.
    Denied(Denial),
}

impl<M> Decision<M> {
    /// Returns `true` exactly for [`Decision::Grant`].
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

/// Opaque rollback position in one validator's committed history.
///
/// The history length must remain an index because rollback truncates a mutable `Vec`; returning a
/// borrowed history element would prevent later mutable checks. The accompanying reference-backed
/// context identity prevents checkpoints from crossing validators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Checkpoint<'arena> {
    context: ContextId<'arena>,
    history_len: usize,
}

impl Checkpoint<'_> {
    /// Number of committed events represented by this checkpoint.
    pub const fn history_len(self) -> usize {
        self.history_len
    }
}

/// Fully compiled rule; all fields are arena-backed and cheap to copy.
#[derive(Clone, Copy)]
struct CompiledRule<'arena> {
    mode: RuleMode,
    head: CompiledHead<'arena>,
    tail: RegexId<'arena>,
}

/// Incremental compiler for validator rules sharing one arena and canonical syntax context.
pub struct ValidatorBuilder<'arena> {
    syntax: SyntaxContext<'arena>,
    rules: Vec<CompiledRule<'arena>>,
}

impl<'arena> ValidatorBuilder<'arena> {
    /// Creates an empty builder whose compiled values live in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            syntax: SyntaxContext::new(arena),
            rules: Vec::new(),
        }
    }

    /// Compiles and appends one rule.
    ///
    /// `build` receives a rule-local syntax builder after `head` has established the variable
    /// scope. Returning a handle from another callback produces [`CompileError::ForeignRuleHandle`].
    pub fn add_rule<F>(
        &mut self,
        mode: RuleMode,
        head: Head,
        build: F,
    ) -> Result<&mut Self, CompileError>
    where
        F: FnOnce(&mut RuleSyntax<'_, 'arena>) -> Result<Regex<'arena>, CompileError>,
    {
        let rule_index = RuleIndex::from_zero_based(self.rules.len());
        let scope_id = self.syntax.new_rule_scope();
        let (head, tail) = {
            let (head, mut rule_syntax) =
                RuleSyntax::new(&mut self.syntax, rule_index, scope_id, &head)?;
            let tail = build(&mut rule_syntax)?;
            let tail = rule_syntax.finish_regex(tail)?;
            (head, tail)
        };
        self.rules.push(CompiledRule { mode, head, tail });
        Ok(self)
    }

    /// Finishes compilation with an empty committed history.
    pub fn finish(self) -> Validator<'arena> {
        Validator {
            syntax: self.syntax,
            rules: self.rules,
            history: Vec::new(),
        }
    }
}

/// Stateful validator for a fixed ordered rule set.
///
/// The validator is intentionally single-owner and mutable: derivatives may extend the shared
/// canonical DAG, and accepted events extend committed history. Denials are atomic.
pub struct Validator<'arena> {
    syntax: SyntaxContext<'arena>,
    rules: Vec<CompiledRule<'arena>>,
    history: Vec<Event>,
}

impl<'arena> Validator<'arena> {
    /// Starts compiling a validator in `arena`.
    pub fn builder(arena: &'arena Bump) -> ValidatorBuilder<'arena> {
        ValidatorBuilder::new(arena)
    }

    /// Checks one request against all rules in source order.
    ///
    /// A nonmatching head does not fire. For a matching head, `Require` denies when the complete
    /// committed history is outside the tail language, while `Forbid` denies when it is inside.
    /// The first violation wins. On success the candidate is appended once and its metadata is
    /// preserved in the returned grant.
    pub fn check<M>(&mut self, request: Request<M>) -> Decision<M> {
        for (zero_based, rule) in self.rules.iter().copied().enumerate() {
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
                let rule_index = RuleIndex::from_zero_based(zero_based);
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

    /// Returns committed grants' events in exact acceptance order.
    pub fn history(&self) -> &[Event] {
        &self.history
    }

    /// Captures an opaque rollback position for this validator.
    pub fn checkpoint(&self) -> Checkpoint<'arena> {
        Checkpoint {
            context: self.syntax.identity(),
            history_len: self.history.len(),
        }
    }

    /// Truncates committed history to `checkpoint`.
    ///
    /// # Panics
    ///
    /// Panics if the checkpoint belongs to another validator or names a future history position.
    pub fn rollback(&mut self, checkpoint: Checkpoint<'arena>) {
        assert_eq!(
            checkpoint.context,
            self.syntax.identity(),
            "checkpoint belongs to another validator"
        );
        assert!(
            checkpoint.history_len <= self.history.len(),
            "invalid validator checkpoint"
        );
        self.history.truncate(checkpoint.history_len);
    }
}
