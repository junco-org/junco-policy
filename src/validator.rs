//! Policy compilation, stateful authorization, and rollback.
//!
//! Source rules are complete owned values. `ValidatorBuilder` compiles each rule by explicitly
//! passing the canonical store and a temporary variable environment to compiler functions. The
//! executable validator retains only canonical compiled rules and committed history.

use std::fmt;

use bumpalo::Bump;
use thiserror::Error;

use crate::model::{Event, Grant, Request};
use crate::syntax::{CanonicalStore, CompiledRule, Rule, RuleMode, accepts, compile_rule};

/// One-based source position of a policy rule.
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

    /// Converts a zero-based rule-vector position to a checked one-based diagnostic index.
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

/// Rule-compilation failure detected before a validator can execute.
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

/// Opaque position in a validator's committed history.
///
/// A checkpoint deliberately contains no validator or store backreference. It is a role-specific
/// history length and must be used with the validator that produced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Checkpoint(usize);

impl Checkpoint {
    /// Number of committed events represented by this checkpoint.
    pub const fn history_len(self) -> usize {
        self.0
    }
}

/// Compiler for complete owned source rules sharing one canonical store.
pub struct ValidatorBuilder<'arena> {
    store: CanonicalStore<'arena>,
    rules: Vec<CompiledRule<'arena>>,
}

impl<'arena> ValidatorBuilder<'arena> {
    /// Creates an empty builder whose compiled values live in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            store: CanonicalStore::new(arena),
            rules: Vec::new(),
        }
    }

    /// Compiles and appends one complete source rule.
    ///
    /// The source expression is context-free. Its head creates a temporary variable environment,
    /// its tail is compiled under that environment, and only the resulting canonical rule is kept.
    pub fn add_rule(&mut self, source: Rule) -> Result<&mut Self, CompileError> {
        let rule_index = RuleIndex::from_zero_based(self.rules.len());
        let compiled = compile_rule(&mut self.store, rule_index, &source)?;
        self.rules.push(compiled);
        Ok(self)
    }

    /// Finishes compilation with an empty committed history.
    pub fn finish(self) -> Validator<'arena> {
        Validator {
            store: self.store,
            rules: self.rules,
            history: Vec::new(),
        }
    }
}

/// Stateful validator for a fixed ordered rule set.
pub struct Validator<'arena> {
    store: CanonicalStore<'arena>,
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
            let Some(substitution) = rule.head.match_candidate(&request.event) else {
                continue;
            };
            let accepted = accepts(
                &mut self.store,
                rule.tail,
                self.history.iter(),
                &substitution,
            );
            let violated = match rule.mode {
                RuleMode::Require => !accepted,
                RuleMode::Forbid => accepted,
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

    /// Captures this validator's current history position.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint(self.history.len())
    }

    /// Truncates committed history to `checkpoint`.
    ///
    /// # Panics
    ///
    /// Panics if the checkpoint names a future history position. Checkpoints are validator-local;
    /// the API intentionally carries no owner backreference.
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        assert!(
            checkpoint.0 <= self.history.len(),
            "invalid validator checkpoint"
        );
        self.history.truncate(checkpoint.0);
    }
}
