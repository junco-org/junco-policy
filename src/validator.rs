//! Policy compilation, stateful authorization, and rollback.
//!
//! Source rules are complete owned values. `ValidatorBuilder` compiles each complete rule by
//! explicitly passing the canonical store and a temporary variable environment to compiler
//! functions. The executable validator retains only canonical compiled rules and committed history.

use bumpalo::Bump;
use thiserror::Error;

use crate::model::{Event, Grant, Request};
use crate::syntax::{CanonicalStore, CompiledRule, Rule, RuleMode, accepts, compile_rule};

/// Rule-compilation failure detected before a validator can execute.
///
/// `ValidatorBuilder::add_rule` compiles exactly one source rule, so the caller already knows which
/// rule failed. Errors contain only the local malformed name rather than a derived vector position.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum CompileError {
    /// One variable name occurs in different product components in the same rule.
    #[error("variable {name:?} occurs in different product components")]
    VariableComponentConflict {
        /// Conflicting variable name.
        name: String,
    },
    /// A tail references a variable that its head does not bind.
    #[error("tail variable {name:?} is not bound by the head")]
    UnboundVariable {
        /// Missing variable name.
        name: String,
    },
}

/// Diagnostic returned when the first matching rule is violated.
///
/// The denial describes the violated relationship without deriving a positional identifier for the
/// internal rule vector. Applications needing rule identity should carry an explicit domain label
/// in their policy model rather than depending on storage order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial {
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

/// Owned snapshot of committed event history.
///
/// A checkpoint contains the state to restore rather than a position requiring validation against a
/// particular vector. Snapshot creation is linear in history length; rollback moves the snapshot
/// into the validator without an index, range invariant, or owner backreference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checkpoint {
    history: Vec<Event>,
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
        let compiled = compile_rule(&mut self.store, &source)?;
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
        for rule in self.rules.iter().copied() {
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
                let relation = match rule.mode {
                    RuleMode::Require => "does not satisfy required",
                    RuleMode::Forbid => "satisfies forbidden",
                };
                return Decision::Denied(Denial {
                    mode: rule.mode,
                    event: request.event,
                    message: format!("committed history {relation} past-regex rule"),
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

    /// Clones committed history into an owned rollback snapshot.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            history: self.history.clone(),
        }
    }

    /// Restores the exact history captured by `checkpoint`.
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        self.history = checkpoint.history;
    }
}
