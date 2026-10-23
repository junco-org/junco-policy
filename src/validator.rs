//! Policy compilation, stateful authorization, and rollback.
//!
//! Source rules are complete owned values. `ValidatorBuilder` resolves each rule through the
//! canonical store and a temporary variable environment. The executable validator retains only
//! canonical runtime rules and its tracked committed [`History`].

use bumpalo::Bump;
use thiserror::Error;

use crate::history::{Checkpoint, History};
use crate::model::{Event, Grant, Request};
use crate::policy::agent::{AgentAction, AgentEvent, Label};
use crate::syntax::{CanonicalStore, Rule, RuleMode, RuntimeRule, compile_rule};

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
pub struct Denial<E: Event> {
    /// Whether the violated rule required or forbade its tail language.
    pub mode: RuleMode,
    /// Candidate event that was denied and was not appended to history.
    pub event: E,
    /// Human-readable explanation of the failed history relation.
    pub message: String,
}

/// Result of checking one capability request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<E: Event, M> {
    /// Request was accepted and appended to committed history.
    Grant(Grant<E, M>),
    /// Request was rejected atomically; committed history is unchanged.
    Denied(Denial<E>),
}

impl<E: Event, M> Decision<E, M> {
    /// Returns `true` exactly for [`Decision::Grant`].
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

/// Resolves complete source rules into runtime rules sharing one canonical store.
pub struct ValidatorBuilder<'arena, E>
where
    E: Event + 'arena,
{
    store: CanonicalStore<'arena, E>,
    rules: Vec<RuntimeRule<'arena, E>>,
}

impl<'arena, E> ValidatorBuilder<'arena, E>
where
    E: Event + 'arena,
{
    /// Creates an empty builder whose resolved values live in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            store: CanonicalStore::new(arena),
            rules: Vec::new(),
        }
    }

    /// Resolves and appends one complete source rule.
    ///
    /// The source expression is context-free. Its head creates a temporary variable environment,
    /// and only the resulting runtime rule is kept.
    pub fn add_rule(&mut self, source: Rule<E>) -> Result<&mut Self, CompileError> {
        let runtime_rule = compile_rule(&mut self.store, &source)?;
        self.rules.push(runtime_rule);
        Ok(self)
    }

    /// Finishes compilation with an empty committed history.
    pub fn finish(self) -> Validator<'arena, E> {
        Validator {
            store: self.store,
            rules: self.rules,
            history: History::new(),
        }
    }
}

/// Stateful validator for a fixed ordered rule set.
pub struct Validator<'arena, E>
where
    E: Event + 'arena,
{
    store: CanonicalStore<'arena, E>,
    rules: Vec<RuntimeRule<'arena, E>>,
    history: History<E>,
}

impl<'arena, E> Validator<'arena, E>
where
    E: Event + 'arena,
{
    /// Starts compiling a validator in `arena`.
    pub fn builder(arena: &'arena Bump) -> ValidatorBuilder<'arena, E> {
        ValidatorBuilder::new(arena)
    }

    /// Checks one request against all rules in source order.
    ///
    /// A nonmatching head does not fire. For a matching head, `Require` denies when the complete
    /// committed history is outside the tail language, while `Forbid` denies when it is inside.
    /// The first violation wins. On success the candidate is appended once and its metadata is
    /// preserved in the returned grant.
    pub fn check<M>(&mut self, request: Request<E, M>) -> Decision<E, M> {
        if let Some(mode) = self.first_violation(&request.event) {
            let relation = match mode {
                RuleMode::Require => "does not satisfy required",
                RuleMode::Forbid => "satisfies forbidden",
            };
            return Decision::Denied(Denial {
                mode,
                event: request.event,
                message: format!("committed history {relation} past-regex rule"),
            });
        }

        self.history.push(request.event);
        Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        })
    }

    /// Returns whether [`Validator::check`] would grant `candidate`, without appending it.
    ///
    /// Evaluation is identical to `check`; repeated calls over an unchanged or append-extended
    /// history resume each rule's cached residual and fold only newly committed events.
    pub fn permits(&mut self, candidate: &E) -> bool {
        self.first_violation(candidate).is_none()
    }

    /// Returns the mode of the first rule, in source order, that `candidate` violates.
    fn first_violation(&mut self, candidate: &E) -> Option<RuleMode> {
        for rule in &mut self.rules {
            let Some(accepted) = rule.accepts_history(&mut self.store, &self.history, candidate)
            else {
                continue;
            };
            let violated = match rule.mode {
                RuleMode::Require => !accepted,
                RuleMode::Forbid => accepted,
            };
            if violated {
                return Some(rule.mode);
            }
        }
        None
    }

    /// Returns committed grants' events in exact acceptance order.
    pub fn history(&self) -> &[E] {
        self.history.as_slice()
    }

    /// Captures the current committed-history position in constant time.
    pub fn checkpoint(&self) -> Checkpoint {
        self.history.checkpoint()
    }

    /// Restores history to a previously captured position of this validator.
    ///
    /// # Panics
    ///
    /// Panics if `checkpoint` belongs to another validator's history or lies beyond the current
    /// history; history is unchanged in that case.
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        self.history.rollback(checkpoint);
    }
}

impl<'arena, P: Label, C: Label> Validator<'arena, AgentEvent<P, C>> {
    /// Appends an operator's declassification of `class` for `principal` and returns the
    /// checkpoint taken before it, so [`Validator::rollback`] undoes the declassification.
    /// Returns `None`, with history unchanged, when a rule refuses it (see
    /// [`crate::AgentRule::undeclassifiable`]).
    pub fn declassify(&mut self, principal: P, class: C) -> Option<Checkpoint> {
        let before = self.checkpoint();
        let declassify = AgentEvent::new(principal, AgentAction::Declassify, class);
        self.check(Request::new(declassify, ()))
            .is_grant()
            .then_some(before)
    }
}
