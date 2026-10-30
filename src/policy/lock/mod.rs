//! Ownership locks expressed as a native trace policy over `history-semantics`.
//!
//! A resource has two independent claims, each folded from committed history:
//!
//! - its **owner**: the principal of the last `edit`, cleared by `release` and `remove`;
//! - its **last reader**: the principal of the last `read`, cleared only by `remove`.
//!
//! `edit` and `remove` are denied while another principal owns the resource or last read it;
//! `release` is denied only while another principal owns it. `read` always grants. Owner denials
//! precede reader denials. [`LockPolicy`] compiles this five-rule table once and retains its
//! evaluator caches across decisions.

use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;

use history_semantics::policy::{
    CompiledPolicy, PolicyRule, action_is, forbid, last_state_change, principal_is, resource_is,
};
use history_semantics::{PolicyDecision, PolicyError};
use history_store::{History, Store};
use history_syntax::{Comparison, Event, RegexExpr, TestExpr};
use junco_core::{CompileError, HistoryError};

use crate::{Action, LockEvent};

/// Everything a lock denial renders from.
struct LockContext {
    principal: String,
    resource: String,
    action: Action,
    owner: String,
    reader: String,
}

/// An on-`r` `action` by a principal other than the acting one.
fn foreign_on_r<E: Event<Action = Action>>(action: Action) -> TestExpr<E> {
    TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(action, Comparison::Eq),
        principal_is(Comparison::Neq),
    ])
}

/// Another principal's `edit` is the last owner-changing event on `r`.
fn owned_by_other<E: Event<Action = Action>>() -> RegexExpr<E> {
    let changes = [Action::Edit, Action::Release, Action::Remove];
    last_state_change(foreign_on_r(Action::Edit), stable(&changes))
}

/// Another principal's `read` is the last reader-changing event on `r`.
fn read_by_other<E: Event<Action = Action>>() -> RegexExpr<E> {
    let changes = [Action::Read, Action::Remove];
    last_state_change(foreign_on_r(Action::Read), stable(&changes))
}

/// An event that is off `r` or is none of `changes`.
fn stable<E: Event<Action = Action>>(changes: &[Action]) -> TestExpr<E> {
    TestExpr::or([
        resource_is(Comparison::Neq),
        TestExpr::and(
            changes
                .iter()
                .map(|&action| action_is(action, Comparison::Neq)),
        ),
    ])
}

fn owner_denial(context: &LockContext) -> (String, Vec<String>) {
    let LockContext {
        principal: p,
        resource: r,
        action,
        owner: q,
        ..
    } = context;
    (
        format!("{r} is owned by {q}; {p} may read it but may not {action} it"),
        vec![format!("{q} release {r}")],
    )
}

fn reader_denial(context: &LockContext) -> (String, Vec<String>) {
    let LockContext {
        principal: p,
        resource: r,
        action,
        reader: s,
        ..
    } = context;
    (
        format!("{r} was last read by {s}; {p} must read it before it may {action} it"),
        vec![format!("{p} read {r}")],
    )
}

/// The five-rule lock table: owner cells first, so the owner diagnostic wins.
fn lock_rules<E: Event<Action = Action>>() -> Vec<PolicyRule<E, LockContext>> {
    vec![
        forbid(Action::Edit, owned_by_other(), Box::new(owner_denial)),
        forbid(Action::Release, owned_by_other(), Box::new(owner_denial)),
        forbid(Action::Remove, owned_by_other(), Box::new(owner_denial)),
        forbid(Action::Edit, read_by_other(), Box::new(reader_denial)),
        forbid(Action::Remove, read_by_other(), Box::new(reader_denial)),
    ]
}

/// Folds `history` to `resource`'s current owner and last reader, for diagnostics only — grant
/// and deny are entirely trace-policy driven. Its arms MUST stay in lockstep with the languages.
///
/// Principal and resource identities are rendered through the caller's `Display` labels here, off
/// the grant path.
fn lock_context<E>(history: &[E], candidate: &E) -> LockContext
where
    E: Event<Action = Action>,
    E::Principal: Display,
    E::Resource: Display,
{
    let resource = candidate.resource();
    let mut owner = None;
    let mut reader = None;
    for event in history.iter().filter(|event| event.resource() == resource) {
        match event.action() {
            Action::Read => reader = Some(event.principal()),
            Action::Edit => owner = Some(event.principal()),
            Action::Release => owner = None,
            Action::Remove => (owner, reader) = (None, None),
        }
    }
    let name = |claim: Option<E::Principal>| {
        claim.map_or_else(
            || "another principal".to_string(),
            |claim| claim.to_string(),
        )
    };
    LockContext {
        principal: candidate.principal().to_string(),
        resource: resource.to_string(),
        action: candidate.action(),
        owner: name(owner),
        reader: name(reader),
    }
}

/// Compiled ownership-lock trace policy reusable across candidate decisions.
///
/// [`LockPolicy::decide`] accepts an externally owned committed [`History`] in the same store.
/// Decisions do not append events; the caller records successful operations explicitly.
pub struct LockPolicy<P, R>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    compiled: CompiledPolicy<LockEvent<P, R>, LockContext>,
}

impl<P, R> LockPolicy<P, R>
where
    P: Copy + Debug + Eq + Hash + Display,
    R: Copy + Debug + Eq + Hash + Display,
{
    /// Builds and compiles the static lock policy in `store`.
    pub fn new(store: Arc<Store<LockEvent<P, R>>>) -> Result<Self, CompileError> {
        Ok(Self {
            compiled: CompiledPolicy::new(store, lock_rules())?,
        })
    }

    /// Decides one candidate against `history`, reusing the compiled table and evaluator caches.
    pub fn decide(
        &mut self,
        history: &History<LockEvent<P, R>>,
        candidate: &LockEvent<P, R>,
    ) -> Result<PolicyDecision, HistoryError> {
        self.compiled.decide(history, candidate, || {
            lock_context(history.as_slice(), candidate)
        })
    }
}

/// Decides one candidate with a one-shot lock policy.
///
/// Prefer retaining [`LockPolicy`] for repeated decisions; this compiles the policy per call.
pub fn lock_decision<P, R>(
    history: &History<LockEvent<P, R>>,
    candidate: &LockEvent<P, R>,
) -> Result<PolicyDecision, PolicyError>
where
    P: Copy + Debug + Eq + Hash + Display,
    R: Copy + Debug + Eq + Hash + Display,
{
    let mut policy = LockPolicy::new(history.store().clone())?;
    Ok(policy.decide(history, candidate)?)
}

#[cfg(test)]
mod tests;
