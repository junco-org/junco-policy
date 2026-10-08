//! Ownership locks expressed as a native trace policy over the [`crate::policy`] kernel.
//!
//! A resource has two independent claims, each folded from committed history:
//!
//! - its **owner**: the principal of the last `edit`, cleared by `release` and `remove`;
//! - its **last reader**: the principal of the last `read`, cleared only by `remove`.
//!
//! `edit` and `remove` are denied while another principal owns the resource or last read it;
//! `release` is denied only while another principal owns it. `read` always grants. Owner denials
//! precede reader denials. [`LockPolicy`] compiles this five-rule table once and retains its
//! canonical nodes and evaluator caches across decisions.

use crate::policy::atoms::{action_is, principal_is, resource_is};
use crate::policy::decision::PolicyDecision;
use crate::policy::evaluate::CompiledPolicy;
use crate::policy::language::last_state_change;
use crate::policy::rule::{PolicyRule, forbid};
use crate::{Action, Bump, Comparison, Event, RegexExpr, TestExpr};

/// Everything a lock denial renders from.
struct LockContext {
    principal: String,
    resource: String,
    action: Action,
    owner: String,
    reader: String,
}

/// An on-`r` `action` by a principal other than the acting one.
fn foreign_on_r(action: Action) -> TestExpr {
    TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(action, Comparison::Eq),
        principal_is(Comparison::Neq),
    ])
}

/// Another principal's `edit` is the last owner-changing event on `r`.
fn owned_by_other() -> RegexExpr {
    let changes = [Action::Edit, Action::Release, Action::Remove];
    last_state_change(foreign_on_r(Action::Edit), stable(&changes))
}

/// Another principal's `read` is the last reader-changing event on `r`.
fn read_by_other() -> RegexExpr {
    let changes = [Action::Read, Action::Remove];
    last_state_change(foreign_on_r(Action::Read), stable(&changes))
}

/// An event that is off `r` or is none of `changes`.
fn stable(changes: &[Action]) -> TestExpr {
    TestExpr::or([
        resource_is(Comparison::Neq),
        TestExpr::and(
            changes
                .iter()
                .map(|action| action_is(action.clone(), Comparison::Neq)),
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
fn lock_rules() -> Vec<PolicyRule<LockContext>> {
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
fn lock_context(history: &[Event], candidate: &Event) -> LockContext {
    let mut owner = None;
    let mut reader = None;
    for event in history
        .iter()
        .filter(|event| event.resource == candidate.resource)
    {
        match event.action {
            Action::Read => reader = Some(event.principal.as_str()),
            Action::Edit => owner = Some(event.principal.as_str()),
            Action::Release => owner = None,
            Action::Remove => (owner, reader) = (None, None),
        }
    }
    let name = |claim: Option<&str>| claim.unwrap_or("another principal").to_string();
    LockContext {
        principal: candidate.principal.as_str().to_string(),
        resource: candidate.resource.to_string(),
        action: candidate.action.clone(),
        owner: name(owner),
        reader: name(reader),
    }
}

/// Compiled ownership-lock trace policy reusable across candidate decisions.
///
/// [`LockPolicy::decide`] accepts an externally owned committed history so callers can preserve
/// append-on-grant semantics while this value retains canonical syntax and derivative caches.
pub struct LockPolicy<'arena> {
    compiled: CompiledPolicy<'arena, LockContext>,
}

impl<'arena> LockPolicy<'arena> {
    /// Builds and compiles the static lock policy in `arena`.
    pub fn new(arena: &'arena Bump) -> Self {
        Self {
            compiled: CompiledPolicy::new(arena, lock_rules())
                .expect("static lock policy rules compile"),
        }
    }

    /// Decides one candidate against `history`, reusing the compiled table and evaluator caches.
    pub fn decide(&mut self, history: &[Event], candidate: &Event) -> PolicyDecision {
        self.compiled
            .decide(history, candidate, || lock_context(history, candidate))
    }
}

/// Decides one candidate with a one-shot lock policy.
///
/// Prefer retaining [`LockPolicy`] for repeated decisions; this compiles the policy per call.
pub fn lock_decision(history: &[Event], candidate: &Event) -> PolicyDecision {
    let arena = Bump::new();
    LockPolicy::new(&arena).decide(history, candidate)
}

#[cfg(test)]
mod tests;
