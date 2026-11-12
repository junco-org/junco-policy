//! Ownership locks expressed as a native trace policy over `history-semantics`.
//!
//! A resource has two independent claims, each folded from committed history:
//!
//! - its **owner**: the principal of the last `edit`, cleared by `release` and `remove`;
//! - its **last reader**: the principal of the last `read`, cleared only by `remove`.
//!
//! `edit` and `remove` are denied while another principal owns the resource or last read it;
//! `release` is denied only while another principal owns it. `read` always grants. A foreign
//! `edit` also blocks `edit` and `remove` until the acting principal reads the resource again;
//! `release` does not restore freshness, and `remove` resets it. Owner denials precede freshness
//! and reader denials. [`LockPolicy`] compiles this seven-rule table once and retains its
//! evaluator caches and a per-resource claim table, so denial text costs the events appended
//! since the last denial.

use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;

use history_semantics::PolicyDecision;
use history_semantics::policy::{
    CompiledPolicy, PolicyRule, action_is, forbid, last_state_change, principal_is, resource_is,
};
use history_store::{History, Store};
use history_syntax::{Comparison, RegexExpr, TestExpr};
use junco_core::{CompileError, HistoryError};

use crate::{Action, LockComponent, LockEvent};

/// Everything a lock denial renders from.
struct LockContext {
    principal: String,
    resource: String,
    action: Action,
    owner: String,
    reader: String,
}

/// An on-`r` `action` by a principal other than the acting one.
fn foreign_on_r<P, R>(action: Action) -> TestExpr<LockEvent<P, R>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(LockComponent::Action(action), Comparison::Eq),
        principal_is(Comparison::Neq),
    ])
}

/// Another principal's `edit` is the last owner-changing event on `r`.
fn owned_by_other<P, R>() -> RegexExpr<LockEvent<P, R>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    let changes = [Action::Edit, Action::Release, Action::Remove];
    last_state_change(foreign_on_r(Action::Edit), stable(&changes))
}

/// Another principal's `read` is the last reader-changing event on `r`.
fn read_by_other<P, R>() -> RegexExpr<LockEvent<P, R>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    let changes = [Action::Read, Action::Remove];
    last_state_change(foreign_on_r(Action::Read), stable(&changes))
}

/// Another principal edited `r` after the acting principal last read or edited it.
fn stale_view<P, R>() -> RegexExpr<LockEvent<P, R>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    last_state_change(
        foreign_on_r(Action::Edit),
        TestExpr::and([
            stable(&[Action::Edit, Action::Remove]),
            TestExpr::or([
                resource_is(Comparison::Neq),
                action_is(LockComponent::Action(Action::Read), Comparison::Neq),
                principal_is(Comparison::Neq),
            ]),
        ]),
    )
}

/// An event that is off `r` or is none of `changes`.
fn stable<P, R>(changes: &[Action]) -> TestExpr<LockEvent<P, R>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    TestExpr::or([
        resource_is(Comparison::Neq),
        TestExpr::and(
            changes
                .iter()
                .map(|&action| action_is(LockComponent::Action(action), Comparison::Neq)),
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

fn stale_denial(context: &LockContext) -> (String, Vec<String>) {
    let LockContext {
        principal: p,
        resource: r,
        action,
        ..
    } = context;
    (
        format!(
            "{r} was modified by another principal; {p} must read it again before it may {action} it"
        ),
        vec![format!("{p} read {r}")],
    )
}

/// The lock table: owner cells first, so the owner diagnostic wins.
fn lock_rules<P, R>() -> Vec<PolicyRule<LockEvent<P, R>, LockContext>>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    vec![
        forbid(
            LockComponent::Action(Action::Edit),
            owned_by_other(),
            Box::new(owner_denial),
        ),
        forbid(
            LockComponent::Action(Action::Release),
            owned_by_other(),
            Box::new(owner_denial),
        ),
        forbid(
            LockComponent::Action(Action::Remove),
            owned_by_other(),
            Box::new(owner_denial),
        ),
        forbid(
            LockComponent::Action(Action::Edit),
            stale_view(),
            Box::new(stale_denial),
        ),
        forbid(
            LockComponent::Action(Action::Remove),
            stale_view(),
            Box::new(stale_denial),
        ),
        forbid(
            LockComponent::Action(Action::Edit),
            read_by_other(),
            Box::new(reader_denial),
        ),
        forbid(
            LockComponent::Action(Action::Remove),
            read_by_other(),
            Box::new(reader_denial),
        ),
    ]
}

/// A resource's current owner and last reader, as the denial text names them.
#[derive(Clone, Copy)]
struct Claims<P> {
    owner: Option<P>,
    reader: Option<P>,
}

/// Per-resource claims folded from one history's committed prefix, resumed across denials.
///
/// `(id, revision)` names an append-only prefix family (truncation bumps the revision, ids are
/// never reused), so a matching key folds only `events[consumed..]`; anything else refolds
/// from the start. The reset state is correct for every history, so no `Option` is needed.
struct ClaimTable<P, R> {
    key: (usize, u64),
    consumed: usize,
    claims: HashMap<R, Claims<P>>,
}

impl<P, R> ClaimTable<P, R>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    fn new() -> Self {
        Self {
            key: (0, 0),
            consumed: 0,
            claims: HashMap::new(),
        }
    }

    /// Catches up on `history` and returns `resource`'s claims, for diagnostics only — grant and
    /// deny are entirely trace-policy driven. The arms MUST stay in lockstep with the languages.
    fn claims(&mut self, history: &History<LockEvent<P, R>>, resource: R) -> Claims<P> {
        let key = (history.id(), history.numeric().revision());
        if self.key != key {
            self.key = key;
            self.consumed = 0;
            self.claims.clear();
        }
        for event in &history.as_slice()[self.consumed..] {
            let claims = self.claims.entry(event.resource).or_insert(Claims {
                owner: None,
                reader: None,
            });
            match event.action {
                Action::Read => claims.reader = Some(event.principal),
                Action::Edit => claims.owner = Some(event.principal),
                Action::Release => claims.owner = None,
                Action::Remove => (claims.owner, claims.reader) = (None, None),
            }
        }
        self.consumed = history.len();
        self.claims.get(&resource).copied().unwrap_or(Claims {
            owner: None,
            reader: None,
        })
    }
}

/// Renders the denial context from `claims`; identities go through the caller's `Display` labels
/// here, off the grant path.
fn lock_context<P: Display, R: Display>(
    claims: Claims<P>,
    candidate: &LockEvent<P, R>,
) -> LockContext {
    let name = |claim: Option<P>| {
        claim.map_or_else(
            || "another principal".to_string(),
            |claim| claim.to_string(),
        )
    };
    LockContext {
        principal: candidate.principal.to_string(),
        resource: candidate.resource.to_string(),
        action: candidate.action,
        owner: name(claims.owner),
        reader: name(claims.reader),
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
    claims: ClaimTable<P, R>,
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
            claims: ClaimTable::new(),
        })
    }

    /// Decides one candidate against `history`, reusing the compiled table and evaluator caches.
    pub fn decide(
        &mut self,
        history: &History<LockEvent<P, R>>,
        candidate: &LockEvent<P, R>,
    ) -> Result<PolicyDecision, HistoryError> {
        let claims = &mut self.claims;
        self.compiled.decide(history, candidate, || {
            lock_context(claims.claims(history, candidate.resource), candidate)
        })
    }
}

#[cfg(test)]
mod tests;
