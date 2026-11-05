#![deny(missing_docs)]
//! Ownership-lock policies backed by the shared `history-semantics` engine.
//!
//! [`LockEvent`] carries the caller's compact principal and resource identities. [`LockPolicy`]
//! retains the compiled seven-rule ownership-lock table.
//! [`AgentPolicy`] decides past-time rules over classified observations.
//! Generic DSL APIs come from `history_syntax`, histories from `history_store`, and validators from `history_semantics`.
//!

mod model;
mod policy;

pub use model::{Action, LockEvent};
pub use policy::agent::{
    AgentAction, AgentDenial, AgentEvent, AgentPolicy, AgentRule, AgentRuleSet, Label,
};
pub use policy::lock::LockPolicy;
