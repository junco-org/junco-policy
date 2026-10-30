#![deny(missing_docs)]
//! Ownership-lock policies backed by the shared `history-semantics` engine.
//!
//! [`LockEvent`] carries the caller's compact principal and resource identities. [`LockPolicy`]
//! retains the compiled five-rule ownership-lock table; [`lock_decision`] evaluates it once.
//! Generic DSL APIs come from `history_syntax`, histories from `history_store`, and validators from `history_semantics`.
//!
//! # Example
//!
//! ```rust
//! use std::sync::Arc;
//! use history_syntax::{
//!     AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
//! };
//! use junco_core::Request;
//! use history_store::Store;
//! use history_semantics::{Decision, Validator};
//! use junco_policy::{Action, LockEvent};
//!
//! /// Caller-assigned actor identity; its label lives outside the evaluator.
//! #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
//! struct Actor(u32);
//! /// Caller-assigned resource identity.
//! #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
//! struct Path(u32);
//!
//! let alice = Actor(1);
//! let src_a = Path(10);
//!
//! let principal = TestExpr::atom(
//!     Comparison::Eq,
//!     AtomPattern::Principal(ComponentPattern::variable("actor")),
//! );
//! let action = TestExpr::atom(
//!     Comparison::Eq,
//!     AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
//! );
//! let resource = TestExpr::atom(
//!     Comparison::Eq,
//!     AtomPattern::Resource(ComponentPattern::variable("target")),
//! );
//! let matching_edit = RegexExpr::test(TestExpr::and([principal, action, resource]));
//! let tail = RegexExpr::concat([RegexExpr::all(), matching_edit]);
//! let rule: Rule<LockEvent<Actor, Path>> = Rule::new(
//!     RuleMode::Require,
//!     Head::new(
//!         ComponentPattern::variable("actor"),
//!         ComponentPattern::constant(Action::Release),
//!         ComponentPattern::variable("target"),
//!     ),
//!     tail,
//! );
//!
//! let store = Arc::new(Store::new()?);
//! let mut builder = Validator::builder(store);
//! builder.add_rule(rule)?;
//! let mut validator = builder.finish()?;
//!
//! let release = LockEvent::new(alice, Action::Release, src_a);
//! assert!(!validator.permits(&release)?);
//! let edit = Request::new(LockEvent::new(alice, Action::Edit, src_a), ());
//! assert!(validator.check(edit)?.is_grant());
//! assert!(matches!(validator.check(Request::new(release, ()))?, Decision::Grant(_)));
//! # Ok::<(), history_semantics::PolicyError>(())
//! ```

mod model;
mod policy;

pub use model::{Action, LockEvent};
pub use policy::lock::{LockPolicy, lock_decision};
