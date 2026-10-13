#![deny(missing_docs)]
//! Exact capability policy validation with finite-product past regular expressions.
//!
//! Policies are assembled from owned, context-free [`Rule`], [`TestExpr`], and [`RegexExpr`]
//! values over a caller-chosen [`Event`] type. Events are compact `Copy` values: caller-owned
//! enums, or finite Frunk [`Coproduct`] unions of payload structs whose principal, action, and
//! resource projections share component types. [`GitEvent`] is the built-in Git representation.
//! Labels for diagnostics live outside the evaluator; equality is the event's full value equality.
//!
//! `ValidatorBuilder` compiles each complete rule by passing a shared canonical store and a
//! temporary variable environment explicitly. Boolean tests and normalized regex nodes are
//! hashconsed in a caller-owned [`Bump`] arena, giving structurally equal expressions one
//! reference-like canonical handle. The executable [`Validator`] retains only the canonical store,
//! runtime rules, and a tracked committed [`History`]; each runtime rule keeps a small bounded
//! cache of evaluated residuals so unchanged or append-extended histories fold only new events.
//!
//! # Example
//!
//! ```rust
//! use junco_policy::{
//!     Action, AtomPattern, Bump, Comparison, ComponentPattern, Decision, GitEvent, Head,
//!     RegexExpr, Request, Rule, RuleMode, TestExpr, Validator, git_event,
//! };
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
//! let rule: Rule<GitEvent<Actor, Path>> = Rule::new(
//!     RuleMode::Require,
//!     Head::new(
//!         ComponentPattern::variable("actor"),
//!         ComponentPattern::constant(Action::Stage),
//!         ComponentPattern::variable("target"),
//!     ),
//!     tail,
//! );
//!
//! let arena = Bump::new();
//! let mut builder = Validator::builder(&arena);
//! builder.add_rule(rule)?;
//! let mut validator = builder.finish();
//!
//! let stage = git_event(alice, Action::Stage, src_a);
//! assert!(!validator.permits(&stage));
//! let edit = Request::new(git_event(alice, Action::Edit, src_a), ());
//! assert!(validator.check(edit).is_grant());
//! assert!(matches!(validator.check(Request::new(stage, ())), Decision::Grant(_)));
//! # Ok::<(), junco_policy::CompileError>(())
//! ```

mod history;
mod model;
mod policy;
mod syntax;
mod validator;

pub use bumpalo::Bump;
pub use frunk_core::Coprod;
pub use frunk_core::coproduct::{CNil, Coproduct};
pub use history::{Checkpoint, History};
pub use model::{
    Action, Event, GitCommit, GitEvent, GitOperation, Grant, MessageId, Request, git_event,
};
pub use policy::{
    PolicyDecision,
    git::{GitPolicy, git_decision},
};
pub use syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
pub use validator::{CompileError, Decision, Denial, Validator, ValidatorBuilder};
