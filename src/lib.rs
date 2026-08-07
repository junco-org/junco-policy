#![deny(missing_docs)]
//! Exact capability policy validation with finite-product past regular expressions.
//!
//! A policy rule has a candidate-only [`Head`], a complete-history regex built through
//! [`RuleSyntax`], and a [`RuleMode`]. Matching the head binds typed variables. The tail then sees
//! only grants committed before the candidate. `Require` demands membership in the tail language;
//! `Forbid` demands non-membership.
//!
//! Internally, constants and nodes are allocated in a caller-owned [`Bump`]. Boolean tests and
//! normalized regex nodes are hashconsed, giving structurally equal residuals one reference-like
//! canonical handle. Exact Brzozowski derivatives evaluate history while smart constructors apply
//! the finite ACI normalization quotient. Public syntax handles carry arena-backed context and rule
//! identities so variables cannot escape their rule scope.
//!
//! # Example
//!
//! ```rust
//! use rust_validator::{
//!     Action, AtomPattern, Bump, Comparison, ComponentPattern, Decision, Event, Head, Request,
//!     RuleMode, Validator,
//! };
//!
//! let arena = Bump::new();
//! let mut builder = Validator::builder(&arena);
//! builder.add_rule(
//!     RuleMode::Require,
//!     Head::new(
//!         ComponentPattern::variable("actor"),
//!         ComponentPattern::constant(Action::Stage),
//!         ComponentPattern::variable("target"),
//!     ),
//!     |syntax| {
//!         let actor_edit = syntax.atom(
//!             Comparison::Eq,
//!             AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
//!         )?;
//!         let actor_edit = syntax.test(actor_edit);
//!         let prefix = syntax.all();
//!         Ok(syntax.concat([prefix, actor_edit]))
//!     },
//! )?;
//!
//! let mut validator = builder.finish();
//! let edit = Request::new(Event::new("alice", Action::Edit, ["src", "a.rs"]), ());
//! assert!(validator.check(edit).is_grant());
//! let stage = Request::new(Event::new("alice", Action::Stage, ["src", "a.rs"]), ());
//! assert!(matches!(validator.check(stage), Decision::Grant(_)));
//! # Ok::<(), rust_validator::CompileError>(())
//! ```

mod model;
mod syntax;
mod validator;

pub use bumpalo::Bump;
pub use model::{Action, Event, Grant, Principal, Request, Resource};
pub use syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, Regex, RuleMode, RuleSyntax, Test,
};
pub use validator::{
    Checkpoint, CompileError, Decision, Denial, RuleIndex, Validator, ValidatorBuilder,
};
