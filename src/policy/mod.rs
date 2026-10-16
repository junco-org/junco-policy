//! A policy kernel: the pieces every trace policy is built from, and the policies built on them.
//!
//! A policy is a table of declarative [`crate::Rule`] values whose tails are past-regexes over
//! committed history, each deny cell paired with a diagnostic that renders the exact
//! precondition/fix strings the consumer boundary surfaces. The kernel is policy-agnostic:
//! [`atoms`] are the one-event tests over the head-bound principal and resource, [`language`] the
//! two tail shapes that classify a resource's history, [`rule`] the rule/diagnostic pairing over a
//! per-policy context, [`evaluate`] the loop that walks a table, and [`decision`] the verdict it
//! returns.
//!
//! [`git`] is the built-in policy: multi-agent git legality. [`TracePolicy`] opens the same
//! compile-once table to caller-assembled rules.

mod atoms;
mod decision;
mod evaluate;
mod language;
mod rule;
mod trace;

pub mod git;

pub use decision::PolicyDecision;
pub use trace::{TraceCursor, TraceDiagnostic, TracePolicy, TraceRule};

#[cfg(test)]
mod tests;
