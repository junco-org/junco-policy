//! A policy kernel: the pieces every trace policy is built from, and the policies built on them.
//!
//! A policy is a table of declarative [`crate::Rule`] values whose tails are past-regexes over
//! committed history, each deny cell paired with a diagnostic that renders the exact
//! precondition/fix strings the consumer boundary surfaces. The kernel is policy-agnostic:
//! [`atoms`] are the one-event tests over the head-bound principal and resource, [`language`] the
//! tail shape that classifies a resource's history, [`rule`] the rule/diagnostic pairing over a
//! per-policy context, [`evaluate`] the loop that walks a table, and [`decision`] the verdict it
//! returns.
//!
//! [`lock`] is the one policy built on it today: multi-agent file ownership.

mod atoms;
mod decision;
mod evaluate;
mod language;
mod rule;

pub mod lock;

pub use decision::PolicyDecision;

#[cfg(test)]
mod tests;
