//! Static analysis of history policies by inclusion between rule tails.
//!
//! A rule denies a candidate event when its head matches the candidate and the history before it
//! lies in its tail language (`Forbid`) or outside it (`Require`). Tails compare history events
//! with constants and with the candidate's components, so their languages depend on the candidate.
//! [`PolicyAnalyzer`] decides, for every candidate at once, whether the denials of one rule are
//! covered by those of others, whether one policy is at least as strict as another, and whether a
//! rule can fire at all.
//!
//! Each question reduces to inclusions `left ⊑ right` between tails under a constraint on the
//! candidate. An inclusion is decided by a breadth-first search for a counterexample among the
//! Brzozowski derivatives of `left ∩ ¬right`:
//!
//! - each search state branches over finitely many classes of events: per component, one of the
//!   values that the state's tests mention, or any other value;
//! - the constraint on the candidate is split only where a test compares one of its components
//!   with a constant;
//! - residuals stay in a normal form given by four local rules (flat, sorted, duplicate-free unions
//!   and intersections without their unit, collapsing to their absorber when it, or a child beside
//!   its complement, occurs; `¬∅ = Σ*`, `¬Σ* = ∅`, `¬¬x = x`; binary concatenation without `∅` or
//!   `ε` factors; `∅* = ε* = ε`, `(Σ*)* = Σ*`). With exactly these rules every expression has
//!   finitely many iterated derivatives, so the search terminates;
//! - states are compared by identity only, so a reported counterexample is a shortest one.
//!
//! A component is assumed to have more values than the rules mention, unless [`Domains`] declares
//! its values. Counterexamples name each component either by a constant or by a numbered fresh
//! value ([`Value`]), because a generic [`Event`](history_syntax::Event) cannot be built from
//! components.
//!
//! Rules are validated and lowered by [`junco_core::flatten_rule`], as for the runtime. The
//! analysis itself is not verified.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

mod analyzer;
mod constraint;
mod expression;
mod search;

#[cfg(test)]
mod tests;

pub use analyzer::{
    Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, Value, Verdict,
};
pub use search::{SearchOptions, SearchStats};
