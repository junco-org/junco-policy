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
//! derivatives of `left ∩ ¬right`. These are the runtime's own: the difference is compiled into a
//! [`history_semantics::SymbolicLanguage`] and stepped by its verified symbolic derivatives and
//! successor interpretation.
//!
//! - each search state branches over finitely many classes of events: per component, one of the
//!   values that its derivative's atoms mention, or any other value. A class's successor is the
//!   runtime's successor for the truth values the atoms take on it;
//! - the constraint on the candidate is split only where an atom compares one of its components
//!   with a constant;
//! - the runtime keeps residuals in a normal form whose unions and intersections are flat, sorted
//!   and duplicate-free, so every residual has finitely many iterated derivatives and the search
//!   terminates;
//! - states are compared by identity only, so a reported counterexample is a shortest one.
//!
//! A component is assumed to have more values than the rules mention, unless [`Domains`] declares
//! its values. Counterexamples name each component either by a constant or by a numbered fresh
//! value ([`Value`]), because a generic [`Event`](history_syntax::Event) cannot be built from
//! components.
//!
//! Rules are validated and lowered by [`junco_core::flatten_rule`] and [`junco_core::lower_flat`],
//! as for the runtime. Each search compiles one graph that may be charged
//! [`SearchOptions::graph_bytes`], 16 MiB by default; a search that exceeds it is reported as
//! [`Inclusion::Exhausted`]. The classes of events and the search are not verified.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

mod analyzer;
mod constraint;
mod search;
mod tables;

#[cfg(test)]
mod tests;

pub use analyzer::{
    Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, Value, Verdict,
};
pub use search::{SearchOptions, SearchStats};
