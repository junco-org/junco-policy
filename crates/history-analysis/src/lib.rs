//! Static analysis of history policies by inclusion between rule tails.
//!
//! Tails compare history events with constants and with the candidate's components, so their
//! languages depend on the candidate. [`PolicyAnalyzer`] decides, for every candidate matching
//! a head, whether every history in one tail is in another.
//!
//! An inclusion `left ⊑ right` under a constraint on the candidate is decided by a breadth-first
//! search for a counterexample among the derivatives of `left ∩ ¬right`. These are the runtime's
//! own: the difference is compiled into a
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
//! - a residual intersects the parts it requires with the complements of the pieces it avoids,
//!   like a pair of a state and a macrostate, and the search prunes with antichains up to a
//!   syntactic simulation, a cheap relation between residuals that implies inclusion: it does not
//!   insert a state whose residual is dead, some part having each of its pieces below an avoided
//!   one, or that an inserted state subsumes, entailing its constraint, requiring all of its parts
//!   and avoiding a piece above each of its pieces. Inserted states are never removed, so a
//!   reported counterexample is a shortest one.
//!
//! A component is assumed to have more values than the rules mention, unless [`Domains`] declares
//! its values. Counterexamples name each component either by a constant or by a numbered fresh
//! value ([`Value`]), because a generic [`Event`](history_syntax::Event) cannot be built from
//! components.
//!
//! Rules are validated and lowered from borrowed inputs by
//! [`junco_core::flatten::flatten_rule_parts`] and [`junco_core::lower_flat`], without cloning
//! caller-owned syntax. Each search compiles one graph that may be charged 16 MiB; a search that
//! exceeds it is reported as [`Inclusion::Exhausted`]. Verus links the native search and
//! reconstruction to typed tail inclusion under the documented native laws and sufficient
//! resource-capacity preconditions.

#![no_std]
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![deny(missing_docs)]

extern crate alloc;

#[cfg(feature = "runtime")]
mod analyzer;
#[cfg(feature = "runtime")]
mod constraint;
#[cfg(feature = "runtime")]
mod native;
#[cfg(feature = "runtime")]
mod prune;
#[cfg(feature = "runtime")]
mod search;
#[cfg(feature = "runtime")]
mod simulation;
#[cfg(feature = "runtime")]
mod tables;

#[cfg(all(test, feature = "runtime"))]
mod tests;

#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub mod verify;

#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub use native::{
    hash_coherent as native_hash_coherent, key_obligations as native_key_obligations,
};

#[cfg(feature = "runtime")]
pub use analyzer::{Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, Value};
