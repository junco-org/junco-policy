//! R4: the hypothesis bundles every monitor and analyzer guarantee assumes about its event type
//! (plan S4, decision 4). The concrete witnesses (`junco_core::verify::hypotheses`,
//! `history_syntax::verify::events`) prove every conjunct except `hash_coherent`, which they take
//! as their only premise.

use crate::spec::semantics::*;
use core::hash::Hash;
use history_syntax::Event;
use history_syntax::spec::events::event_laws;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// The single uninterpreted hashing hypothesis: `K`'s `Hash`/`Eq` are faithful to `eq_spec`, so
/// the `external_body` hash containers behave as maps on `eq_spec` classes. Semantically this is
/// vstd's key model (`vstd::std_specs::hash::obeys_key_model`), which exists only with vstd's
/// `std` feature; it stays uninterpreted here so every configuration compiles. Nothing discharges
/// it for a user component type: the reviewer theorems carry `hash_coherent::<C>()` as a premise.
/// The library's internal key types take it by the axioms in
/// `history_analysis::verify::key_axioms` (TRUST.md).
pub uninterp spec fn hash_coherent<K: ?Sized>() -> bool;

/// `eq_spec` is an equivalence relation on `T`.
pub open spec fn eq_equivalence<T: PartialEq>() -> bool {
    &&& forall|a: T| #[trigger] a.eq_spec(&a)
    &&& forall|a: T, b: T| #[trigger] a.eq_spec(&b) == b.eq_spec(&a)
    &&& forall|a: T, b: T, c: T| #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) ==> a.eq_spec(&c)
}

/// What a hash-container key must satisfy: `Eq` agrees with `eq_spec`, which is an equivalence
/// and is respected by `Hash`.
pub open spec fn key_laws<K: Eq + Hash>() -> bool {
    K::obeys_eq_spec() && eq_equivalence::<K>() && hash_coherent::<K>()
}

/// The one bundle every monitor and analyzer guarantee assumes about the event type `E`
/// (R1 `event_laws` plus `key_laws` of its component type).
pub open spec fn event_obligations<E: Event>() -> bool {
    event_laws::<E>() && key_laws::<E::Component>()
}

} // verus!
