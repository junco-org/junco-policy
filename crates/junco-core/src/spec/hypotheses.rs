//! R4: the hypothesis bundles every monitor and analyzer guarantee assumes about its event type
//! (plan S4, decision 4). Their discharge for concrete event types is in
//! `junco_core::verify::hypotheses` and `history_syntax::verify::events`; the one trusted token is
//! `hash_coherent`, listed in TRUST.md.

use crate::spec::semantics::*;
use core::hash::Hash;
use history_syntax::Event;
use history_syntax::spec::events::event_laws;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// The single trust token: `K`'s `Hash`/`Eq` are faithful to `eq_spec`, so the `external_body`
/// hash containers behave as maps on `eq_spec` classes. This is vstd's key model; vstd axiomatizes
/// it for primitive integers and `bool`; `Component2/3/4` get it from their payloads by the axioms
/// in `junco_core::verify::hypotheses` (TRUST.md).
pub open spec fn hash_coherent<K: ?Sized>() -> bool {
    vstd::std_specs::hash::obeys_key_model::<K>()
}

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
