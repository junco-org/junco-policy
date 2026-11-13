//! R4: user-dischargeable hypotheses, separated from library-internal key obligations.
//! Panicking or unstable user Hash/Eq implementations are outside these guarantees.

use core::hash::Hash;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{arity, projection_laws, surjectivity};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// Equality is reflexive, symmetric, and transitive on the specified carrier.
pub open spec fn eq_equivalence<T>(
    eq: spec_fn(T, T) -> bool, domain: spec_fn(T) -> bool,
) -> bool {
    (forall|a: T| domain(a) ==> #[trigger] eq(a, a))
        && (forall|a: T, b: T| domain(a) && domain(b)
            ==> #[trigger] eq(a, b) == eq(b, a))
        && (forall|a: T, b: T, c: T| #![trigger eq(a, b), eq(b, c)]
            domain(a) && domain(b) && domain(c) && eq(a, b) && eq(b, c) ==> eq(a, c))
}

/// Faithfulness of the external hash containers for K: stable hashing coherent with modeled equality.
/// Introductions are restricted to decision 4's library-internal key types.
pub uninterp spec fn hash_coherent<K: Eq + Hash>() -> bool;

/// The external hash-container contracts are faithful for K and its modeled equality.
pub open spec fn key_laws<K: Eq + Hash>() -> bool {
    K::obeys_eq_spec() && eq_equivalence::<K>(|a: K, b: K| a.eq_spec(&b), |_: K| true)
        && hash_coherent::<K>()
}

/// The monitor needs stable, correctly tagged projections and faithful component keys.
/// Surjectivity is unnecessary for monitor soundness and is not added to its hypotheses.
pub open spec fn monitor_hypotheses<E: Event>() -> bool {
    1 <= arity::<E>() <= history_syntax::MAX_ARITY && E::obeys_projection_spec()
        && projection_laws::<E>() && key_laws::<E::Component>()
}

/// The analyzer additionally needs every well-tagged component tuple to represent a real event.
/// Fresh-value capacity is deliberately not a call precondition; it qualifies only a refutation.
pub open spec fn analyzer_hypotheses<E: Event>() -> bool {
    monitor_hypotheses::<E>() && surjectivity::<E>()
}

}
