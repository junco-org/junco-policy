//! R4: user-dischargeable hypotheses, separated from library-internal key obligations.
//! Panicking or unstable user Hash/Eq implementations are outside these guarantees.

use core::hash::Hash;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{arity, projection_laws, surjectivity};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// Modeled component equality is reflexive, symmetric, and transitive.
pub open spec fn eq_equivalence<T: PartialEq>() -> bool {
    (forall|a: T| #[trigger] a.eq_spec(&a))
        && (forall|a: T, b: T| #[trigger] a.eq_spec(&b) == b.eq_spec(&a))
        && (forall|a: T, b: T, c: T| #![trigger a.eq_spec(&b), b.eq_spec(&c)]
            a.eq_spec(&b) && b.eq_spec(&c) ==> a.eq_spec(&c))
}

/// Faithfulness of the external hash containers for K: stable hashing coherent with modeled equality.
/// Library-internal introductions are restricted to the type-specific axioms of decision 4.
pub uninterp spec fn hash_coherent<K: Eq + Hash>() -> bool;

/// The external hash-container contracts are faithful for K and its modeled equality.
pub open spec fn key_laws<K: Eq + Hash>() -> bool {
    K::obeys_eq_spec() && eq_equivalence::<K>() && hash_coherent::<K>()
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
