//! R4: user-dischargeable hypotheses, separated from library-internal key obligations.
//! Panicking or unstable user Hash/Eq implementations are outside these guarantees.

use core::fmt::Debug;
use core::hash::Hash;
use history_syntax::Component3;
use history_syntax::Event;
use history_syntax::spec::events::EventSpec;
use history_syntax::spec::events::{arity, event_view, projection_laws, surjectivity, well_tagged};
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

/// Instantiates the canonical equivalence law without relying on higher-order trigger inference.
pub proof fn lemma_eq_equivalence_at<T>(
    eq: spec_fn(T, T) -> bool, domain: spec_fn(T) -> bool, a: T, b: T, c: T,
)
    requires eq_equivalence(eq, domain), domain(a), domain(b), domain(c),
    ensures eq(a, a), eq(a, b) == eq(b, a), eq(a, b) && eq(b, c) ==> eq(a, c),
{}

/// Restricting an equivalence relation to a smaller carrier preserves its laws.
pub proof fn lemma_eq_equivalence_restrict<T>(
    eq: spec_fn(T, T) -> bool, domain: spec_fn(T) -> bool, subset: spec_fn(T) -> bool,
)
    requires eq_equivalence(eq, domain), forall|a: T| #[trigger] subset(a) ==> domain(a),
    ensures eq_equivalence(eq, subset),
{}

/// Faithfulness of the external hash containers for K: stable hashing coherent with modeled equality.
/// Only decision 4's exact library-internal key types have trusted introductions.
pub uninterp spec fn hash_coherent<K: Eq + Hash>() -> bool;

/// The external hash-container contracts are faithful for K and its modeled equality.
pub open spec fn key_laws<K: Eq + Hash>() -> bool {
    K::obeys_eq_spec() && eq_equivalence::<K>(|a: K, b: K| a.eq_spec(&b), |_: K| true)
        && hash_coherent::<K>()
}

/// Instantiates native equality laws from the single faithful-container boundary.
pub proof fn lemma_key_laws_at<K: Eq + Hash>(a: K, b: K, c: K)
    requires key_laws::<K>(),
    ensures a.eq_spec(&a), a.eq_spec(&b) == b.eq_spec(&a),
        a.eq_spec(&b) && b.eq_spec(&c) ==> a.eq_spec(&c),
{
    lemma_eq_equivalence_at(|a: K, b: K| a.eq_spec(&b), |_: K| true, a, b, c);
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

/// Instantiates R1 projection correctness at one real event and valid coordinate.
pub proof fn lemma_monitor_projection<E: Event>(event: E, index: int)
    requires monitor_hypotheses::<E>(), 0 <= index < arity::<E>(),
    ensures event_view(event).len() == arity::<E>(),
        E::coordinate_spec(event_view(event)[index]) == index,
{
    assert(well_tagged::<E>(event_view(event)));
}

/// Tuple projections and tagged equality discharge both bundles from the component hash token.
pub proof fn lemma_tuple3_event_hypotheses<
    A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash, C: Copy + Debug + Eq + Hash,
>()
    requires A::obeys_eq_spec(), B::obeys_eq_spec(), C::obeys_eq_spec(),
        eq_equivalence::<A>(|a: A, b: A| a.eq_spec(&b), |_: A| true),
        eq_equivalence::<B>(|a: B, b: B| a.eq_spec(&b), |_: B| true),
        eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true),
        hash_coherent::<Component3<A, B, C>>(),
    ensures monitor_hypotheses::<(A, B, C)>(), analyzer_hypotheses::<(A, B, C)>(),
{
    assert(eq_equivalence::<A>(|a: A, b: A| a.eq_spec(&b), |_: A| true));
    assert(eq_equivalence::<B>(|a: B, b: B| a.eq_spec(&b), |_: B| true));
    assert(eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true));
    assert forall|x: Component3<A, B, C>| #[trigger] x.eq_spec(&x) by {
        history_syntax::spec::equality::lemma_component3_equality(x, x);
        match x {
            Component3::C0(a) => lemma_eq_equivalence_at(|a: A, b: A| a.eq_spec(&b), |_: A| true, a, a, a),
            Component3::C1(b) => lemma_eq_equivalence_at(|a: B, b: B| a.eq_spec(&b), |_: B| true, b, b, b),
            Component3::C2(c) => lemma_eq_equivalence_at(|a: C, b: C| a.eq_spec(&b), |_: C| true, c, c, c),
        }
    }
    assert forall|x: Component3<A, B, C>, y: Component3<A, B, C>|
        #[trigger] x.eq_spec(&y) == y.eq_spec(&x) by {
        history_syntax::spec::equality::lemma_component3_equality(x, y);
        history_syntax::spec::equality::lemma_component3_equality(y, x);
        match (x, y) {
            (Component3::C0(a), Component3::C0(b)) => lemma_eq_equivalence_at(|a: A, b: A| a.eq_spec(&b), |_: A| true, a, b, b),
            (Component3::C1(a), Component3::C1(b)) => lemma_eq_equivalence_at(|a: B, b: B| a.eq_spec(&b), |_: B| true, a, b, b),
            (Component3::C2(a), Component3::C2(b)) => lemma_eq_equivalence_at(|a: C, b: C| a.eq_spec(&b), |_: C| true, a, b, b),
            _ => {},
        }
    }
    assert forall|x: Component3<A, B, C>, y: Component3<A, B, C>, z: Component3<A, B, C>|
        #[trigger] x.eq_spec(&y) && #[trigger] y.eq_spec(&z) implies x.eq_spec(&z) by {
        history_syntax::spec::equality::lemma_component3_equality(x, y);
        history_syntax::spec::equality::lemma_component3_equality(y, z);
        history_syntax::spec::equality::lemma_component3_equality(x, z);
        match (x, y, z) {
            (Component3::C0(a), Component3::C0(b), Component3::C0(c)) => lemma_eq_equivalence_at(|a: A, b: A| a.eq_spec(&b), |_: A| true, a, b, c),
            (Component3::C1(a), Component3::C1(b), Component3::C1(c)) => lemma_eq_equivalence_at(|a: B, b: B| a.eq_spec(&b), |_: B| true, a, b, c),
            (Component3::C2(a), Component3::C2(b), Component3::C2(c)) => lemma_eq_equivalence_at(|a: C, b: C| a.eq_spec(&b), |_: C| true, a, b, c),
            _ => {},
        }
    }
    history_syntax::spec::events::lemma_tuple3_event_laws::<A, B, C>();
}

/// All finite three-u8 event hypotheses except the explicit external-container faithfulness token.
pub proof fn lemma_u8_event_hypotheses()
    requires hash_coherent::<Component3<u8, u8, u8>>(),
    ensures monitor_hypotheses::<(u8, u8, u8)>(), analyzer_hypotheses::<(u8, u8, u8)>(),
{
    lemma_tuple3_event_hypotheses::<u8, u8, u8>();
}

/// All u32-coordinate event hypotheses except the explicit external-container faithfulness token.
pub proof fn lemma_u32_event_hypotheses()
    requires hash_coherent::<Component3<u32, u8, u8>>(),
    ensures monitor_hypotheses::<(u32, u8, u8)>(), analyzer_hypotheses::<(u32, u8, u8)>(),
{
    lemma_tuple3_event_hypotheses::<u32, u8, u8>();
}

}

#[cfg(feature = "runtime")]
pub mod internal_keys {
    use super::*;
    use crate::kernel::{RegexId, TestId};
    use crate::observation::SmallVecSpecFns;
    use smallvec::SmallVec;

    verus! {
    /// Decision 4: an internal search key pairs a constraint index with an exact regex id.
    #[verifier::external_body]
    pub broadcast proof fn lemma_search_key_laws()
        ensures #[trigger] key_laws::<(u32, RegexId)>(),
    {}

    /// Decision 4: the simulation memo compares and hashes both exact regex ids.
    #[verifier::external_body]
    pub broadcast proof fn lemma_regex_pair_key_laws()
        ensures #[trigger] key_laws::<(RegexId, RegexId)>(),
    {}

    /// Decision 4: the test simulation memo compares and hashes both exact test ids.
    #[verifier::external_body]
    pub broadcast proof fn lemma_test_pair_key_laws()
        ensures #[trigger] key_laws::<(TestId, TestId)>(),
    {}

    /// Decision 4: ordered internal part keys compare/hash the complete id sequence.
    #[verifier::external_body]
    pub broadcast proof fn lemma_parts_key_laws()
        ensures #[trigger] key_laws::<SmallVec<[RegexId; 4]>>(),
            forall|a: SmallVec<[RegexId; 4]>, b: SmallVec<[RegexId; 4]>|
                #[trigger] a.eq_spec(&b) ==> a.view() == b.view(),
    {}

    pub broadcast group group_internal_key_laws {
        lemma_search_key_laws,
        lemma_regex_pair_key_laws,
        lemma_test_pair_key_laws,
        lemma_parts_key_laws,
    }
    }
}
