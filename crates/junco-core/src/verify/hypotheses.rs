//! Concrete witnesses for `event_obligations` (`junco_core::spec::hypotheses`): the built-in tuple events satisfy
//! every conjunct once `hash_coherent` of their component type is assumed; nothing here is trusted.

use crate::spec::hypotheses::{eq_equivalence, event_obligations, hash_coherent, key_laws};
use core::fmt::Debug;
use core::hash::Hash;
use history_syntax::event::{Component2, Component3, Component4};
use history_syntax::verify::events::{
    lemma_event_laws_pair, lemma_event_laws_quad, lemma_event_laws_triple,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// A tagged pair component is a hash key when its payloads' `eq_spec` is faithful and an
/// equivalence and its hashing is coherent.
pub proof fn lemma_key_laws_component2<A: Eq + Hash, B: Eq + Hash>()
    requires hash_coherent::<Component2<A, B>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
    ensures key_laws::<Component2<A, B>>(),
{
    assert forall|a: Component2<A, B>, b: Component2<A, B>, c: Component2<A, B>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component2::C0(x), Component2::C0(y), Component2::C0(z)) => assert(x.eq_spec(&z)),
            (Component2::C1(x), Component2::C1(y), Component2::C1(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
}

/// A tagged triple component is a hash key under the same premises on its payloads.
pub proof fn lemma_key_laws_component3<A: Eq + Hash, B: Eq + Hash, C: Eq + Hash>()
    requires hash_coherent::<Component3<A, B, C>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
        C::obeys_eq_spec(), eq_equivalence::<C>(),
    ensures key_laws::<Component3<A, B, C>>(),
{
    assert forall|a: Component3<A, B, C>, b: Component3<A, B, C>, c: Component3<A, B, C>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component3::C0(x), Component3::C0(y), Component3::C0(z)) => assert(x.eq_spec(&z)),
            (Component3::C1(x), Component3::C1(y), Component3::C1(z)) => assert(x.eq_spec(&z)),
            (Component3::C2(x), Component3::C2(y), Component3::C2(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
}

/// A tagged quadruple component is a hash key under the same premises on its payloads.
pub proof fn lemma_key_laws_component4<A: Eq + Hash, B: Eq + Hash, C: Eq + Hash, D: Eq + Hash>()
    requires hash_coherent::<Component4<A, B, C, D>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
        C::obeys_eq_spec(), eq_equivalence::<C>(), D::obeys_eq_spec(), eq_equivalence::<D>(),
    ensures key_laws::<Component4<A, B, C, D>>(),
{
    assert forall|a: Component4<A, B, C, D>, b: Component4<A, B, C, D>, c: Component4<A, B, C, D>|
        #[trigger] a.eq_spec(&b) && #[trigger] b.eq_spec(&c) implies a.eq_spec(&c) by {
        match (a, b, c) {
            (Component4::C0(x), Component4::C0(y), Component4::C0(z)) => assert(x.eq_spec(&z)),
            (Component4::C1(x), Component4::C1(y), Component4::C1(z)) => assert(x.eq_spec(&z)),
            (Component4::C2(x), Component4::C2(y), Component4::C2(z)) => assert(x.eq_spec(&z)),
            (Component4::C3(x), Component4::C3(y), Component4::C3(z)) => assert(x.eq_spec(&z)),
            _ => {}
        }
    }
}

/// `event_obligations` for a pair event: `hash_coherent` of its component type plus faithful
/// equivalence `eq_spec` on the payloads.
pub proof fn lemma_pair_event_hypotheses<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash>()
    requires hash_coherent::<Component2<A, B>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
    ensures event_obligations::<(A, B)>(),
{
    lemma_event_laws_pair::<A, B>();
    lemma_key_laws_component2::<A, B>();
}

/// `event_obligations` for a triple event under the same premises.
pub proof fn lemma_triple_event_hypotheses<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash>()
    requires hash_coherent::<Component3<A, B, C>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
        C::obeys_eq_spec(), eq_equivalence::<C>(),
    ensures event_obligations::<(A, B, C)>(),
{
    lemma_event_laws_triple::<A, B, C>();
    lemma_key_laws_component3::<A, B, C>();
}

/// `event_obligations` for a quadruple event under the same premises.
pub proof fn lemma_quad_event_hypotheses<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash, D: Copy + Debug + Eq + Hash>()
    requires hash_coherent::<Component4<A, B, C, D>>(),
        A::obeys_eq_spec(), eq_equivalence::<A>(), B::obeys_eq_spec(), eq_equivalence::<B>(),
        C::obeys_eq_spec(), eq_equivalence::<C>(), D::obeys_eq_spec(), eq_equivalence::<D>(),
    ensures event_obligations::<(A, B, C, D)>(),
{
    lemma_event_laws_quad::<A, B, C, D>();
    lemma_key_laws_component4::<A, B, C, D>();
}

/// `(u32, u64)` events: `hash_coherent` of the component type is the only premise (vstd gives
/// `eq_spec` as `==` for primitives).
pub proof fn lemma_u32_u64_event_hypotheses()
    requires hash_coherent::<Component2<u32, u64>>(),
    ensures event_obligations::<(u32, u64)>(),
{
    lemma_pair_event_hypotheses::<u32, u64>();
}

/// `(u8, u8, u8)` events: `hash_coherent` of the component type is the only premise.
pub proof fn lemma_u8_triple_event_hypotheses()
    requires hash_coherent::<Component3<u8, u8, u8>>(),
    ensures event_obligations::<(u8, u8, u8)>(),
{
    lemma_triple_event_hypotheses::<u8, u8, u8>();
}

/// `(u32, u8, bool)` events: `hash_coherent` of the component type is the only premise.
pub proof fn lemma_u32_mixed_event_hypotheses()
    requires hash_coherent::<Component3<u32, u8, bool>>(),
    ensures event_obligations::<(u32, u8, bool)>(),
{
    lemma_triple_event_hypotheses::<u32, u8, bool>();
}

} // verus!
