//! vstd's hash-table key model for the tagged component types (TRUST.md, "axiom").
//!
//! `obeys_key_model::<K>()` says `K`'s `Hash`/`Eq` are faithful to `eq_spec`; vstd axiomatizes it
//! for primitive integers and `bool` and derives nothing for user types. `Component2/3/4` derive
//! `PartialEq`/`Eq`/`Hash` structurally (tag, then payload), so the model lifts from the payloads;
//! the derive is the whole justification.

use crate::event::{Component2, Component3, Component4};
use core::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;

verus! {

pub broadcast axiom fn axiom_component2_key_model<A: Eq + Hash, B: Eq + Hash>()
    ensures obeys_key_model::<A>() && obeys_key_model::<B>()
        ==> #[trigger] obeys_key_model::<Component2<A, B>>();

pub broadcast axiom fn axiom_component3_key_model<A: Eq + Hash, B: Eq + Hash, C: Eq + Hash>()
    ensures obeys_key_model::<A>() && obeys_key_model::<B>() && obeys_key_model::<C>()
        ==> #[trigger] obeys_key_model::<Component3<A, B, C>>();

pub broadcast axiom fn axiom_component4_key_model<A: Eq + Hash, B: Eq + Hash, C: Eq + Hash, D: Eq + Hash>()
    ensures obeys_key_model::<A>() && obeys_key_model::<B>() && obeys_key_model::<C>()
        && obeys_key_model::<D>() ==> #[trigger] obeys_key_model::<Component4<A, B, C, D>>();

pub broadcast group group_component_key_axioms {
    axiom_component2_key_model,
    axiom_component3_key_model,
    axiom_component4_key_model,
}

} // verus!
