//! vstd's hash-table key model for the analyzer's internal hash keys (TRUST.md, "axiom").
//!
//! Each key type's `Hash` and `Eq` are structural: `RegexId`/`TestId` are `u32` newtypes with
//! derived impls; pairs hash and compare field by field (std); `SmallVec` delegates to its slice;
//! `Constraint` derives `Hash` over its `Vec<RegisterConstraint>` and its `PartialEq::eq` ensures
//! `constraint_key` equality, which is structural equality of that vector. The derives are the
//! whole justification.

use crate::constraint::Constraint;
use core::hash::Hash;
use junco_core::kernel::{RegexId, TestId};
use smallvec::SmallVec;
use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;

verus! {

/// `RegexId`: `u32` newtype with derived `Hash`/`Eq`.
pub broadcast axiom fn axiom_regex_id_key_model()
    ensures #[trigger] obeys_key_model::<RegexId>();

/// `TestId`: `u32` newtype with derived `Hash`/`Eq`.
pub broadcast axiom fn axiom_test_id_key_model()
    ensures #[trigger] obeys_key_model::<TestId>();

/// Pairs hash and compare field by field (std), so the model lifts from the fields.
pub broadcast axiom fn axiom_pair_key_model<A: Eq + Hash, B: Eq + Hash>()
    ensures obeys_key_model::<A>() && obeys_key_model::<B>() ==> #[trigger] obeys_key_model::<(A, B)>();

/// `SmallVec<[RegexId; 4]>` delegates `Hash`/`Eq` to its slice.
pub broadcast axiom fn axiom_regex_id_smallvec_key_model()
    ensures #[trigger] obeys_key_model::<SmallVec<[RegexId; 4]>>();

/// `Constraint`: derived `Hash` over `Vec<RegisterConstraint>`; `eq` is `constraint_key` equality,
/// which is structural equality of that vector.
pub broadcast axiom fn axiom_constraint_key_model()
    ensures #[trigger] obeys_key_model::<Constraint>();

/// All five internal key-model axioms.
pub broadcast group group_internal_key_axioms {
    axiom_regex_id_key_model,
    axiom_test_id_key_model,
    axiom_pair_key_model,
    axiom_regex_id_smallvec_key_model,
    axiom_constraint_key_model,
}

} // verus!
