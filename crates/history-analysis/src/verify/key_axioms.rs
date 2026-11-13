//! R4's `hash_coherent` for the analyzer's internal hash keys (TRUST.md, "axiom").
//!
//! Each key type's `Hash` and `Eq` are structural: `ConstraintId` is `u32`, `RegexId`/`TestId` are
//! `u32` newtypes with derived impls; pairs hash and compare field by field (std); `SmallVec`
//! delegates to its slice;
//! `Constraint` derives `Hash` over its `Vec<RegisterConstraint>` and its `PartialEq::eq` ensures
//! `constraint_key` equality, which is structural equality of that vector. The derives are the
//! whole justification.

use crate::constraint::{Constraint, ConstraintId};
use core::hash::Hash;
use junco_core::kernel::{RegexId, TestId};
use junco_core::observation::SmallVecSpecFns;
use junco_core::spec::hypotheses::hash_coherent;
use smallvec::SmallVec;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// `(ConstraintId, RegexId)`: a `u32` and a `u32` newtype with derived `Hash`/`Eq`, hashed and
/// compared field by field (std).
pub broadcast axiom fn axiom_constraint_regex_pair_key_model()
    ensures #[trigger] hash_coherent::<(ConstraintId, RegexId)>();

/// `(RegexId, RegexId)`: two `u32` newtypes with derived `Hash`/`Eq`, field by field (std).
pub broadcast axiom fn axiom_regex_pair_key_model()
    ensures #[trigger] hash_coherent::<(RegexId, RegexId)>();

/// `(TestId, TestId)`: two `u32` newtypes with derived `Hash`/`Eq`, field by field (std).
pub broadcast axiom fn axiom_test_pair_key_model()
    ensures #[trigger] hash_coherent::<(TestId, TestId)>();

/// `SmallVec<[RegexId; 4]>` delegates `Hash`/`Eq` to its slice: `PartialEq` is slice equality,
/// element-wise on the derived `RegexId` `PartialEq`, so `eq_spec` is view equality (no
/// `PartialEqSpecImpl` can be written for the foreign type).
pub broadcast axiom fn axiom_regex_id_smallvec_key_model()
    ensures #[trigger] hash_coherent::<SmallVec<[RegexId; 4]>>(),
        <SmallVec<[RegexId; 4]> as PartialEqSpec>::obeys_eq_spec(),
        forall|a: SmallVec<[RegexId; 4]>, b: SmallVec<[RegexId; 4]>|
            #[trigger] a.eq_spec(&b) == (a.view() == b.view());

/// `Constraint`: derived `Hash` over `Vec<RegisterConstraint>`; `eq` is `constraint_key` equality,
/// which is structural equality of that vector.
pub broadcast axiom fn axiom_constraint_key_model()
    ensures #[trigger] hash_coherent::<Constraint>();

/// All five internal key-model axioms.
pub broadcast group group_internal_key_axioms {
    axiom_constraint_regex_pair_key_model,
    axiom_regex_pair_key_model,
    axiom_test_pair_key_model,
    axiom_regex_id_smallvec_key_model,
    axiom_constraint_key_model,
}

} // verus!
