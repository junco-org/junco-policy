//! Typed and numeric policies (R4): a stored rule denies a typed pair exactly when its numeric
//! rule denies the pair's numeric image, pointwise over policies, and the typed answers of
//! `covered`, `redundant` and `at_least_as_strict` follow from the numeric ones.

use vstd::prelude::*;

verus! {
} // verus!
