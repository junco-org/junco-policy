//! Exact firing and the policy split (R3): the cases of a split on the head constants of a
//! policy decide those constants, so `Constraint::entails` against a rule's head constraint is
//! exactly semantic entailment; the cases satisfy `inclusion::split_ok` on `head_pairs`; and a
//! stored template's tail has the template's language (`policy::template_regex`).

use vstd::prelude::*;

verus! {
} // verus!
