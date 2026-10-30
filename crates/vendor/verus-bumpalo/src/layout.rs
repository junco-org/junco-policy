//! The crate's trusted bridge to `core::alloc::Layout::{size, align}`.

use core::alloc::Layout;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

pub uninterp spec fn layout_size(l: &Layout) -> usize;
pub uninterp spec fn layout_align(l: &Layout) -> usize;

#[verifier::when_used_as_spec(layout_size)]
pub assume_specification [Layout::size](l: &Layout) -> (s: usize)
    ensures s == layout_size(l),
    opens_invariants none
    no_unwind;

/// Trusted: Layout guarantees a power-of-two alignment that fits in usize.
#[verifier::when_used_as_spec(layout_align)]
pub assume_specification [Layout::align](l: &Layout) -> (a: usize)
    ensures a == layout_align(l), exists|n: nat| n < usize::BITS && a == pow2(n),
    opens_invariants none
    no_unwind;

}
