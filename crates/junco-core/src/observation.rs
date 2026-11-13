// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;
#[cfg(feature = "runtime")]
use smallvec::SmallVec;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

#[cfg(any(test, feature = "test-util"))]
std::thread_local! {
    static RESERVATION_FAILURE_AFTER: core::cell::Cell<Option<usize>> = const {
        core::cell::Cell::new(None)
    };
}

#[cfg(any(test, feature = "test-util"))]
pub struct ReservationFailureGuard(Option<usize>);

#[cfg(any(test, feature = "test-util"))]
impl Drop for ReservationFailureGuard {
    fn drop(&mut self) {
        RESERVATION_FAILURE_AFTER.with(|remaining| remaining.set(self.0));
    }
}

#[cfg(any(test, feature = "test-util"))]
pub fn fail_reservations_after(successful: usize) -> ReservationFailureGuard {
    ReservationFailureGuard(
        RESERVATION_FAILURE_AFTER.with(|remaining| remaining.replace(Some(successful))),
    )
}

#[cfg(any(test, feature = "test-util"))]
pub fn reservation_checkpoint() -> Result<(), alloc::collections::TryReserveError> {
    let fail = RESERVATION_FAILURE_AFTER.with(|remaining| match remaining.get() {
        None => false,
        Some(0) => true,
        Some(count) => {
            remaining.set(Some(count - 1));
            false
        }
    });
    if fail {
        Vec::<u8>::new().try_reserve(usize::MAX)
    } else {
        Ok(())
    }
}

// Native SmallVec contents are an explicit container boundary, shared by its leaves.
#[cfg(all(feature = "runtime", verus_keep_ghost))]
verus! {
    #[verifier::external_trait_specification]
    pub trait ExSmallVecArray {
        type ExternalTraitSpecificationFor: smallvec::Array;
        type Item;
    }

    #[verifier::external_type_specification]
    #[verifier::external_body]
    #[verifier::accept_recursive_types(A)]
    pub struct ExSmallVec<A: smallvec::Array>(SmallVec<A>);

    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExCollectionAllocErr(smallvec::CollectionAllocErr);

    pub trait SmallVecSpecFns<T> {
        spec fn view(&self) -> Seq<T>;
    }

    impl<A: smallvec::Array> SmallVecSpecFns<A::Item> for SmallVec<A> {
        uninterp spec fn view(&self) -> Seq<A::Item>;
    }
}

/// Owned ordered regex parts with native equality verified against its sequence model.
///
/// SmallVec's external `PartialEq` implementation has no equality specification in
/// the pinned vstd. This key keeps the same storage and hashing, but compares the
/// borrowed ID slices through the verified implementation instead.
#[cfg(feature = "runtime")]
#[allow(clippy::derived_hash_with_manual_eq)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Hash)]
pub struct PartsKey(SmallVec<[crate::kernel::RegexId; 4]>);

#[cfg(feature = "runtime")]
#[verus_verify]
impl PartsKey {
    #[verus_spec(result => ensures result.view() == parts.view())]
    pub fn from_smallvec(parts: SmallVec<[crate::kernel::RegexId; 4]>) -> Self {
        Self(parts)
    }

    #[verus_spec(result => ensures result == self.view().len())]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[verus_spec(result => ensures result == (self.view().len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[verus_spec(result => ensures result@ == self.view())]
    pub fn as_slice(&self) -> &[crate::kernel::RegexId] {
        &self.0
    }
}

#[cfg(all(feature = "runtime", verus_keep_ghost))]
verus! {
    impl PartsKey {
        pub closed spec fn view(&self) -> Seq<crate::kernel::RegexId> {
            self.0.view()
        }
    }

    impl vstd::std_specs::cmp::PartialEqSpecImpl for PartsKey {
        open spec fn obeys_eq_spec() -> bool { true }
        open spec fn eq_spec(&self, other: &Self) -> bool {
            self.view() == other.view()
        }
    }
}

#[cfg(feature = "runtime")]
#[verus_verify]
impl PartialEq for PartsKey {
    #[verus_spec(result => ensures result == (self.view() == other.view()))]
    fn eq(&self, other: &Self) -> bool {
        crate::kernel::id_slice_eq(self.as_slice(), other.as_slice())
    }
}

#[cfg(feature = "runtime")]
#[verus_verify]
impl Eq for PartsKey {}

/// Capability for native reservation observations during one history operation.
#[verus_verify]
pub struct ObservationWorld;

impl ObservationWorld {
    // Native reservation may fail but must preserve every existing element.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values)@ == old(values)@)]
    #[inline]
    pub fn try_reserve_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        #[cfg(any(test, feature = "test-util"))]
        reservation_checkpoint()?;
        values.try_reserve(additional)
    }

    // Vec::try_reserve_exact is unsupported by Verus; reservation preserves elements.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values)@ == old(values)@)]
    #[inline]
    pub fn try_reserve_vec_exact<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        #[cfg(any(test, feature = "test-util"))]
        reservation_checkpoint()?;
        values.try_reserve_exact(additional)
    }

    #[cfg(feature = "runtime")]
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures final(values).view() == old(values).view())]
    #[inline]
    pub fn try_reserve_words(
        &mut self,
        values: &mut SmallVec<[u64; 2]>,
        additional: usize,
    ) -> Result<(), smallvec::CollectionAllocErr> {
        #[cfg(any(test, feature = "test-util"))]
        if reservation_checkpoint().is_err() {
            return values.try_reserve_exact(usize::MAX);
        }
        values.try_reserve_exact(additional)
    }
}
