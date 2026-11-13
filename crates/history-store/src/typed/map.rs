//! Native hashbrown leaves; representatives model Eq classes, not Rust identity.
//!
//! Keys are user component types, so user `Hash`/`Eq` code runs under the store lock. A panic
//! there unwinds through the lock and is outside the trusted base: Verus assumes the lock
//! invariant on re-entry, and the contracts below hold only for `Hash`/`Eq` that return
//! (`key_laws` in `junco_core::spec::hypotheses` states the faithfulness they must also have).

use core::hash::Hash;
use hashbrown::HashMap;
use junco_core::errors::HistoryError;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub(crate) struct NativeMap<K: Copy + Eq + Hash> {
    inner: HashMap<K, u64>,
}

/// These are precisely the finite representatives stored by this native map.
pub(crate) uninterp spec fn representatives<K: Copy + Eq + Hash>(map: NativeMap<K>) -> Seq<(K, u64)>;

impl<K: Copy + Eq + Hash> NativeMap<K> {
    #[verifier::external_body]
    pub(super) fn new() -> (result: Self)
        ensures representatives(result) == Seq::<(K, u64)>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub(super) fn lookup(&self, key: &K) -> (result: Option<u64>)
        ensures junco_core::spec::hypotheses::key_laws::<K>() ==> match result {
            Some(id) => exists|i: int| 0 <= i < representatives(*self).len()
                && representatives(*self)[i].1 == id
                && key.eq_spec(&representatives(*self)[i].0),
            None => forall|i: int| 0 <= i < representatives(*self).len()
                ==> !key.eq_spec(&representatives(*self)[i].0),
        },
    {
        self.inner.get(key).copied()
    }

    #[verifier::external_body]
    pub(super) fn reserve_one(&mut self) -> (result: Result<(), HistoryError>)
        ensures representatives(*final(self)) == representatives(*old(self)),
            result is Err ==> result == Err(HistoryError::AllocationFailed),
    {
        #[cfg(any(test, feature = "test-util"))]
        junco_core::observation::reservation_checkpoint()
            .map_err(|_| HistoryError::AllocationFailed)?;
        self.inner.try_reserve(1).map_err(|_| HistoryError::AllocationFailed)
    }

    #[verifier::external_body]
    pub(super) fn insert_fresh(&mut self, key: K, id: u64)
        requires junco_core::spec::hypotheses::key_laws::<K>() ==> forall|i: int|
            0 <= i < representatives(*old(self)).len()
                ==> !key.eq_spec(&representatives(*old(self))[i].0),
        ensures junco_core::spec::hypotheses::key_laws::<K>() ==>
            representatives(*final(self)) == representatives(*old(self)).push((key, id)),
    {
        self.inner.insert(key, id);
    }
}
}
