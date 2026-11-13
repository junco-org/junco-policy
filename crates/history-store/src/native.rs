//! Faithful native hash containers over modeled equality classes, shared by the store and analyzer.

use alloc::vec::Vec;
use core::hash::Hash;
use hashbrown::{HashMap, HashSet};
use junco_core::error::HistoryError;
use junco_core::spec::hypotheses::key_laws;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct NativeMap<K: Eq + Hash, V: Copy> {
    inner: HashMap<K, V>,
}

/// The finite representatives actually stored; keys model Eq classes, not Rust identity.
pub uninterp spec fn representatives<K: Eq + Hash, V: Copy>(m: NativeMap<K, V>) -> Seq<(K, V)>;

impl<K: Eq + Hash, V: Copy> NativeMap<K, V> {
    #[verifier::external_body]
    pub fn new() -> (m: Self)
        ensures representatives(m) == Seq::<(K, V)>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn lookup(&self, key: &K) -> (value: Option<V>)
        ensures key_laws::<K>() ==> match value {
            Some(v) => exists|i: int| 0 <= i < representatives(*self).len()
                && representatives(*self)[i].1 == v && key.eq_spec(&representatives(*self)[i].0),
            None => forall|i: int| 0 <= i < representatives(*self).len()
                ==> !key.eq_spec(&representatives(*self)[i].0),
        },
    {
        self.inner.get(key).copied()
    }

    #[verifier::external_body]
    pub fn reserve_one(&mut self) -> (result: Result<(), HistoryError>)
        ensures representatives(*final(self)) == representatives(*old(self)),
            result is Err ==> result == Err(HistoryError::AllocationFailed),
    {
        #[cfg(any(test, feature = "test-util"))]
        junco_core::observation::reservation_checkpoint()
            .map_err(|_| HistoryError::AllocationFailed)?;
        self.inner.try_reserve(1).map_err(|_| HistoryError::AllocationFailed)
    }

    #[verifier::external_body]
    pub fn insert_fresh(&mut self, key: K, value: V)
        requires key_laws::<K>() ==> forall|i: int|
            0 <= i < representatives(*old(self)).len()
                ==> !key.eq_spec(&representatives(*old(self))[i].0),
        ensures key_laws::<K>() ==>
            representatives(*final(self)) == representatives(*old(self)).push((key, value)),
    {
        self.inner.insert(key, value);
    }
}

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub struct NativeSet<K: Eq + Hash> {
    inner: HashSet<K>,
}

pub uninterp spec fn members<K: Eq + Hash>(s: NativeSet<K>) -> Set<K>;

impl<K: Eq + Hash> NativeSet<K> {
    #[verifier::external_body]
    pub fn new() -> (s: Self)
        ensures members(s) == Set::<K>::empty(),
    {
        Self { inner: HashSet::new() }
    }

    #[verifier::external_body]
    pub fn insert(&mut self, key: K) -> (fresh: bool)
        ensures key_laws::<K>() ==> {
            &&& fresh == !(exists|k: K| members(*old(self)).contains(k) && key.eq_spec(&k))
            &&& members(*final(self)) == if fresh {
                members(*old(self)).insert(key)
            } else { members(*old(self)) }
        },
    {
        self.inner.insert(key)
    }
}

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct NativeGroups<K: Eq + Hash, V> {
    inner: HashMap<K, Vec<V>>,
}

pub uninterp spec fn groups<K: Eq + Hash, V>(m: NativeGroups<K, V>) -> Map<K, Seq<V>>;

impl<K: Eq + Hash, V> NativeGroups<K, V> {
    #[verifier::external_body]
    pub fn new() -> (m: Self)
        ensures groups(m) == Map::<K, Seq<V>>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn get(&self, key: &K) -> (value: Option<&Vec<V>>)
        ensures key_laws::<K>() ==> match value {
            Some(values) => exists|k: K| groups(*self).dom().contains(k)
                && key.eq_spec(&k) && values@ == groups(*self)[k],
            None => forall|k: K| groups(*self).dom().contains(k) ==> !key.eq_spec(&k),
        },
    {
        self.inner.get(key)
    }

    #[verifier::external_body]
    pub fn push(&mut self, key: K, value: V)
        ensures key_laws::<K>() ==> {
            &&& groups(*final(self)).dom() == if exists|k: K|
                groups(*old(self)).dom().contains(k) && key.eq_spec(&k)
            { groups(*old(self)).dom() } else { groups(*old(self)).dom().insert(key) }
            &&& forall|k: K| groups(*old(self)).dom().contains(k)
                ==> groups(*final(self))[k] == if key.eq_spec(&k) {
                    groups(*old(self))[k].push(value)
                } else { groups(*old(self))[k] }
            &&& !(exists|k: K| groups(*old(self)).dom().contains(k) && key.eq_spec(&k))
                ==> groups(*final(self))[key] == Seq::<V>::empty().push(value)
        },
    {
        self.inner.entry(key).or_default().push(value);
    }
}

}
