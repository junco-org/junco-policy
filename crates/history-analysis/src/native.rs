//! Native hashbrown leaves; logical keys represent Eq classes, not Rust identity.

use alloc::vec::Vec;
use core::hash::Hash;
use hashbrown::{HashMap, HashSet};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub(crate) struct NativeMap<K: Eq + Hash, V: Copy> {
    inner: HashMap<K, V>,
}

pub(crate) uninterp spec fn representatives<K: Eq + Hash, V: Copy>(m: NativeMap<K, V>)
    -> Seq<(K, V)>;

/// Native Hash/Eq coherence supplied as an implementation obligation.
pub uninterp spec fn hash_coherent<K: Eq + Hash>() -> bool;

/// Equality laws and native hashing obligations required by the hashbrown leaves.
pub open spec fn key_obligations<K: Eq + Hash>() -> bool {
    K::obeys_eq_spec() && hash_coherent::<K>()
        && (forall|a: K| #[trigger] a.eq_spec(&a))
        && (forall|a: K, b: K| #[trigger] a.eq_spec(&b) == b.eq_spec(&a))
        && (forall|a: K, b: K, c: K| #[trigger] a.eq_spec(&b)
            && #[trigger] b.eq_spec(&c) ==> a.eq_spec(&c))
}

impl<K: Eq + Hash, V: Copy> NativeMap<K, V> {
    #[verifier::external_body]
    pub(crate) fn new() -> (m: Self)
        ensures representatives(m) == Seq::<(K, V)>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub(crate) fn lookup(&self, key: &K) -> (value: Option<V>)
        ensures key_obligations::<K>() ==> match value {
            Some(v) => exists|i: int| 0 <= i < representatives(*self).len()
                && representatives(*self)[i].1 == v
                && key.eq_spec(&representatives(*self)[i].0),
            None => forall|i: int| 0 <= i < representatives(*self).len()
                ==> !key.eq_spec(&representatives(*self)[i].0),
        },
    {
        self.inner.get(key).copied()
    }

    #[verifier::external_body]
    pub(crate) fn insert_fresh(&mut self, key: K, value: V)
        requires key_obligations::<K>() ==> forall|i: int|
            0 <= i < representatives(*old(self)).len()
                ==> !key.eq_spec(&representatives(*old(self))[i].0),
        ensures key_obligations::<K>() ==>
            representatives(*final(self)) == representatives(*old(self)).push((key, value)),
    {
        self.inner.insert(key, value);
    }
}

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub(crate) struct NativeSet<K: Eq + Hash> {
    inner: HashSet<K>,
}

pub(crate) uninterp spec fn members<K: Eq + Hash>(s: NativeSet<K>) -> Set<K>;

impl<K: Eq + Hash> NativeSet<K> {
    #[verifier::external_body]
    pub(crate) fn new() -> (s: Self)
        ensures members(s) == Set::<K>::empty(),
    {
        Self { inner: HashSet::new() }
    }

    #[verifier::external_body]
    pub(crate) fn insert(&mut self, key: K) -> (fresh: bool)
        ensures key_obligations::<K>() ==> {
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
pub(crate) struct NativeGroups<K: Eq + Hash, V> {
    inner: HashMap<K, Vec<V>>,
}

pub(crate) uninterp spec fn groups<K: Eq + Hash, V>(m: NativeGroups<K, V>) -> Map<K, Seq<V>>;

impl<K: Eq + Hash, V> NativeGroups<K, V> {
    #[verifier::external_body]
    pub(crate) fn new() -> (m: Self)
        ensures groups(m) == Map::<K, Seq<V>>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub(crate) fn get(&self, key: &K) -> (value: Option<&Vec<V>>)
        ensures key_obligations::<K>() ==> match value {
            Some(values) => exists|k: K| groups(*self).dom().contains(k)
                && key.eq_spec(&k) && values@ == groups(*self)[k],
            None => forall|k: K| groups(*self).dom().contains(k) ==> !key.eq_spec(&k),
        },
    {
        self.inner.get(key)
    }

    #[verifier::external_body]
    pub(crate) fn push(&mut self, key: K, value: V)
        ensures key_obligations::<K>() ==> {
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
