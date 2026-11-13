//! Verified hash containers over `history_store::keyed::KeyedMap`; logical keys represent
//! `eq_spec` classes, not Rust identity.

use alloc::vec::Vec;
use history_store::keyed::KeyedMap;
use history_syntax::KeyHash;
#[cfg(verus_keep_ghost)]
use junco_core::spec::hypotheses::key_laws;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use vstd::seq::Seq::to_set_ensures;

pub(crate) type NativeMap<K, V> = KeyedMap<K, V>;

/// The entries of an interning map, in insertion order.
pub(crate) open spec fn representatives<K: Eq + KeyHash, V>(m: NativeMap<K, V>) -> Seq<(K, V)> {
    m@
}

/// The keys of an entry sequence, in order.
pub(crate) open spec fn keys_of<K, V>(entries: Seq<(K, V)>) -> Seq<K> {
    entries.map_values(|e: (K, V)| e.0)
}

pub(crate) struct NativeSet<K: Eq + KeyHash> {
    pub(crate) inner: KeyedMap<K, ()>,
}

/// The keys stored so far.
pub(crate) open spec fn members<K: Eq + KeyHash>(s: NativeSet<K>) -> Set<K> {
    keys_of(s.inner@).to_set()
}

impl<K: Eq + KeyHash> NativeSet<K> {
    pub(crate) fn new() -> (s: Self)
        ensures members(s) == Set::<K>::empty(),
    {
        let s = Self { inner: KeyedMap::new() };
        proof { assert(members(s) =~= Set::<K>::empty()); }
        s
    }

    pub(crate) fn insert(&mut self, key: K) -> (fresh: bool)
        ensures key_laws::<K>() ==> {
            &&& fresh == !(exists|k: K| members(*old(self)).contains(k) && key.eq_spec(&k))
            &&& members(*final(self)) == if fresh {
                members(*old(self)).insert(key)
            } else { members(*old(self)) }
        },
    {
        let ghost before = self.inner@;
        let found = self.inner.find(&key);
        proof {
            if key_laws::<K>() {
                match found {
                    Some(i) => {
                        assert(keys_of(before)[i as int] == before[i as int].0);
                        assert(members(*self).contains(before[i as int].0));
                    },
                    None => {
                        assert forall|k: K| members(*self).contains(k) implies !key.eq_spec(&k) by {
                            let i = choose|i: int| 0 <= i < keys_of(before).len()
                                && keys_of(before)[i] == k;
                            assert(!key.eq_spec(&before[i].0));
                        }
                    },
                }
            }
        }
        if found.is_some() {
            return false;
        }
        self.inner.insert_fresh(key, ());
        proof {
            assert(keys_of(self.inner@) =~= keys_of(before).push(key));
            keys_of(before).lemma_push_to_set_commute(key);
        }
        true
    }
}

/// Lists keyed by `eq_spec` class; no two stored keys are `eq_spec`-equal.
pub(crate) struct NativeGroups<K: Eq + KeyHash, V> {
    pub(crate) inner: KeyedMap<K, Vec<V>>,
}

/// Each stored key's list.
pub(crate) open spec fn groups<K: Eq + KeyHash, V>(m: NativeGroups<K, V>) -> Map<K, Seq<V>> {
    Map::new(
        keys_of(m.inner@).to_set(),
        |k: K| m.inner@[choose|i: int| 0 <= i < m.inner@.len() && m.inner@[i].0 == k].1@,
    )
}

impl<K: Eq + KeyHash, V> NativeGroups<K, V> {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        key_laws::<K>() ==> forall|i: int, j: int| 0 <= i < j < self.inner@.len()
            ==> !self.inner@[i].0.eq_spec(&self.inner@[j].0)
    }

    /// The stored key at `i` names exactly the `i`th list.
    proof fn lemma_group_index(self, i: int)
        requires self.inv(), key_laws::<K>(), 0 <= i < self.inner@.len(),
        ensures groups(self).dom().contains(self.inner@[i].0),
            groups(self)[self.inner@[i].0] == self.inner@[i].1@,
    {
        let k = self.inner@[i].0;
        assert(keys_of(self.inner@)[i] == k);
        let j = choose|j: int| 0 <= j < self.inner@.len() && self.inner@[j].0 == k;
        if j != i {
            assert(self.inner@[i].0.eq_spec(&self.inner@[j].0));
            assert(false);
        }
    }

    /// Every stored key is some entry's key.
    proof fn lemma_dom(self, k: K)
        requires groups(self).dom().contains(k),
        ensures exists|i: int| 0 <= i < self.inner@.len() && self.inner@[i].0 == k,
    {
        let i = choose|i: int| 0 <= i < keys_of(self.inner@).len() && keys_of(self.inner@)[i] == k;
        assert(self.inner@[i].0 == k);
    }

    pub(crate) fn new() -> (m: Self)
        ensures groups(m) == Map::<K, Seq<V>>::empty(),
    {
        let m = Self { inner: KeyedMap::new() };
        proof { assert(groups(m) =~= Map::<K, Seq<V>>::empty()); }
        m
    }

    pub(crate) fn get(&self, key: &K) -> (value: Option<&Vec<V>>)
        ensures key_laws::<K>() ==> match value {
            Some(values) => exists|k: K| groups(*self).dom().contains(k)
                && key.eq_spec(&k) && values@ == groups(*self)[k],
            None => forall|k: K| groups(*self).dom().contains(k) ==> !key.eq_spec(&k),
        },
    {
        proof { use_type_invariant(&*self); }
        let found = self.inner.find(key);
        proof {
            if key_laws::<K>() {
                match found {
                    Some(i) => self.lemma_group_index(i as int),
                    None => {
                        assert forall|k: K| groups(*self).dom().contains(k)
                            implies !key.eq_spec(&k) by {
                            self.lemma_dom(k);
                            let i = choose|i: int| 0 <= i < self.inner@.len()
                                && self.inner@[i].0 == k;
                            assert(!key.eq_spec(&self.inner@[i].0));
                        }
                    },
                }
            }
        }
        match found {
            Some(i) => Some(&self.inner.at(i).1),
            None => None,
        }
    }

    // `vec![]` has no vstd spec; the verified `Vec::new` + `push` do.
    #[allow(clippy::vec_init_then_push)]
    pub(crate) fn push(&mut self, key: K, value: V)
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
        proof { use_type_invariant(&*self); }
        let ghost before = *self;
        let mut inner = KeyedMap::new();
        core::mem::swap(&mut self.inner, &mut inner);
        let found = inner.find(&key);
        match found {
            Some(i) => inner.push_at(i, value),
            None => {
                let mut group = Vec::new();
                group.push(value);
                inner.insert_fresh(key, group);
            },
        }
        self.inner = inner;
        proof {
            if key_laws::<K>() {
                let old_entries = before.inner@;
                match found {
                    Some(i) => {
                        before.lemma_group_index(i as int);
                        assert(keys_of(self.inner@) =~= keys_of(old_entries));
                        assert forall|k: K| groups(before).dom().contains(k)
                            implies groups(*self)[k] == (
                                if key.eq_spec(&k) { groups(before)[k].push(value) }
                                else { groups(before)[k] }) by {
                            before.lemma_dom(k);
                            let j = choose|j: int| 0 <= j < old_entries.len() && old_entries[j].0 == k;
                            before.lemma_group_index(j);
                            self.lemma_group_index(j);
                            if key.eq_spec(&k) {
                                assert(old_entries[i as int].0.eq_spec(&old_entries[j].0));
                                assert(j == i);
                            } else {
                                assert(j != i);
                            }
                        }
                    },
                    None => {
                        assert(keys_of(self.inner@) =~= keys_of(old_entries).push(key));
                        keys_of(old_entries).lemma_push_to_set_commute(key);
                        assert forall|k: K| groups(before).dom().contains(k)
                            implies !key.eq_spec(&k) && groups(*self)[k] == groups(before)[k] by {
                            before.lemma_dom(k);
                            let j = choose|j: int| 0 <= j < old_entries.len() && old_entries[j].0 == k;
                            before.lemma_group_index(j);
                            self.lemma_group_index(j);
                        }
                        self.lemma_group_index(old_entries.len() as int);
                        assert(groups(*self)[key] =~= Seq::<V>::empty().push(value));
                    },
                }
            }
        }
    }
}

} // verus!
