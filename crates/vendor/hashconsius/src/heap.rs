//! Strong-reference heap hash consing; handles retain their values independently.
use crate::{index::Buckets, HashKey};
use alloc::vec::Vec;
use std::cmp::Ordering;
use std::sync::Arc;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::cmp::OrdSpec;

verus! {

pub struct HConsed<T> { elm: Arc<T>, uid: usize, cid: usize }

impl<T> HConsed<T> {
    pub closed spec fn spec_uid(&self) -> usize { self.uid }
    pub closed spec fn spec_cid(&self) -> usize { self.cid }
    pub closed spec fn value(self) -> T { *self.elm }
    #[verifier::when_used_as_spec(spec_uid)]
    pub fn uid(&self) -> (u: usize) ensures u == self.spec_uid() { self.uid }
    #[verifier::when_used_as_spec(spec_cid)]
    pub fn cid(&self) -> (c: usize) ensures c == self.spec_cid() { self.cid }
    pub fn get(&self) -> (r: &T) ensures *r == self.value() { &*self.elm }
}
impl<T: View> View for HConsed<T> {
    type V = T::V;
    open spec fn view(&self) -> T::V { self.value()@ }
}
impl<T> Clone for HConsed<T> {
    fn clone(&self) -> (r: Self) ensures r == *self {
        Self { elm: self.elm.clone(), uid: self.uid, cid: self.cid }
    }
}
impl<T> PartialEq for HConsed<T> {
    fn eq(&self, o: &Self) -> (r: bool)
        ensures r == (self.spec_cid() == o.spec_cid() && self.spec_uid() == o.spec_uid()),
    { self.cid == o.cid && self.uid == o.uid }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::PartialEqSpecImpl for HConsed<T> {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, o: &Self) -> bool {
        self.spec_cid() == o.spec_cid() && self.spec_uid() == o.spec_uid()
    }
}
impl<T> Eq for HConsed<T> {}
impl<T> PartialOrd for HConsed<T> {
    fn partial_cmp(&self, o: &Self) -> (r: Option<Ordering>)
        ensures r == Some(if self.spec_cid() == o.spec_cid() {
            self.spec_uid().cmp_spec(&o.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&o.spec_cid())
        }),
    { Some(if self.cid == o.cid { self.uid.cmp(&o.uid) } else { self.cid.cmp(&o.cid) }) }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::PartialOrdSpecImpl for HConsed<T> {
    open spec fn obeys_partial_cmp_spec() -> bool { true }
    open spec fn partial_cmp_spec(&self, o: &Self) -> Option<Ordering> {
        Some(if self.spec_cid() == o.spec_cid() {
            self.spec_uid().cmp_spec(&o.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&o.spec_cid())
        })
    }
}
impl<T> Ord for HConsed<T> {
    fn cmp(&self, o: &Self) -> (r: Ordering)
        ensures r == if self.spec_cid() == o.spec_cid() {
            self.spec_uid().cmp_spec(&o.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&o.spec_cid())
        },
    { if self.cid == o.cid { self.uid.cmp(&o.uid) } else { self.cid.cmp(&o.cid) } }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::OrdSpecImpl for HConsed<T> {
    open spec fn obeys_cmp_spec() -> bool { true }
    open spec fn cmp_spec(&self, o: &Self) -> Ordering {
        if self.spec_cid() == o.spec_cid() {
            OrdSpec::cmp_spec(&self.spec_uid(), &o.spec_uid())
        } else {
            OrdSpec::cmp_spec(&self.spec_cid(), &o.spec_cid())
        }
    }
}

pub struct HConsign<T: HashKey> { elems: Vec<Arc<T>>, index: Buckets, cid: usize }
impl<T: HashKey> View for HConsign<T> {
    type V = Seq<T::V>;
    closed spec fn view(&self) -> Seq<T::V> {
        self.elems@.map_values(|a: Arc<T>| a@)
    }
}
impl<T: HashKey> HConsign<T> {
    pub closed spec fn hashes(self) -> Seq<u64> {
        self@.map_values(|v: T::V| T::spec_hash(v))
    }
    pub closed spec fn spec_cid(self) -> usize { self.cid }
    pub closed spec fn inv(self) -> bool {
        self@.no_duplicates() && self.index.inv(self.hashes())
    }
    pub open spec fn owns(self, h: HConsed<T>) -> bool {
        h.spec_cid() == self.spec_cid() && h.spec_uid() < self@.len() && self@[h.spec_uid() as int] == h@
    }
    pub fn empty() -> (r: Self) ensures r.inv(), r@ == Seq::<T::V>::empty() {
        Self::with_capacity(16)
    }
    pub fn with_capacity(capacity: usize) -> (r: Self)
        ensures r.inv(), r@ == Seq::<T::V>::empty(),
    {
        let r = Self { elems: Vec::with_capacity(capacity), index: Buckets::new(capacity), cid: crate::fresh_cid() };
        assert(r@ =~= Seq::<T::V>::empty());
        assert(r.hashes() =~= Seq::<u64>::empty());
        r
    }
    pub fn len(&self) -> (n: usize) ensures n == self@.len() { self.elems.len() }
    pub fn is_empty(&self) -> (b: bool) ensures b == (self@.len() == 0) { self.elems.len() == 0 }
    pub fn elem(&self, uid: usize) -> (r: &T)
        requires uid < self@.len(),
        ensures r@ == self@[uid as int],
    { &*self.elems[uid] }
    pub fn contains(&self, x: &T) -> (b: bool)
        requires self.inv(),
        ensures b == self@.contains(x@),
    { self.find(x).is_some() }
    pub fn reserve(&mut self, additional: usize)
        requires old(self).inv(), old(self)@.len() + additional <= usize::MAX,
        ensures final(self).inv(), final(self)@ == old(self)@,
            final(self).spec_cid() == old(self).spec_cid(),
    {
        let ghost hs = self.hashes();
        let total = self.elems.len() + additional;
        self.elems.reserve(additional);
        self.index.reserve(total, Ghost(hs));
    }
    pub fn mk_is_new(&mut self, x: T) -> (r: (HConsed<T>, bool))
        requires old(self).inv(),
        ensures
            final(self).inv(), final(self).spec_cid() == old(self).spec_cid(),
            old(self)@.is_prefix_of(final(self)@),
            forall|h: HConsed<T>| old(self).owns(h) ==> #[trigger] final(self).owns(h),
            final(self).owns(r.0), r.0@ == x@,
            r.1 == !old(self)@.contains(x@),
            r.1 ==> final(self)@ == old(self)@.push(x@) && r.0.spec_uid() == old(self)@.len(),
            !r.1 ==> final(self)@ == old(self)@,
    {
        let ghost before = self@;
        match self.find(&x) {
            Some(u) => (HConsed { elm: self.elems[u].clone(), uid: u, cid: self.cid }, false),
            None => {
                let h = x.hash();
                let ghost hs = self.hashes();
                let a = Arc::new(x);
                let uid = self.elems.len();
                self.elems.push(a.clone());
                proof {
                    vstd::std_specs::vec::axiom_spec_len(&self.elems);
                    assert(self@ =~= before.push(x@));
                    assert(self.hashes() =~= hs.push(h));
                    assert(self@.no_duplicates());
                    assert(before.is_prefix_of(self@));
                }
                self.index.insert(h, uid, Ghost(hs));
                (HConsed { elm: a, uid, cid: self.cid }, true)
            }
        }
    }
    pub fn mk(&mut self, x: T) -> (h: HConsed<T>)
        requires old(self).inv(),
        ensures
            final(self).inv(), final(self).spec_cid() == old(self).spec_cid(),
            old(self)@.is_prefix_of(final(self)@),
            forall|h: HConsed<T>| old(self).owns(h) ==> #[trigger] final(self).owns(h),
            final(self).owns(h), h@ == x@,
            !old(self)@.contains(x@) ==> final(self)@ == old(self)@.push(x@) && h.spec_uid() == old(self)@.len(),
            old(self)@.contains(x@) ==> final(self)@ == old(self)@,
    { self.mk_is_new(x).0 }
    pub proof fn lemma_no_duplicates(self)
        requires self.inv(),
        ensures self@.no_duplicates(),
    { }
    pub proof fn lemma_uid_eq(self, h1: HConsed<T>, h2: HConsed<T>)
        requires self.inv(), self.owns(h1), self.owns(h2),
        ensures (h1.spec_uid() == h2.spec_uid()) <==> (h1@ == h2@),
    { }
    fn find(&self, x: &T) -> (r: Option<usize>)
        requires self.inv(),
        ensures
            r matches Some(u) ==> u < self@.len() && self@[u as int] == x@,
            r is None ==> !self@.contains(x@),
    {
        let h = x.hash();
        proof {
            self.index.lemma_nonempty(self.hashes());
            vstd::std_specs::vec::axiom_spec_len(&self.elems);
        }
        let bucket = self.index.bucket(h);
        let mut j = 0;
        while j < bucket.len()
            invariant
                self.inv(), h == T::spec_hash(x@),
                self.index.nb() > 0, self@.len() <= usize::MAX,
                bucket@ == self.index.bucket_of(h),
                0 <= j <= bucket@.len(),
                forall|k: int| 0 <= k < j ==>
                    (#[trigger] bucket@[k].1 < self@.len()
                    && !(bucket@[k].0 == h && self@[bucket@[k].1 as int] == x@)),
            decreases bucket@.len() - j,
        {
            let (bh, u) = bucket[j];
            proof { self.index.lemma_sound(self.hashes(), h, j as int); }
            if bh == h && x.key_eq(&*self.elems[u]) { return Some(u); }
            j += 1;
        }
        proof {
            assert forall|u: int| 0 <= u < self@.len() implies self@[u] != x@ by {
                if self@[u] == x@ {
                    self.index.lemma_complete(self.hashes(), u);
                    assert(self.hashes()[u] == h);
                    let k = bucket@.lemma_contains_to_index((h, u as usize));
                    assert(bucket@[k].0 == h && self@[bucket@[k].1 as int] == x@);
                }
            }
        }
        None
    }
}
}
