//! Fixed-capacity hash consing. Call `free` to release the chunk; stored destructors never run.
use crate::{index::Buckets, HashKey};
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::marker::PhantomData;
#[cfg(verus_only)]
use verus_bumpalo::{back_wf, Alloc, Id};
use verus_bumpalo::{AllocErr, Bump, BumpState, BumpTok};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::raw_ptr::PointsToRaw;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref, PointsTo};
#[cfg(verus_only)]
use vstd::std_specs::cmp::OrdSpec;

verus! {

#[verifier::accept_recursive_types(T)]
pub struct BHConsed<T> { cid: usize, uid: usize, _t: PhantomData<T> }

impl<T> Clone for BHConsed<T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    { *self }
}
impl<T> Copy for BHConsed<T> {}

impl<T> BHConsed<T> {
    pub closed spec fn spec_uid(&self) -> usize { self.uid }
    pub closed spec fn spec_cid(&self) -> usize { self.cid }

    #[verifier::when_used_as_spec(spec_uid)]
    pub fn uid(&self) -> (u: usize)
        ensures u == self.spec_uid(),
    { self.uid }

    #[verifier::when_used_as_spec(spec_cid)]
    pub fn cid(&self) -> (c: usize)
        ensures c == self.spec_cid(),
    { self.cid }
}

impl<T> PartialEq for BHConsed<T> {
    fn eq(&self, other: &Self) -> (r: bool)
        ensures r == (self.spec_cid() == other.spec_cid() && self.spec_uid() == other.spec_uid()),
    { self.cid == other.cid && self.uid == other.uid }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::PartialEqSpecImpl for BHConsed<T> {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.spec_cid() == other.spec_cid() && self.spec_uid() == other.spec_uid()
    }
}
impl<T> Eq for BHConsed<T> {}
impl<T> PartialOrd for BHConsed<T> {
    fn partial_cmp(&self, other: &Self) -> (r: Option<Ordering>)
        ensures r == Some(if self.spec_cid() == other.spec_cid() {
            self.spec_uid().cmp_spec(&other.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&other.spec_cid())
        }),
    {
        Some(if self.cid == other.cid { self.uid.cmp(&other.uid) } else { self.cid.cmp(&other.cid) })
    }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::PartialOrdSpecImpl for BHConsed<T> {
    open spec fn obeys_partial_cmp_spec() -> bool { true }
    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        Some(if self.spec_cid() == other.spec_cid() {
            self.spec_uid().cmp_spec(&other.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&other.spec_cid())
        })
    }
}
impl<T> Ord for BHConsed<T> {
    fn cmp(&self, other: &Self) -> (r: Ordering)
        ensures r == if self.spec_cid() == other.spec_cid() {
            self.spec_uid().cmp_spec(&other.spec_uid())
        } else {
            self.spec_cid().cmp_spec(&other.spec_cid())
        },
    { if self.cid == other.cid { self.uid.cmp(&other.uid) } else { self.cid.cmp(&other.cid) } }
}
#[cfg(verus_only)]
impl<T> vstd::std_specs::cmp::OrdSpecImpl for BHConsed<T> {
    open spec fn obeys_cmp_spec() -> bool { true }
    open spec fn cmp_spec(&self, other: &Self) -> Ordering {
        if self.spec_cid() == other.spec_cid() {
            OrdSpec::cmp_spec(&self.spec_uid(), &other.spec_uid())
        } else {
            OrdSpec::cmp_spec(&self.spec_cid(), &other.spec_cid())
        }
    }
}

pub struct BHConsign<T: HashKey> {
    bump: Bump,
    st: Tracked<BumpState>,
    ptrs: Vec<*mut T>,
    perms: Tracked<Map<nat, (PointsTo<T>, BumpTok)>>,
    index: Buckets,
    cid: usize,
}

// SAFETY: the consign owns its chunk and all stored keys. Insertion, reservation,
// and reclamation require ownership or &mut self; moving keys requires T: Send.
#[verifier::external]
unsafe impl<T: HashKey + Send> Send for BHConsign<T> {}

// SAFETY: shared methods only read keys and index metadata. References borrow the
// consign, preventing mutation/free while shared, and T: Sync permits shared keys.
#[verifier::external]
unsafe impl<T: HashKey + Sync> Sync for BHConsign<T> {}

impl<T: HashKey> View for BHConsign<T> {
    type V = Seq<T::V>;
    closed spec fn view(&self) -> Seq<T::V> {
        Seq::new(self.ptrs@.len(), |i: int| self.perms@[i as nat].0.value()@)
    }
}

spec fn perms_wf<T>(perms: Map<nat, (PointsTo<T>, BumpTok)>, n: nat, st: BumpState) -> bool {
    &&& forall|i: nat| i < n ==> #[trigger] perms.dom().contains(i) && {
        let (pt, tok) = perms[i];
        &&& pt.is_init()
        &&& pt.ptr()@.provenance == st.provenance()
        &&& tok.inst() == st.inst()
        &&& tok.alloc() == Alloc { addr: pt.ptr().addr(), size: size_of::<T>() }
        &&& st.outstanding().contains(tok.id())
    }
    &&& forall|i: nat, j: nat| i < n && j < n && i != j
        ==> perms[i].1.id() != perms[j].1.id()
}

impl<T: HashKey> BHConsign<T> {
    pub closed spec fn hashes(self) -> Seq<u64> {
        self@.map_values(|v: T::V| T::spec_hash(v))
    }
    pub closed spec fn remaining(self) -> int { self.bump.remaining(self.st@) }
    pub closed spec fn capacity(self) -> int { self.bump.capacity() }
    pub closed spec fn aligned(self) -> bool {
        self.bump.cursor(self.st@) as int % align_of::<T>() as int == 0
    }
    pub closed spec fn spec_cid(self) -> usize { self.cid }
    pub open spec fn owns(self, h: BHConsed<T>) -> bool {
        h.spec_cid() == self.spec_cid() && h.spec_uid() < self@.len()
    }
    pub closed spec fn inv(self) -> bool {
        &&& self.bump.wf(self.st@)
        &&& perms_wf(self.perms@, self.ptrs@.len(), self.st@)
        &&& forall|i: nat| i < self.ptrs@.len() ==>
            self.perms@[i].0.ptr() == #[trigger] self.ptrs@[i as int]
        &&& forall|id: Id| #[trigger] self.st@.outstanding().contains(id) <==>
            exists|i: nat| i < self.ptrs@.len() && self.perms@[i].1.id() == id
        &&& self@.no_duplicates()
        &&& self.index.inv(self.hashes())
    }

    /// Creates a fixed arena, returning `AllocErr` if chunk allocation fails.
    pub fn new(arena_bytes: usize) -> (r: Result<Self, AllocErr>)
        ensures
            r matches Ok(c) ==> c.inv() && c@ == Seq::<T::V>::empty()
                && c.remaining() == arena_bytes && c.capacity() == arena_bytes
                && (align_of::<T>() <= verus_bumpalo::CHUNK_ALIGN
                    && arena_bytes as int % align_of::<T>() as int == 0 ==> c.aligned()),
    { Self::with_capacity(arena_bytes, 16) }

    /// Creates a fixed arena with an initial hash-index capacity.
    pub fn with_capacity(arena_bytes: usize, capacity: usize) -> (r: Result<Self, AllocErr>)
        ensures
            r matches Ok(c) ==> c.inv() && c@ == Seq::<T::V>::empty()
                && c.remaining() == arena_bytes && c.capacity() == arena_bytes
                && (align_of::<T>() <= verus_bumpalo::CHUNK_ALIGN
                    && arena_bytes as int % align_of::<T>() as int == 0 ==> c.aligned()),
    {
        vstd::layout::layout_for_type_is_valid::<T>();
        let (bump, Tracked(st)) = match Bump::try_with_capacity(arena_bytes) {
            Ok(pair) => pair,
            Err(e) => return Err(e),
        };
        let r = Self {
            bump, st: Tracked(st), ptrs: Vec::with_capacity(capacity),
            perms: Tracked(Map::tracked_empty()), index: Buckets::new(capacity),
            cid: crate::fresh_cid(),
        };
        proof {
            bump.lemma_wf(st);
            if align_of::<T>() <= verus_bumpalo::CHUNK_ALIGN
                && arena_bytes as int % align_of::<T>() as int == 0 {
                verus_bumpalo::lemma_chunk_align_divides(bump.start() as int, align_of::<T>() as int);
                vstd::arithmetic::div_mod::lemma_mod_adds(
                    bump.start() as int, arena_bytes as int, align_of::<T>() as int);
            }
            assert(r@ =~= Seq::<T::V>::empty());
            assert(r.hashes() =~= Seq::<u64>::empty());
            assert forall|id: Id| r.st@.outstanding().contains(id) <==>
                (exists|i: nat| i < r.ptrs@.len() && r.perms@[i].1.id() == id) by { }
        }
        Ok(r)
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    { self.ptrs.len() }

    pub fn is_empty(&self) -> (b: bool)
        ensures b == (self@.len() == 0),
    { self.ptrs.len() == 0 }

    /// Panics if `h` is not owned by this arena (uid out of range or consign id mismatch);
    /// verified callers prove the check away via `owns`.
    pub fn get(&self, h: BHConsed<T>) -> (r: &T)
        requires self.inv(), self.owns(h),
        ensures r@ == self@[h.spec_uid() as int],
    {
        vstd::pervasive::runtime_assert(h.uid < self.ptrs.len() && h.cid == self.cid);
        self.elem(h.uid)
    }

    pub fn elem(&self, uid: usize) -> (r: &T)
        requires self.inv(), uid < self@.len(),
        ensures r@ == self@[uid as int],
    {
        proof {
            reveal(perms_wf);
            assert(self.perms@.dom().contains(uid as nat));
            assert(self.perms@[uid as nat].0.is_init());
        }
        let tracked pair = self.perms.borrow().tracked_borrow(uid as nat);
        ptr_ref(self.ptrs[uid], Tracked(&pair.0))
    }

    pub fn contains(&self, x: &T) -> (b: bool)
        requires self.inv(),
        ensures b == self@.contains(x@),
    { self.find(x).is_some() }

    pub fn reserve(&mut self, additional: usize)
        requires old(self).inv(), old(self)@.len() + additional <= usize::MAX,
        ensures final(self).inv(), final(self)@ == old(self)@,
            final(self).spec_cid() == old(self).spec_cid(),
            final(self).remaining() == old(self).remaining(),
            final(self).aligned() == old(self).aligned(),
            final(self).capacity() == old(self).capacity(),
            forall|h: BHConsed<T>| old(self).owns(h) ==> #[trigger] final(self).owns(h),
    {
        let total = self.ptrs.len() + additional;
        self.ptrs.reserve(additional);
        self.index.reserve(total, Ghost(self.hashes()));
    }

    pub fn find(&self, x: &T) -> (r: Option<usize>)
        requires self.inv(),
        ensures
            r matches Some(u) ==> u < self@.len() && self@[u as int] == x@,
            r is None ==> !self@.contains(x@),
    {
        let h = x.hash();
        proof {
            self.index.lemma_nonempty(self.hashes());
            vstd::std_specs::vec::axiom_spec_len(&self.ptrs);
        }
        let bucket = self.index.bucket(h);
        let mut j = 0;
        while j < bucket.len()
            invariant
                self.inv(), h == T::spec_hash(x@), self@.len() <= usize::MAX,
                self.index.nb() > 0,
                bucket@ == self.index.bucket_of(h), j <= bucket@.len(),
                forall|k: int| 0 <= k < j ==> bucket@[k].1 < self@.len()
                    && !(bucket@[k].0 == h && self@[bucket@[k].1 as int] == x@),
            decreases bucket@.len() - j,
        {
            let (bh, u) = bucket[j];
            proof { self.index.lemma_sound(self.hashes(), h, j as int); }
            if bh == h && x.key_eq(self.elem(u)) { return Some(u); }
            j += 1;
        }
        proof {
            assert forall|u: int| 0 <= u < self@.len() implies self@[u] != x@ by {
                if self@[u] == x@ {
                    self.index.lemma_complete(self.hashes(), u);
                    assert(self.hashes()[u] == h);
                    let k = bucket@.lemma_contains_to_index((h, u as usize));
                    assert(bucket@[k] == (h, u as usize));
                }
            }
        }
        None
    }

    pub fn try_mk_is_new(&mut self, x: T) -> (r: Result<(BHConsed<T>, bool), T>)
        requires old(self).inv(), size_of::<T>() > 0,
        ensures
            final(self).inv(), final(self).spec_cid() == old(self).spec_cid(),
            old(self)@.is_prefix_of(final(self)@),
            forall|h: BHConsed<T>| old(self).owns(h) ==> #[trigger] final(self).owns(h),
            final(self).remaining() <= old(self).remaining(),
            final(self).capacity() == old(self).capacity(),
            r is Err ==> final(self).aligned() == old(self).aligned(),
            old(self).aligned() ==> final(self).aligned(),
            old(self).aligned() && (r matches Ok((h, true))) ==>
                final(self).remaining() == old(self).remaining() - size_of::<T>(),
            old(self).aligned() && r is Err ==> size_of::<T>() > old(self).remaining(),
            r matches Err(y) ==> y == x && final(self)@ == old(self)@
                && final(self).remaining() == old(self).remaining(),
            r matches Ok((h, fresh)) ==> {
                &&& final(self).owns(h) && final(self)@[h.spec_uid() as int] == x@
                &&& fresh == !old(self)@.contains(x@)
                &&& fresh ==> final(self)@ == old(self)@.push(x@)
                    && h.spec_uid() == old(self)@.len()
                    && final(self).remaining() >= old(self).remaining()
                        - (size_of::<T>() + align_of::<T>() - 1)
                &&& !fresh ==> final(self)@ == old(self)@
                    && final(self).remaining() == old(self).remaining()
            },
            size_of::<T>() + align_of::<T>() - 1 <= old(self).remaining() ==> r is Ok,
    {
        let ghost before = *self;
        match self.find(&x) {
            Some(uid) => return Ok((BHConsed { cid: self.cid, uid, _t: PhantomData }, false)),
            None => {},
        }
        let h = x.hash();
        let ghost hs = self.hashes();
        vstd::layout::layout_for_type_is_valid::<T>();
        let size = core::mem::size_of::<T>();
        let align = core::mem::align_of::<T>();
        proof {
            verus_bumpalo::lemma_pow2_witness(align);
            if self.aligned() {
                verus_bumpalo::lemma_align_down_exact(
                    self.bump.cursor(self.st@) as int, size as int, align as int);
            }
        }
        let (p, Tracked(raw), Tracked(tok)) = match self.bump.try_alloc(
            size, align, Tracked(self.st.borrow_mut())) {
            Ok(parts) => parts,
            Err(_) => return Err(x),
        };
        let ghost id = tok.id();
        let tracked mut pt = raw.into_typed::<T>(p.addr());
        let tp = p as *mut T;
        ptr_mut_write(tp, Tracked(&mut pt), x);
        let uid = self.ptrs.len();
        self.ptrs.push(tp);
        proof {
            vstd::std_specs::vec::axiom_spec_len(&self.ptrs);
            self.perms.borrow_mut().tracked_insert(uid as nat, (pt, tok));
            assert(self@ =~= before@.push(x@));
            assert(self.hashes() =~= hs.push(h));
            assert forall|i: nat| i < self.ptrs@.len()
                implies #[trigger] self.perms@.dom().contains(i) && {
                    let (pt, tok) = self.perms@[i];
                    &&& pt.is_init()
                    &&& pt.ptr()@.provenance == self.st@.provenance()
                    &&& tok.inst() == self.st@.inst()
                    &&& tok.alloc() == Alloc { addr: pt.ptr().addr(), size: size_of::<T>() }
                    &&& self.st@.outstanding().contains(tok.id())
                } by {
                if i < uid { assert(before.perms@[i].1.id() != id); }
            }
            assert forall|i: nat, j: nat| i < self.ptrs@.len() && j < self.ptrs@.len()
                && i != j implies self.perms@[i].1.id() != self.perms@[j].1.id() by {
                if i < uid && j < uid { } else if i == uid {
                    assert(before.st@.outstanding().contains(before.perms@[j].1.id()));
                } else {
                    assert(before.st@.outstanding().contains(before.perms@[i].1.id()));
                }
            }
            assert forall|a: Id| #[trigger] self.st@.outstanding().contains(a) <==>
                (exists|i: nat| i < self.ptrs@.len() && self.perms@[i].1.id() == a) by {
                assert forall|a: Id| self.st@.outstanding().contains(a) implies
                    exists|i: nat| i < self.ptrs@.len() && self.perms@[i].1.id() == a by {
                    if a == id { assert(self.perms@[uid as nat].1.id() == a); }
                    else {
                        let i = choose|i: nat| i < before.ptrs@.len()
                            && before.perms@[i].1.id() == a;
                        assert(self.perms@[i].1.id() == a);
                    }
                }
            }
            vstd::arithmetic::div_mod::lemma_mod_bound(
                before.bump.cursor(before.st@) - size_of::<T>(), align_of::<T>() as int);
        }
        self.index.insert(h, uid, Ghost(hs));
        proof {
            assert(self@.no_duplicates());
            assert forall|h: BHConsed<T>| before.owns(h) implies #[trigger] self.owns(h) by { }
        }
        Ok((BHConsed { cid: self.cid, uid, _t: PhantomData }, true))
    }

    pub fn try_mk(&mut self, x: T) -> (r: Result<BHConsed<T>, T>)
        requires old(self).inv(), size_of::<T>() > 0,
        ensures
            final(self).inv(), final(self).spec_cid() == old(self).spec_cid(),
            old(self)@.is_prefix_of(final(self)@),
            forall|h: BHConsed<T>| old(self).owns(h) ==> #[trigger] final(self).owns(h),
            final(self).remaining() <= old(self).remaining(),
            final(self).capacity() == old(self).capacity(),
            r is Err ==> final(self).aligned() == old(self).aligned(),
            old(self).aligned() ==> final(self).aligned(),
            old(self).aligned() && r is Ok && !old(self)@.contains(x@) ==>
                final(self).remaining() == old(self).remaining() - size_of::<T>(),
            old(self).aligned() && r is Err ==> size_of::<T>() > old(self).remaining(),
            r matches Err(y) ==> y == x && final(self)@ == old(self)@
                && final(self).remaining() == old(self).remaining(),
            r matches Ok(h) ==> {
                &&& final(self).owns(h) && final(self)@[h.spec_uid() as int] == x@
                &&& !old(self)@.contains(x@) ==> final(self)@ == old(self)@.push(x@)
                    && h.spec_uid() == old(self)@.len()
                    && final(self).remaining() >= old(self).remaining()
                        - (size_of::<T>() + align_of::<T>() - 1)
                &&& old(self)@.contains(x@) ==> final(self)@ == old(self)@
                    && final(self).remaining() == old(self).remaining()
            },
            size_of::<T>() + align_of::<T>() - 1 <= old(self).remaining() ==> r is Ok,
    {
        match self.try_mk_is_new(x) {
            Ok((h, _)) => Ok(h),
            Err(y) => Err(y),
        }
    }

    pub proof fn lemma_no_duplicates(self)
        requires self.inv(),
        ensures self@.no_duplicates(),
    { }

    pub proof fn lemma_uid_eq(self, h1: BHConsed<T>, h2: BHConsed<T>)
        requires self.inv(), self.owns(h1), self.owns(h2),
        ensures (h1.spec_uid() == h2.spec_uid()) <==>
            (self@[h1.spec_uid() as int] == self@[h2.spec_uid() as int]),
    { }

    /// Returns the entire arena chunk without running stored `T` destructors.
    pub fn free(self)
        requires self.inv(),
    {
        vstd::layout::layout_for_type_is_valid::<T>();
        let Tracked(st) = self.st;
        let Tracked(mut perms) = self.perms;
        let tracked back;
        proof {
            back = collect_back(&mut perms, self.ptrs@.len(), st);
            assert(back.dom() =~= st.outstanding());
        }
        self.bump.free(Tracked(st), Tracked(back));
    }
}

proof fn collect_back<T>(
    tracked perms: &mut Map<nat, (PointsTo<T>, BumpTok)>, n: nat, st: BumpState,
) -> (tracked back: Map<Id, (PointsToRaw, BumpTok)>)
    requires perms_wf(*old(perms), n, st), vstd::layout::size_of::<T>() <= usize::MAX,
    ensures
        back_wf(st, back),
        forall|id: Id| #[trigger] back.dom().contains(id) <==>
            exists|i: nat| i < n && old(perms)[i].1.id() == id,
    decreases n,
{
    let ghost original = *perms;
    reveal(perms_wf);
    if n == 0 {
        let tracked back = Map::tracked_empty();
        assert forall|id: Id| back.dom().contains(id) <==>
            (exists|i: nat| i < n && original[i].1.id() == id) by { }
        back
    } else {
        let k = (n - 1) as nat;
        assert(original.dom().contains(k));
        assert(original[k].1.inst() == st.inst());
        assert(original[k].0.ptr()@.provenance == st.provenance());
        assert(original[k].1.alloc() == Alloc {
            addr: original[k].0.ptr().addr(), size: size_of::<T>() });
        let tracked (mut pt, tok) = perms.tracked_remove(k);
        let ghost id = tok.id();
        assert(perms_wf(*perms, k, st));
        let tracked mut back = collect_back(perms, k, st);
        let ghost prefix = back;
        let ghost rest = original.remove(k);
        assert(!prefix.dom().contains(id)) by {
            if prefix.dom().contains(id) {
                let i = choose|i: nat| i < k && rest[i].1.id() == id;
                assert(original[i] == rest[i]);
                assert(original[i].1.id() != original[k].1.id());
            }
        }
        pt.leak_contents();
        let tracked raw = pt.into_raw();
        back.tracked_insert(id, (raw, tok));
        assert forall|a: Id| #[trigger] back.dom().contains(a) <==>
            (exists|i: nat| i < n && original[i].1.id() == a) by {
            if back.dom().contains(a) {
                if a == id {
                    assert(original[k].1.id() == a);
                } else {
                    let i = choose|i: nat| i < k && rest[i].1.id() == a;
                    assert(original[i] == rest[i]);
                }
            }
            if exists|i: nat| i < n && original[i].1.id() == a {
                let i = choose|i: nat| i < n && original[i].1.id() == a;
                if i < k {
                    assert(original[i] == rest[i]);
                    assert(exists|j: nat| j < k && rest[j].1.id() == a);
                    assert(prefix.dom().contains(a));
                }
            }
        }
        assert(back_wf(st, back)) by {
            assert forall|a: Id| #[trigger] back.dom().contains(a) implies {
                &&& back[a].1.inst() == st.inst()
                &&& back[a].1.id() == a
                &&& back[a].0.is_range(back[a].1.alloc().addr as int,
                    back[a].1.alloc().size as int)
                &&& back[a].0.provenance() == st.provenance()
            } by {
                if a != id { assert(prefix.dom().contains(a)); }
            }
        }
        back
    }
}

}
