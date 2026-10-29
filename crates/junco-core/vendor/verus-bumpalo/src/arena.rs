//! Verified fixed-chunk containers with encapsulated allocation permissions.

#[cfg(verus_only)]
use crate::{
    back_wf, lemma_align_down_exact, lemma_chunk_align_divides, lemma_pow2_witness, Alloc, Id,
    CHUNK_ALIGN, MAX_CAP,
};
use crate::{AllocErr, Bump, BumpState, BumpTok};
use alloc::vec::Vec;
#[cfg(verus_only)]
use vstd::layout::{align_of, size_of};
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {
broadcast use vstd::set::Set::lemma_map_contains;

#[verifier::reject_recursive_types(T)]
struct TypedInner<T: Copy> {
    bump: Bump,
    ptrs: Vec<*mut T>,
    st: Tracked<BumpState>,
    perms: Tracked<Map<int, (PointsTo<T>, BumpTok)>>,
}

/// A fixed-capacity arena of copied values. Call `free` to release its chunk.
#[verifier::reject_recursive_types(T)]
pub struct TypedArena<T: Copy> {
    inner: Option<TypedInner<T>>,
}

spec fn typed_token_ids<T: Copy>(perms: Map<int, (PointsTo<T>, BumpTok)>, n: nat)
    -> Set<Id>
{
    Set::range(0int, n as int).map(|i: int| perms[i].1.id())
}

spec fn typed_permissions_wf<T: Copy>(
    perms: Map<int, (PointsTo<T>, BumpTok)>,
    n: nat,
    st: BumpState,
) -> bool {
    &&& perms.dom() == Set::range(0int, n as int)
    &&& forall|i: int| 0 <= i < n ==> {
        &&& #[trigger] perms[i].0.is_init()
        &&& perms[i].0.ptr()@.provenance == st.provenance()
        &&& perms[i].1.inst() == st.inst()
        &&& perms[i].1.alloc() == Alloc {
            addr: perms[i].0.ptr().addr(), size: size_of::<T>() as usize,
        }
        &&& st.outstanding().contains(perms[i].1.id())
    }
    &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j
        ==> #[trigger] perms[i].1.id() != #[trigger] perms[j].1.id()
}

proof fn collect_typed<T: Copy>(
    tracked mut perms: Map<int, (PointsTo<T>, BumpTok)>,
    n: nat,
    tracked st: &BumpState,
) -> (tracked back: Map<Id, (PointsToRaw, BumpTok)>)
    requires
        typed_permissions_wf(perms, n, *st),
        vstd::layout::size_of::<T>() <= usize::MAX,
    ensures
        back_wf(*st, back),
        back.dom() == typed_token_ids(perms, n),
    decreases n,
{
    let ghost original = perms;
    if n == 0 {
        let tracked back = Map::tracked_empty();
        assert(back.dom() =~= typed_token_ids(original, n));
        back
    } else {
        let i = (n - 1) as int;
        assert(perms.dom().contains(i));
        assert(original[i].0.is_init());
        let tracked (mut perm, tok) = perms.tracked_remove(i);
        let ghost id = tok.id();
        assert(typed_permissions_wf(perms, (n - 1) as nat, *st)) by {
            assert(perms.dom() =~= Set::range(0int, n - 1));
            assert forall|j: int| 0 <= j < n - 1 implies {
                &&& #[trigger] perms[j].0.is_init()
                &&& perms[j].0.ptr()@.provenance == st.provenance()
                &&& perms[j].1.inst() == st.inst()
                &&& perms[j].1.alloc() == Alloc {
                    addr: perms[j].0.ptr().addr(), size: size_of::<T>() as usize,
                }
                &&& st.outstanding().contains(perms[j].1.id())
            } by {
                assert(perms[j] == original[j]);
            }
            assert forall|j: int, k: int|
                0 <= j < n - 1 && 0 <= k < n - 1 && j != k
                implies #[trigger] perms[j].1.id() != #[trigger] perms[k].1.id()
            by {
                assert(perms[j] == original[j]);
                assert(perms[k] == original[k]);
            }
        }
        let tracked mut back = collect_typed(perms, (n - 1) as nat, st);
        let ghost previous_back = back;
        assert(!back.dom().contains(id)) by {
            if back.dom().contains(id) {
                let j = choose|j: int| 0 <= j < n - 1 && perms[j].1.id() == id;
                assert(original[j].1.id() != original[i].1.id());
            }
        }
        perm.leak_contents();
        let tracked raw = perm.into_raw();
        back.tracked_insert(id, (raw, tok));
        assert(back_wf(*st, back)) by {
            assert(back.dom() <= st.outstanding()) by {
                assert forall|k: Id| back.dom().contains(k)
                    implies st.outstanding().contains(k) by {
                    if k == id {
                        assert(original[i].0.is_init());
                        assert(st.outstanding().contains(original[i].1.id()));
                    } else {
                        assert(previous_back.dom().contains(k));
                    }
                }
            }
            assert forall|k: Id| #[trigger] back.dom().contains(k) implies {
                &&& back[k].1.inst() == st.inst()
                &&& back[k].1.id() == k
                &&& back[k].0.is_range(back[k].1.alloc().addr as int,
                    back[k].1.alloc().size as int)
                &&& back[k].0.provenance() == st.provenance()
            } by {
                if k == id {
                    assert(original[i].0.is_init());
                    assert(vstd::layout::size_of::<T>() as usize as nat
                        == vstd::layout::size_of::<T>());
                    assert(back[k].1 == original[i].1);
                    assert(back[k].0.is_range(original[i].0.ptr().addr() as int,
                        vstd::layout::size_of::<T>() as int));
                } else {
                    assert(previous_back.dom().contains(k));
                    assert(back[k] == previous_back[k]);
                }
            }
        }
        assert(back.dom() =~= typed_token_ids(original, n)) by {
            assert forall|k: Id| back.dom().contains(k)
                implies typed_token_ids(original, n).contains(k) by {
                if k == id {
                    assert(original[i].1.id() == k);
                } else {
                    let j = choose|j: int| 0 <= j < n - 1 && perms[j].1.id() == k;
                    assert(original[j].1.id() == k);
                }
            }
            assert forall|k: Id| typed_token_ids(original, n).contains(k)
                implies back.dom().contains(k) by {
                let j = choose|j: int| 0 <= j < n && original[j].1.id() == k;
                if j != i {
                    assert(perms[j].1.id() == k);
                    assert(typed_token_ids(perms, (n - 1) as nat).contains(k));
                }
            }
        }
        back
    }
}

impl<T: Copy> TypedInner<T> {
    closed spec fn wf(&self) -> bool {
        &&& self.bump.wf(self.st@)
        &&& typed_permissions_wf(self.perms@, self.ptrs@.len(), self.st@)
        &&& forall|i: int| 0 <= i < self.ptrs@.len()
            ==> #[trigger] self.perms@[i].0.ptr() == self.ptrs@[i]
        &&& self.st@.outstanding() == typed_token_ids(self.perms@, self.ptrs@.len())
    }

    closed spec fn view(&self) -> Seq<T> {
        Seq::new(self.ptrs@.len(), |i: int| self.perms@[i].0.value())
    }

    closed spec fn capacity(&self) -> int { self.bump.capacity() }
    closed spec fn remaining(&self) -> int { self.bump.remaining(self.st@) }
    closed spec fn aligned(&self) -> bool {
        self.bump.cursor(self.st@) as int % align_of::<T>() as int == 0
    }

    fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.view().len(),
    {
        self.ptrs.len()
    }

    fn get(&self, index: usize) -> (r: Option<&T>)
        requires self.wf(),
        ensures
            r matches Some(v) ==> index < self.view().len()
                && *v == self.view()[index as int],
            r is None ==> index >= self.view().len(),
    {
        match self.ptrs.get(index) {
            Some(p) => {
                let tracked perm = &self.perms.borrow().tracked_borrow(index as int).0;
                Some(ptr_ref(*p as *const T, Tracked(perm)))
            }
            None => None,
        }
    }

    fn try_push(&mut self, value: T) -> (r: Result<usize, AllocErr>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).capacity() == old(self).capacity(),
            r matches Ok(i) ==> i == old(self).view().len()
                && final(self).view() == old(self).view().push(value),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).remaining() == old(self).remaining()
                && final(self).aligned() == old(self).aligned(),
            old(self).aligned() && r is Ok ==> final(self).aligned()
                && final(self).remaining() == old(self).remaining() - size_of::<T>(),
            old(self).aligned() && r == Err(AllocErr::Exhausted)
                ==> size_of::<T>() > old(self).remaining(),
    {
        let ghost previous_ptrs = self.ptrs@;
        let ghost previous_perms = self.perms@;
        let ghost previous_st = self.st@;
        let ghost previous_view = self.view();
        proof {
            assert(typed_permissions_wf(previous_perms, previous_ptrs.len(), previous_st));
        }
        if self.ptrs.try_reserve(1).is_err() {
            return Err(AllocErr::Global);
        }
        vstd::layout::layout_for_type_is_valid::<T>();
        let size = core::mem::size_of::<T>();
        let align = core::mem::align_of::<T>();
        proof {
            lemma_pow2_witness(align);
            if self.aligned() {
                lemma_align_down_exact(self.bump.cursor(self.st@) as int, size as int, align as int);
            }
        }
        let (p8, Tracked(raw), Tracked(tok)) = match self.bump.try_alloc(
            size, align, Tracked(self.st.borrow_mut()),
        ) {
            Ok(allocation) => allocation,
            Err(error) => { return Err(error); }
        };
        let p: *mut T = cast_ptr_to_thin_ptr(p8);
        let ghost addr = p.addr();
        proof {
            assert(addr as int % vstd::layout::align_of::<T>() as int == 0);
            assert(raw.is_range(addr as int, vstd::layout::size_of::<T>() as int));
        }
        let tracked mut perm = raw.into_typed::<T>(addr);
        proof {
            broadcast use group_raw_ptr_axioms;
            assert(perm.ptr()@ == p@);
            assert(perm.ptr() == p);
        }
        ptr_mut_write(p, Tracked(&mut perm), value);
        let index = self.ptrs.len();
        let ghost id = tok.id();
        self.ptrs.push(p);
        proof {
            self.perms.borrow_mut().tracked_insert(index as int, (perm, tok));
            assert(self.perms@.dom() =~= Set::range(0int, self.ptrs@.len() as int));
            assert forall|i: int| 0 <= i < self.ptrs@.len() implies {
                &&& #[trigger] self.perms@[i].0.is_init()
                &&& self.perms@[i].0.ptr()@.provenance == self.st@.provenance()
                &&& self.perms@[i].1.inst() == self.st@.inst()
                &&& self.perms@[i].1.alloc() == Alloc {
                    addr: self.perms@[i].0.ptr().addr(), size: size_of::<T>() as usize,
                }
                &&& self.st@.outstanding().contains(self.perms@[i].1.id())
            } by {
                if i != index as int {
                    assert(self.perms@[i] == previous_perms[i]);
                    assert(previous_perms[i].0.is_init());
                    assert(previous_st.outstanding().contains(previous_perms[i].1.id()));
                }
            }
            assert forall|i: int, j: int|
                0 <= i < self.ptrs@.len() && 0 <= j < self.ptrs@.len() && i != j
                implies #[trigger] self.perms@[i].1.id() != #[trigger] self.perms@[j].1.id()
            by {
                if i == index as int {
                    assert(previous_perms[j].0.is_init());
                    assert(previous_st.outstanding().contains(previous_perms[j].1.id()));
                } else if j == index as int {
                    assert(previous_perms[i].0.is_init());
                    assert(previous_st.outstanding().contains(previous_perms[i].1.id()));
                } else {
                    assert(previous_perms[i].1.id() != previous_perms[j].1.id());
                }
            }
            assert forall|i: int| 0 <= i < self.ptrs@.len()
                implies #[trigger] self.perms@[i].0.ptr() == self.ptrs@[i] by {
                if i != index as int {
                    assert(self.perms@[i] == previous_perms[i]);
                    assert(self.ptrs@[i] == previous_ptrs[i]);
                }
            }
            assert(typed_token_ids(self.perms@, self.ptrs@.len())
                =~= typed_token_ids(previous_perms, previous_ptrs.len()).insert(id)) by {
                assert forall|k: Id| typed_token_ids(self.perms@, self.ptrs@.len()).contains(k)
                    implies typed_token_ids(previous_perms, previous_ptrs.len()).insert(id).contains(k)
                by {
                    let i = choose|i: int| 0 <= i < self.ptrs@.len()
                        && self.perms@[i].1.id() == k;
                    if i != index as int {
                        assert(previous_perms[i].1.id() == k);
                        assert(typed_token_ids(previous_perms, previous_ptrs.len()).contains(k));
                    }
                }
                assert forall|k: Id| typed_token_ids(previous_perms, previous_ptrs.len()).insert(id).contains(k)
                    implies typed_token_ids(self.perms@, self.ptrs@.len()).contains(k)
                by {
                    if k == id {
                        assert(self.perms@[index as int].1.id() == k);
                        assert(Set::range(0int, self.ptrs@.len() as int).contains(index as int));
                        assert(exists|i: int| 0 <= i < self.ptrs@.len() && self.perms@[i].1.id() == k);
                    } else {
                        let i = choose|i: int| 0 <= i < previous_ptrs.len()
                            && previous_perms[i].1.id() == k;
                        assert(self.perms@[i].1.id() == k);
                        assert(Set::range(0int, self.ptrs@.len() as int).contains(i));
                        assert(exists|j: int| 0 <= j < self.ptrs@.len() && self.perms@[j].1.id() == k);
                    }
                }
            }
            assert(self.wf());
            assert(self.view() =~= previous_view.push(value));
        }
        Ok(index)
    }

    fn free(self)
        requires self.wf(),
    {
        vstd::layout::layout_for_type_is_valid::<T>();
        let TypedInner { bump, ptrs, st: Tracked(st), perms: Tracked(perms) } = self;
        let tracked back = collect_typed(perms, ptrs@.len(), &st);
        proof { assert(back.dom() == st.outstanding()); }
        bump.free(Tracked(st), Tracked(back));
    }
}

impl<T: Copy> View for TypedArena<T> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Seq<T> {
        match self.inner {
            Some(inner) => inner.view(),
            None => Seq::empty(),
        }
    }
}

impl<T: Copy> TypedArena<T> {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        self.inner is Some ==> self.inner->0.wf()
    }

    /// Chunk size in bytes (0 without a chunk).
    pub closed spec fn capacity(&self) -> int {
        match self.inner { Some(inner) => inner.capacity(), None => 0 }
    }

    /// Bytes below the cursor (0 without a chunk).
    pub closed spec fn remaining(&self) -> int {
        match self.inner { Some(inner) => inner.remaining(), None => 0 }
    }

    /// The cursor is a multiple of `align_of::<T>()`, so pushes never pad.
    pub closed spec fn aligned(&self) -> bool {
        self.inner matches Some(inner) ==> inner.aligned()
    }

    /// Creates an empty arena backed by one fixed-size chunk.
    pub fn with_capacity(capacity: usize) -> (r: Result<Self, AllocErr>)
        ensures
            r matches Ok(arena) ==> arena@ == Seq::<T>::empty()
                && arena.capacity() == capacity && arena.remaining() == capacity
                && (align_of::<T>() <= CHUNK_ALIGN
                    && capacity as int % align_of::<T>() as int == 0 ==> arena.aligned()),
            capacity == 0 || capacity > MAX_CAP ==> r == Err(AllocErr::Capacity),
    {
        let (bump, Tracked(st)) = Bump::try_with_capacity(capacity)?;
        let ptrs = Vec::new();
        let tracked perms = Map::tracked_empty();
        proof {
            assert(typed_token_ids::<T>(perms, 0) =~= Set::empty());
            assert(perms.dom() =~= Set::range(0int, 0int));
            lemma_cursor_aligned::<T>(bump, st, capacity);
        }
        Ok(TypedArena { inner: Some(TypedInner {
            bump, ptrs, st: Tracked(st), perms: Tracked(perms),
        }) })
    }

    /// Returns the number of initialized values.
    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        proof { use_type_invariant(self); }
        match &self.inner {
            Some(inner) => inner.len(),
            None => 0,
        }
    }

    /// Borrows the value at `index`, if present.
    pub fn get(&self, index: usize) -> (r: Option<&T>)
        ensures
            r matches Some(v) ==> index < self@.len() && *v == self@[index as int],
            r is None ==> index >= self@.len(),
    {
        proof { use_type_invariant(self); }
        match &self.inner {
            Some(inner) => inner.get(index),
            None => None,
        }
    }

    /// Appends a copy, leaving the sequence unchanged on allocation failure.
    ///
    /// From an aligned cursor a push consumes exactly `size_of::<T>()` bytes and fails
    /// with `Exhausted` only when that many bytes are not left.
    pub fn try_push(&mut self, value: T) -> (r: Result<usize, AllocErr>)
        ensures
            final(self).capacity() == old(self).capacity(),
            r matches Ok(i) ==> i == old(self)@.len()
                && final(self)@ == old(self)@.push(value),
            r is Err ==> final(self)@ == old(self)@
                && final(self).remaining() == old(self).remaining()
                && final(self).aligned() == old(self).aligned(),
            old(self).aligned() && r is Ok ==> final(self).aligned()
                && final(self).remaining() == old(self).remaining() - size_of::<T>(),
            old(self).aligned() && r == Err(AllocErr::Exhausted)
                ==> size_of::<T>() > old(self).remaining(),
    {
        proof { use_type_invariant(&*self); }
        let inner = self.inner.take();
        match inner {
            Some(mut inner) => {
                let result = inner.try_push(value);
                self.inner = Some(inner);
                result
            }
            None => Err(AllocErr::Global),
        }
    }

    /// Releases the chunk and pointer table without running value destructors.
    pub fn free(self) {
        proof { use_type_invariant(&self); }
        if let Some(inner) = self.inner {
            inner.free();
        }
    }
}

/// A fresh chunk's cursor (`start + capacity`) is `T`-aligned when `T`'s alignment fits
/// the chunk alignment and divides the capacity.
proof fn lemma_cursor_aligned<T>(bump: Bump, st: BumpState, capacity: usize)
    requires bump.wf(st), bump.remaining(st) == capacity,
    ensures
        align_of::<T>() <= CHUNK_ALIGN && capacity as int % align_of::<T>() as int == 0
            ==> bump.cursor(st) as int % align_of::<T>() as int == 0,
{
    broadcast use vstd::layout::align_properties, vstd::layout::align_nonzero;
    if align_of::<T>() <= CHUNK_ALIGN && capacity as int % align_of::<T>() as int == 0 {
        bump.lemma_wf(st);
        lemma_chunk_align_divides(bump.start() as int, align_of::<T>() as int);
        vstd::arithmetic::div_mod::lemma_small_mod(0, align_of::<T>());
        vstd::arithmetic::div_mod::lemma_add_mod_noop(
            bump.start() as int, capacity as int, align_of::<T>() as int,
        );
    }
}


#[verifier::reject_recursive_types(T)]
pub tracked struct SlicePerm<T> {
    tracked elems: Map<int, PointsTo<T>>,
    ghost base: *mut T,
    ghost len: nat,
}

impl<T> SlicePerm<T> {
    pub closed spec fn ptr(self) -> *mut T { self.base }
    pub closed spec fn len(self) -> nat { self.len }
    pub closed spec fn elem_ptr(self, i: int) -> *mut T {
        self.base.with_addr((self.base.addr() + i * size_of::<T>()) as usize)
    }
    pub closed spec fn wf(self) -> bool {
        &&& self.base.addr() != 0
        &&& self.base.addr() as int % align_of::<T>() as int == 0
        &&& self.len * size_of::<T>() <= isize::MAX
        &&& self.base.addr() + self.len * size_of::<T>() <= usize::MAX
        &&& self.elems.dom() == Set::range(0int, self.len as int)
        &&& forall|i: int| 0 <= i < self.len ==> {
            &&& #[trigger] self.elems[i].ptr() == self.elem_ptr(i)
            &&& self.elems[i].is_init()
            &&& self.elems[i].ptr()@.provenance == self.base@.provenance
        }
    }
    pub closed spec fn values(self) -> Seq<T> {
        Seq::new(self.len, |i: int| self.elems[i].value())
    }
    pub proof fn into_raw(tracked self) -> (tracked raw: PointsToRaw)
        requires self.wf(),
        ensures
            raw.is_range(self.ptr().addr() as int, (self.len() * size_of::<T>()) as int),
            raw.provenance() == self.ptr()@.provenance,
    {
        broadcast use vstd::raw_ptr::group_raw_ptr_axioms;
        assert forall|i: int| 0 <= i < self.len implies {
            &&& self.elems[i].ptr().addr() == self.base.addr() + i * size_of::<T>()
            &&& self.elems[i].ptr()@.provenance == self.base@.provenance
            &&& self.elems[i].is_init()
        } by {
            assert(self.elems[i].ptr() == self.elem_ptr(i));
            assert(0 <= self.base.addr() + i * size_of::<T>() <= usize::MAX) by (nonlinear_arith)
                requires 0 <= i < self.len, self.base.addr() + self.len * size_of::<T>() <= usize::MAX;
        }
        slice_elems_into_raw(self.elems, self.base, self.len)
    }
}

proof fn slice_elems_into_raw<T>(tracked elems: Map<int, PointsTo<T>>, base: *mut T, n: nat)
    -> (tracked raw: PointsToRaw)
    requires
        base.addr() + n * size_of::<T>() <= usize::MAX,
        elems.dom() == Set::range(0int, n as int),
        forall|i: int| 0 <= i < n ==> {
            &&& #[trigger] elems[i].ptr().addr() == base.addr() + i * size_of::<T>()
            &&& elems[i].ptr()@.provenance == base@.provenance
            &&& elems[i].is_init()
        },
    ensures
        raw.is_range(base.addr() as int, (n * size_of::<T>()) as int),
        raw.provenance() == base@.provenance,
    decreases n,
{
    if n == 0 {
        let tracked raw = PointsToRaw::empty(base@.provenance);
        assert(raw.dom() =~= Set::range(base.addr() as int, base.addr() as int));
        raw
    } else {
        let tracked mut elems = elems;
        let ghost i = (n - 1) as int;
        let tracked mut elem = elems.tracked_remove(i);
        assert(elems.dom() =~= Set::range(0int, n - 1));
        assert(base.addr() + (n - 1) * size_of::<T>() <= usize::MAX) by (nonlinear_arith)
            requires n > 0, base.addr() + n * size_of::<T>() <= usize::MAX;
        let tracked prefix = slice_elems_into_raw(elems, base, (n - 1) as nat);
        elem.leak_contents();
        let tracked tail = elem.into_raw();
        let tracked raw = prefix.join(tail);
        assert(base.addr() + n * size_of::<T>() ==
            base.addr() + (n - 1) * size_of::<T>() + size_of::<T>()) by (nonlinear_arith);
        assert forall|x: int| raw.dom().contains(x) <==>
            Set::range(base.addr() as int, base.addr() + n * size_of::<T>()).contains(x) by {
            assert(prefix.dom().contains(x) <==> base.addr() <= x < base.addr() + (n - 1) * size_of::<T>());
            assert(tail.dom().contains(x) <==> base.addr() + (n - 1) * size_of::<T>() <= x < base.addr() + n * size_of::<T>());
        }
        assert(raw.dom() =~= Set::range(base.addr() as int, base.addr() + n * size_of::<T>()));
        raw
    }
}

/// Trusted: forms a shared slice from nonnull, aligned, initialized contiguous
/// elements with one allocation provenance and at most isize::MAX bytes.
#[verifier::external_body]
pub fn slice_ref<'a, T>(p: *mut T, len: usize, Tracked(perm): Tracked<&'a SlicePerm<T>>)
    -> (s: &'a [T])
    requires perm.wf(), perm.ptr() == p, perm.len() == len,
    ensures s@ == perm.values(),
{
    // SAFETY: wf supplies alignment/non-nullness even for empty/ZST slices,
    // initialized permissions with one provenance, and the slice byte bound.
    unsafe { core::slice::from_raw_parts(p, len) }
}

#[verifier::reject_recursive_types(T)]
struct SliceInner<T: Copy> {
    bump: Bump,
    slices: Vec<(*mut T, usize)>,
    st: Tracked<BumpState>,
    perms: Tracked<Map<int, (SlicePerm<T>, BumpTok)>>,
}

#[verifier::reject_recursive_types(T)]
pub struct SliceArena<T: Copy> {
    inner: Option<SliceInner<T>>,
}

// SAFETY: the arena exclusively owns its chunk and copied elements. All mutation
// and reclamation require ownership or &mut self; moving T requires T: Send.
#[verifier::external]
unsafe impl<T: Copy + Send> Send for SliceArena<T> {}

// SAFETY: shared access only reads initialized elements and pointer metadata;
// returned slices borrow the arena, so sharing them requires T: Sync.
#[verifier::external]
unsafe impl<T: Copy + Sync> Sync for SliceArena<T> {}

impl<T: Copy> SliceInner<T> {
    closed spec fn wf(&self) -> bool {
        &&& self.bump.wf(self.st@)
        &&& self.perms@.dom() == Set::range(0int, self.slices@.len() as int)
        &&& forall|i: int| 0 <= i < self.slices@.len() ==> {
            &&& #[trigger] self.perms@[i].0.wf()
            &&& self.perms@[i].0.ptr() == self.slices@[i].0
            &&& self.perms@[i].0.len() == self.slices@[i].1
            &&& self.perms@[i].0.ptr()@.provenance == self.st@.provenance()
            &&& self.perms@[i].1.inst() == self.st@.inst()
            &&& self.st@.outstanding().contains(self.perms@[i].1.id())
            &&& self.perms@[i].1.alloc() == (Alloc {
                addr: self.slices@[i].0.addr(),
                size: (self.slices@[i].1 * size_of::<T>()) as usize,
            })
        }
        &&& forall|i: int, j: int| 0 <= i < self.slices@.len() && 0 <= j < self.slices@.len()
            && i != j ==> #[trigger] self.perms@[i].1.id() != #[trigger] self.perms@[j].1.id()
        &&& forall|k: Id| self.st@.outstanding().contains(k) <==>
            exists|i: int| 0 <= i < self.slices@.len() && #[trigger] self.perms@[i].1.id() == k
    }
    closed spec fn view(&self) -> Seq<Seq<T>> {
        Seq::new(self.slices@.len(), |i: int| self.perms@[i].0.values())
    }

    closed spec fn capacity(&self) -> int { self.bump.capacity() }
    closed spec fn remaining(&self) -> int { self.bump.remaining(self.st@) }
    closed spec fn aligned(&self) -> bool {
        self.bump.cursor(self.st@) as int % align_of::<T>() as int == 0
    }

    fn get(&self, index: usize) -> (r: Option<&[T]>)
        requires self.wf(),
        ensures
            r matches Some(s) ==> index < self.view().len() && s@ == self.view()[index as int],
            r is None ==> index >= self.view().len(),
    {
        match self.slices.get(index) {
            Some(entry) => {
                let tracked perm = &self.perms.borrow().tracked_borrow(index as int).0;
                proof { assert(self.perms@[index as int].0.wf()); }
                Some(slice_ref(entry.0, entry.1, Tracked(perm)))
            },
            None => None,
        }
    }

    fn try_push(&mut self, values: &[T]) -> (r: Result<usize, AllocErr>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).capacity() == old(self).capacity(),
            r matches Ok(i) ==> i == old(self).view().len()
                && final(self).view() == old(self).view().push(values@),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).remaining() == old(self).remaining()
                && final(self).aligned() == old(self).aligned(),
            old(self).aligned() && r is Ok ==> final(self).aligned()
                && final(self).remaining() == old(self).remaining() - values@.len() * size_of::<T>(),
            old(self).aligned() && r == Err(AllocErr::Exhausted)
                ==> values@.len() * size_of::<T>() > old(self).remaining(),
    {
        if self.slices.try_reserve(1).is_err() { return Err(AllocErr::Global); }
        vstd::layout::layout_for_type_is_valid::<T>();
        proof { self.bump.lemma_wf(self.st@); }
        let size = match values.len().checked_mul(core::mem::size_of::<T>()) {
            Some(size) => size,
            None => return Err(AllocErr::Exhausted),
        };
        let align = core::mem::align_of::<T>();
        proof {
            broadcast use vstd::layout::align_nonzero;
            lemma_pow2_witness(align);
            vstd::arithmetic::div_mod::lemma_small_mod(0, align as nat);
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(
                size_of::<T>() as int, values@.len() as int, align as int,
            );
            assert(size as int == values@.len() * size_of::<T>());
            assert(size as int % align as int == 0);
            if self.aligned() {
                lemma_align_down_exact(self.bump.cursor(self.st@) as int, size as int, align as int);
            }
        }
        let ghost old_perms = self.perms@;
        let ghost old_slices = self.slices@;
        let ghost old_st = self.st@;
        let (p8, Tracked(raw), Tracked(tok)) = match
            self.bump.try_alloc(size, align, Tracked(self.st.borrow_mut())) {
            Ok(a) => a,
            Err(e) => return Err(e),
        };
        let p: *mut T = cast_ptr_to_thin_ptr(p8);
        let n = values.len();
        let stride = core::mem::size_of::<T>();
        let base = p.addr();
        let tracked mut rest = raw;
        let tracked mut elems = Map::<int, PointsTo<T>>::tracked_empty();
        proof {
            broadcast use vstd::raw_ptr::group_raw_ptr_axioms;
            broadcast use vstd::layout::align_properties;
            broadcast use vstd::layout::align_nonzero;
            assert(align_of::<T>() > 0);
            assert(size_of::<T>() % align_of::<T>() == 0);
            assert(p@.provenance == p8@.provenance);
            assert(base == p8.addr());
        }
        let mut i: usize = 0;
        let ghost allocated_st = self.st@;
        while i < n
            invariant
                old(self).wf(),
                old_slices == old(self).slices@,
                old_perms == old(self).perms@,
                old_st == old(self).st@,
                self.slices@ == old_slices,
                self.perms@ == old_perms,
                self.st@ == allocated_st,
                self.bump.wf(self.st@),
                self.st@.inst() == old_st.inst(),
                self.st@.provenance() == old_st.provenance(),
                self.st@.outstanding() == old_st.outstanding().insert(tok.id()),
                !old_st.outstanding().contains(tok.id()),
                tok.inst() == self.st@.inst(),
                tok.alloc() == (Alloc { addr: base, size: (n * size_of::<T>()) as usize }),
                p@.provenance == self.st@.provenance(),
                i <= n,
                n == values@.len(),
                stride == size_of::<T>(),
                base == p.addr(),
                base != 0,
                base as int % align_of::<T>() as int == 0,
                size_of::<T>() as int % align_of::<T>() as int == 0,
                align_of::<T>() > 0,
                base + n * size_of::<T>() <= usize::MAX,
                n * size_of::<T>() <= isize::MAX,
                rest.provenance() == p@.provenance,
                rest.dom() == Set::range(base + i * size_of::<T>(), base + n * size_of::<T>()),
                elems.dom() == Set::range(0int, i as int),
                forall|j: int| 0 <= j < i ==> {
                    &&& #[trigger] elems[j].ptr() == p.with_addr(
                        (base + j * size_of::<T>()) as usize)
                    &&& elems[j].ptr()@.provenance == p@.provenance
                    &&& elems[j].is_init()
                    &&& elems[j].value() == values@[j]
                },
            decreases n - i,
        {
            proof {
                assert((i as int) * (stride as int) <= (n as int) * (stride as int)) by (nonlinear_arith)
                    requires i < n;
                assert(((i as int) + 1) * (stride as int) <= (n as int) * (stride as int)) by (nonlinear_arith)
                    requires i < n;
                assert((stride as int) % (align_of::<T>() as int) == 0);
                vstd::arithmetic::div_mod::lemma_small_mod(0, align_of::<T>());
                vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(stride as int, i as int, align_of::<T>() as int);
                vstd::arithmetic::div_mod::lemma_mod_adds(base as int, i * stride, align_of::<T>() as int);
                assert(stride * i == i * stride) by (nonlinear_arith);
                assert((i * stride) % (align_of::<T>() as int) == 0);
                assert((base + i * stride) % (align_of::<T>() as int) == 0);
                assert(Set::range(base + i * stride, base + (i + 1) * stride)
                    <= rest.dom()) by {
                    assert(base + (i + 1) * stride <= base + n * stride);
                }
            }
            let addr = base + i * stride;
            proof {
                assert(addr + stride == base + (i + 1) * stride) by (nonlinear_arith)
                    requires addr == base + i * stride;
            }
            let tracked (chunk, rest2) = rest.split(Set::range(addr as int, addr + stride));
            proof {
                assert(chunk.is_range(addr as int, size_of::<T>() as int));
            }
            let tracked mut elem = chunk.into_typed::<T>(addr);
            let q = p.with_addr(addr);
            proof {
                broadcast use vstd::raw_ptr::group_raw_ptr_axioms;
                assert(elem.ptr() == q);
            }
            ptr_mut_write(q, Tracked(&mut elem), *vstd::slice::slice_index_get(values, i));
            proof {
                elems.tracked_insert(i as int, elem);
                rest = rest2;
                assert(base + (i + 1) * stride == base + i * stride + stride) by (nonlinear_arith);
                assert(rest.dom() =~= Set::range(base + (i + 1) * stride, base + n * stride));
            }
            i += 1;
        }
        let tracked perm = SlicePerm { elems, base: p, len: n as nat };
        proof {
            assert(elems.dom() == Set::range(0int, n as int));
            assert forall|j: int| 0 <= j < n implies {
                &&& #[trigger] perm.elems[j].ptr() == perm.elem_ptr(j)
                &&& perm.elems[j].is_init()
                &&& perm.elems[j].ptr()@.provenance == perm.base@.provenance
            } by {
                assert(elems[j].ptr() == p.with_addr((base + j * size_of::<T>()) as usize));
            }
            assert(perm.wf());
            assert forall|j: int| 0 <= j < n implies perm.values()[j] == values@[j] by {
                assert(elems[j].ptr() == p.with_addr((base + j * size_of::<T>()) as usize));
                assert(elems[j].is_init());
                assert(elems[j].value() == values@[j]);
            }
            assert(perm.values() =~= values@);
        }
        let index = self.slices.len();
        proof { assert(index == old_slices.len()); }
        self.slices.push((p, n));
        proof {
            let ghost fresh = tok.id();
            self.perms.borrow_mut().tracked_insert(index as int, (perm, tok));
            assert forall|j: int| 0 <= j < index implies old_st.outstanding().contains(old_perms[j].1.id()) by {
                assert(old_perms[j].0.wf());
            }
            assert forall|a: int, b: int| 0 <= a < self.slices@.len() && 0 <= b < self.slices@.len()
                && a != b implies #[trigger] self.perms@[a].1.id() != #[trigger] self.perms@[b].1.id() by {
                if a == index { assert(!old_st.outstanding().contains(fresh)); }
                if b == index { assert(!old_st.outstanding().contains(fresh)); }
            }
            assert forall|k: Id| #[trigger] self.st@.outstanding().contains(k) <==>
                exists|j: int| 0 <= j < self.slices@.len() && #[trigger] self.perms@[j].1.id() == k by {
                if k == fresh {
                    assert(self.perms@[index as int].1.id() == k);
                } else if self.st@.outstanding().contains(k) {
                    let j = choose|j: int| 0 <= j < old_slices.len() && old_perms[j].1.id() == k;
                    assert(self.perms@[j].1.id() == k);
                }
            }
            assert(self.perms@.dom() =~= Set::range(0int, self.slices@.len() as int));
            assert forall|j: int| 0 <= j < self.slices@.len() implies {
                &&& #[trigger] self.perms@[j].0.wf()
                &&& self.perms@[j].0.ptr() == self.slices@[j].0
                &&& self.perms@[j].0.len() == self.slices@[j].1
                &&& self.perms@[j].0.ptr()@.provenance == self.st@.provenance()
                &&& self.perms@[j].1.inst() == self.st@.inst()
                &&& self.st@.outstanding().contains(self.perms@[j].1.id())
                &&& self.perms@[j].1.alloc() == (Alloc {
                    addr: self.slices@[j].0.addr(),
                    size: (self.slices@[j].1 * size_of::<T>()) as usize,
                })
            } by {
                if j != index {
                    assert(old_perms[j].0.wf());
                    assert(self.perms@[j] == old_perms[j]);
                }
            }
            assert(self.wf());
            assert(self.view() =~= old(self).view().push(values@));
        }
        Ok(index)
    }

    fn free(self)
        requires self.wf(),
    {
        let SliceInner { bump, slices, st: Tracked(st), perms: Tracked(perms) } = self;
        proof {
            assert forall|i: int| 0 <= i < slices@.len() implies {
                &&& perms[i].0.wf()
                &&& perms[i].0.ptr()@.provenance == st.provenance()
                &&& perms[i].1.inst() == st.inst()
                &&& perms[i].1.alloc().addr == perms[i].0.ptr().addr()
                &&& perms[i].1.alloc().size == perms[i].0.len() * size_of::<T>()
            } by {
                assert(perms[i].0.wf());
            }
        }
        let tracked back = collect_slices(perms, slices@.len(), st.inst(), st.provenance());
        proof {
            assert(back.dom() =~= st.outstanding());
            assert(back_wf(st, back));
        }
        bump.free(Tracked(st), Tracked(back));
    }
}

proof fn collect_slices<T>(tracked perms: Map<int, (SlicePerm<T>, BumpTok)>, n: nat,
    inst: vstd::resource::Loc, provenance: vstd::raw_ptr::Provenance)
    -> (tracked back: Map<Id, (PointsToRaw, BumpTok)>)
    requires
        perms.dom() == Set::range(0int, n as int),
        forall|i: int| 0 <= i < n ==> {
            &&& #[trigger] perms[i].0.wf()
            &&& perms[i].0.ptr()@.provenance == provenance
            &&& perms[i].1.inst() == inst
            &&& perms[i].1.alloc().addr == perms[i].0.ptr().addr()
            &&& perms[i].1.alloc().size == perms[i].0.len() * size_of::<T>()
        },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j
            ==> #[trigger] perms[i].1.id() != #[trigger] perms[j].1.id(),
    ensures
        forall|k: Id| back.dom().contains(k) <==>
            exists|i: int| 0 <= i < n && #[trigger] perms[i].1.id() == k,
        forall|k: Id| #[trigger] back.dom().contains(k) ==> {
            &&& back[k].1.id() == k
            &&& back[k].1.inst() == inst
            &&& back[k].0.provenance() == provenance
            &&& back[k].0.is_range(back[k].1.alloc().addr as int, back[k].1.alloc().size as int)
        },
    decreases n,
{
    if n == 0 {
        Map::tracked_empty()
    } else {
        let tracked mut perms = perms;
        let ghost original = perms;
        let ghost i = (n - 1) as int;
        let tracked (perm, tok) = perms.tracked_remove(i);
        assert(original[i].0.wf());
        assert(perms.dom() =~= Set::range(0int, n - 1));
        let tracked mut back = collect_slices(perms, (n - 1) as nat, inst, provenance);
        let ghost previous_back = back;
        let tracked raw = perm.into_raw();
        let ghost id = tok.id();
        assert(!back.dom().contains(id)) by {
            if back.dom().contains(id) {
                let j = choose|j: int| 0 <= j < n - 1 && perms[j].1.id() == id;
                assert(original[j].1.id() != original[i].1.id());
            }
        }
        back.tracked_insert(id, (raw, tok));
        assert forall|k: Id| back.dom().contains(k) <==>
            exists|j: int| 0 <= j < n && original[j].1.id() == k by {
            if k == id {
                assert(original[i].1.id() == k);
            } else if back.dom().contains(k) {
                let j = choose|j: int| 0 <= j < n - 1 && perms[j].1.id() == k;
                assert(original[j].1.id() == k);
            } else if exists|j: int| 0 <= j < n && original[j].1.id() == k {
                let j = choose|j: int| 0 <= j < n && original[j].1.id() == k;
                assert(j != i);
                assert(perms[j].1.id() == k);
                assert(back.dom().contains(k));
            }
        }
        assert forall|k: Id| #[trigger] back.dom().contains(k) implies {
            &&& back[k].1.id() == k
            &&& back[k].1.inst() == inst
            &&& back[k].0.provenance() == provenance
            &&& back[k].0.is_range(back[k].1.alloc().addr as int, back[k].1.alloc().size as int)
        } by {
            if k == id {
                assert(original[i].0.wf());
            } else {
                assert(previous_back.dom().contains(k));
                assert(back[k] == previous_back[k]);
            }
        }
        back
    }
}

impl<T: Copy> View for SliceArena<T> {
    type V = Seq<Seq<T>>;
    closed spec fn view(&self) -> Seq<Seq<T>> {
        match self.inner { Some(inner) => inner.view(), None => Seq::empty() }
    }
}

impl<T: Copy> SliceArena<T> {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        self.inner is Some ==> self.inner->0.wf()
    }

    /// Chunk size in bytes (0 without a chunk).
    pub closed spec fn capacity(&self) -> int {
        match self.inner { Some(inner) => inner.capacity(), None => 0 }
    }

    /// Bytes below the cursor (0 without a chunk).
    pub closed spec fn remaining(&self) -> int {
        match self.inner { Some(inner) => inner.remaining(), None => 0 }
    }

    /// The cursor is a multiple of `align_of::<T>()`, so pushes never pad.
    pub closed spec fn aligned(&self) -> bool {
        self.inner matches Some(inner) ==> inner.aligned()
    }

    /// Creates an empty arena backed by one fixed-size chunk.
    pub fn with_capacity(capacity: usize) -> (r: Result<Self, AllocErr>)
        ensures
            r matches Ok(a) ==> a@ == Seq::<Seq<T>>::empty()
                && a.capacity() == capacity && a.remaining() == capacity
                && (align_of::<T>() <= CHUNK_ALIGN
                    && capacity as int % align_of::<T>() as int == 0 ==> a.aligned()),
            capacity == 0 || capacity > MAX_CAP ==> r == Err(AllocErr::Capacity),
    {
        let (bump, Tracked(st)) = Bump::try_with_capacity(capacity)?;
        let inner = SliceInner {
            bump,
            slices: Vec::new(),
            st: Tracked(st),
            perms: Tracked(Map::tracked_empty()),
        };
        proof {
            assert(inner.perms@.dom() =~= Set::range(0int, 0int));
            assert(inner.wf());
            lemma_cursor_aligned::<T>(bump, st, capacity);
        }
        Ok(Self { inner: Some(inner) })
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        proof { use_type_invariant(&*self); }
        match &self.inner { Some(inner) => inner.slices.len(), None => 0 }
    }

    pub fn get(&self, index: usize) -> (r: Option<&[T]>)
        ensures
            r matches Some(s) ==> index < self@.len() && s@ == self@[index as int],
            r is None ==> index >= self@.len(),
    {
        proof { use_type_invariant(&*self); }
        match &self.inner { Some(inner) => inner.get(index), None => None }
    }

    /// Appends a copied slice, leaving the sequence unchanged on allocation failure.
    ///
    /// From an aligned cursor a push consumes exactly `len * size_of::<T>()` bytes and
    /// fails with `Exhausted` only when that many bytes are not left.
    pub fn try_push(&mut self, values: &[T]) -> (r: Result<usize, AllocErr>)
        ensures
            final(self).capacity() == old(self).capacity(),
            r matches Ok(i) ==> i == old(self)@.len() && final(self)@ == old(self)@.push(values@),
            r is Err ==> final(self)@ == old(self)@
                && final(self).remaining() == old(self).remaining()
                && final(self).aligned() == old(self).aligned(),
            old(self).aligned() && r is Ok ==> final(self).aligned()
                && final(self).remaining() == old(self).remaining() - values@.len() * size_of::<T>(),
            old(self).aligned() && r == Err(AllocErr::Exhausted)
                ==> values@.len() * size_of::<T>() > old(self).remaining(),
    {
        proof { use_type_invariant(&*self); }
        let inner = self.inner.take();
        match inner {
            Some(mut inner) => {
                let result = inner.try_push(values);
                self.inner = Some(inner);
                result
            },
            None => Err(AllocErr::Global),
        }
    }

    pub fn free(self) {
        proof { use_type_invariant(&self); }
        if let Some(inner) = self.inner { inner.free(); }
    }
}


}
