#![cfg_attr(not(verus_only), allow(dead_code, unused_braces))]
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(allocator_api))]
//! A verified, fixed single-chunk bump allocator.
//!
//! Allocations never grow the arena. Call `Bump::free` with every outstanding
//! allocation permission to release its chunk. There is no `Drop` implementation:
//! dropping an arena without explicitly freeing it leaks the chunk.
//!
//! Memory-safety guarantees require verified callers to preserve tracked permissions;
//! ordinary Rust raw-pointer dereferences still require `unsafe`. Trusted boundaries
//! are `Layout::size`/`Layout::align`, fallible chunk allocation, and slice formation.
//! SliceArena's native Send/Sync implementations additionally rely on exclusive
//! chunk ownership, immutable shared access, and the corresponding T: Send/Sync bound.

extern crate alloc;

use core::alloc::Layout;
#[cfg(verus_only)]
use vstd::arithmetic::power::pow;
#[cfg(verus_only)]
use vstd::arithmetic::power2::{is_pow2, pow2};
use vstd::cell::pcell::{PCell, PointsTo as CellPointsTo};
use vstd::prelude::*;
use vstd::raw_ptr::{
    deallocate, expose_provenance, with_exposed_provenance, Dealloc, IsExposed, PointsToRaw,
};
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
#[cfg(verus_only)]
use vstd::resource::Loc;

pub mod arena;
pub mod layout;
pub use arena::{SliceArena, SlicePerm, TypedArena};

verus! {
pub const CHUNK_ALIGN: usize = 16;
pub const MAX_CAP: usize = (isize::MAX as usize) - 15;

/// Why an allocation request was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocErr {
    /// The request does not fit in this chunk (including a byte count that overflows `usize`).
    Exhausted,
    /// The global allocator failed (chunk creation or the containers' pointer table).
    Global,
    /// `cap == 0 || cap > MAX_CAP`.
    Capacity,
}

/// Trusted: fallible global allocation. A null result becomes `None`; no abort.
#[verifier::external_body]
fn try_allocate(size: usize, align: usize)
    -> (r: Option<(*mut u8, Tracked<PointsToRaw>, Tracked<Dealloc>)>)
    requires vstd::layout::valid_layout(size, align), size != 0,
    ensures r matches Some(pt) ==> {
        &&& pt.1@.is_range(pt.0.addr() as int, size as int)
        &&& pt.0.addr() != 0
        &&& pt.0.addr() + size <= usize::MAX + 1
        &&& pt.2@@ == (vstd::raw_ptr::DeallocData { addr: pt.0.addr(), size: size as nat, align: align as nat, provenance: pt.1@.provenance() })
        &&& pt.0.addr() as int % align as int == 0
        &&& pt.0@.provenance == pt.1@.provenance()
    },
    opens_invariants none
{
    // SAFETY: valid_layout and size != 0 are preconditions.
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    // SAFETY: layout is valid and nonzero; null is handled below.
    let p = unsafe { alloc::alloc::alloc(layout) };
    if p.is_null() { None } else { Some((p, Tracked::assume_new(), Tracked::assume_new())) }
}

/// A mathematical allocation index; its nat identity is part of the ghost API.
pub type Id = nat;

/// Address and byte length recorded for one allocation.
pub ghost struct Alloc { pub addr: usize, pub size: usize }

pub tracked struct BumpTok { tracked pt: GhostPointsTo<nat, Alloc> }

impl BumpTok {
    pub closed spec fn inst(self) -> Loc { self.pt.id() }
    pub closed spec fn id(self) -> Id { self.pt.key() }
    pub closed spec fn alloc(self) -> Alloc { self.pt.value() }

    /// Relates a live token to the arena's ghost record.
    pub proof fn agree(tracked &self, tracked st: &BumpState)
        requires self.inst() == st.inst(),
        ensures st.outstanding().contains(self.id()), st.addr_of(self.id()) == self.alloc().addr,
    { self.pt.agree(&st.auth); }
}

spec fn range_of(a: Alloc) -> Set<int> {
    Set::range(a.addr as int, a.addr + a.size)
}

spec fn used_upto(m: Map<nat, Alloc>, i: nat) -> Set<int>
    decreases i,
{
    if i == 0 {
        Set::empty()
    } else {
        let u = used_upto(m, (i - 1) as nat);
        let k = (i - 1) as nat;
        if m.dom().contains(k) { u + range_of(m[k]) } else { u }
    }
}

pub tracked struct BumpState {
    tracked ptr_perm: CellPointsTo<usize>,
    tracked free: PointsToRaw,
    tracked dealloc: Dealloc,
    tracked exposed: IsExposed,
    tracked auth: GhostMapAuth<nat, Alloc>,
    ghost next_id: nat,
}

impl BumpState {
    pub closed spec fn inst(self) -> Loc { self.auth.id() }
    pub closed spec fn outstanding(self) -> Set<Id> { self.auth.dom() }
    pub closed spec fn addr_of(self, k: Id) -> usize { self.auth@[k].addr }
    pub closed spec fn provenance(self) -> vstd::raw_ptr::Provenance { self.free.provenance() }
    spec fn used(self) -> Set<int> { used_upto(self.auth@, self.next_id) }
}

pub struct Bump { ptr: PCell<usize>, start: usize, end: usize }

impl Bump {
    pub closed spec fn start(self) -> usize { self.start }
    pub closed spec fn end(self) -> usize { self.end }
    pub closed spec fn cursor(self, st: BumpState) -> usize { *st.ptr_perm.value() }
    pub open spec fn capacity(self) -> int { self.end() - self.start() }
    pub open spec fn remaining(self, st: BumpState) -> int { self.cursor(st) - self.start() }
    pub open spec fn in_arena(self, addr: usize, size: usize) -> bool {
        self.start() <= addr && addr + size <= self.end()
    }
    pub closed spec fn wf(self, st: BumpState) -> bool {
        &&& st.ptr_perm.id() == self.ptr.id()
        &&& self.start != 0
        &&& self.start as int % CHUNK_ALIGN as int == 0
        &&& self.end - self.start <= MAX_CAP
        &&& self.start <= *st.ptr_perm.value() <= self.end
        &&& st.exposed.provenance() == st.free.provenance()
        &&& st.dealloc.provenance() == st.free.provenance()
        &&& st.dealloc.addr() == self.start && st.dealloc.size() == self.end - self.start
            && st.dealloc.align() == CHUNK_ALIGN
        &&& st.free.dom().disjoint(st.used())
        &&& st.free.dom() + st.used() == Set::range(self.start as int, self.end as int)
        &&& Set::range(self.start as int, st.ptr_perm.value() as int) <= st.free.dom()
        &&& forall|k: nat| st.auth.dom().contains(k) ==> k < st.next_id
        &&& forall|k: nat| #[trigger] st.auth.dom().contains(k)
            ==> range_of(st.auth@[k]).disjoint(used_upto(st.auth@, k))
    }

    /// Bounds every well-formed arena satisfies.
    pub proof fn lemma_wf(self, st: BumpState)
        requires self.wf(st),
        ensures
            0 <= self.remaining(st) <= self.capacity() <= MAX_CAP,
            self.start() != 0,
            self.start() as int % CHUNK_ALIGN as int == 0,
    {
    }

    /// Creates one fixed-size chunk.
    ///
    /// # Errors
    /// `Capacity` for zero/oversized capacity; `Global` when the global allocator fails
    /// or the chunk's end address is unrepresentable.
    pub fn try_with_capacity(cap: usize) -> (r: Result<(Bump, Tracked<BumpState>), AllocErr>)
        ensures
            r matches Ok((b, st)) ==> b.wf(st@) && st@.outstanding().is_empty()
                && b.capacity() == cap && b.remaining(st@) == cap,
            cap == 0 || cap > MAX_CAP ==> r == Err(AllocErr::Capacity),
    {
        if cap == 0 || cap > MAX_CAP { return Err(AllocErr::Capacity); }
        proof {
            reveal(is_pow2);
            assert(is_pow2(16)) by (compute);
        }
        let Some((base, Tracked(free), Tracked(dealloc))) = try_allocate(cap, CHUNK_ALIGN)
            else { return Err(AllocErr::Global); };
        let start = base.addr();
        if start > usize::MAX - cap {
            proof {
                vstd::arithmetic::div_mod::lemma_mod_adds(start as int, cap as int, 16);
                assert((usize::MAX as int + 1) % 16 == 0);
            }
            deallocate(base, cap, CHUNK_ALIGN, Tracked(free), Tracked(dealloc));
            return Err(AllocErr::Global);
        }
        let end = start + cap;
        let Tracked(exposed) = expose_provenance(base);
        let (ptr, Tracked(ptr_perm)) = PCell::new(end);
        let tracked (auth, _sub) = GhostMapAuth::<nat, Alloc>::new(Map::empty());
        let tracked st = BumpState { ptr_perm, free, dealloc, exposed, auth, next_id: 0 };
        proof {
            assert(st.used() =~= Set::empty());
            assert(st.free.dom() + st.used() =~= Set::range(start as int, end as int));
        }
        Ok((Bump { ptr, start, end }, Tracked(st)))
    }

    /// Allocates `size` bytes at power-of-two `align` downward from this arena, retaining
    /// padding for later reclamation. Returns the pointer, its uninitialized-memory
    /// permission, and its return token.
    ///
    /// # Errors
    /// Returns `Exhausted` without changing the arena if size or alignment exhausts it.
    #[inline(always)]
    pub fn try_alloc(&self, size: usize, align: usize, Tracked(st): Tracked<&mut BumpState>)
        -> (r: Result<(*mut u8, Tracked<PointsToRaw>, Tracked<BumpTok>), AllocErr>)
        requires self.wf(*old(st)), exists|n: nat| n < usize::BITS && align == pow2(n),
        ensures
            self.wf(*final(st)),
            final(st).inst() == old(st).inst(),
            final(st).provenance() == old(st).provenance(),
            self.remaining(*final(st)) <= self.remaining(*old(st)),
            r matches Ok((p, perm, tok)) ==> {
                &&& p.addr() != 0
                &&& perm@.is_range(p.addr() as int, size as int)
                &&& perm@.provenance() == p@.provenance
                &&& perm@.provenance() == final(st).provenance()
                &&& p.addr() as int % align as int == 0
                &&& self.in_arena(p.addr(), size)
                &&& p.addr() == align_down(self.cursor(*old(st)) - size, align as int)
                &&& self.cursor(*final(st)) == p.addr()
                &&& tok@.inst() == final(st).inst()
                &&& tok@.alloc() == Alloc { addr: p.addr(), size }
                &&& !old(st).outstanding().contains(tok@.id())
                &&& final(st).outstanding() == old(st).outstanding().insert(tok@.id())
            },
            r is Err ==> *final(st) == *old(st) && r == Err(AllocErr::Exhausted),
            r is Ok <==> size <= self.remaining(*old(st))
                && self.start() <= align_down(self.cursor(*old(st)) - size, align as int),
            size + align - 1 <= self.remaining(*old(st)) ==> r is Ok,
    {
        let ghost n = choose|n: nat| n < usize::BITS && align == pow2(n);
        proof { vstd::bits::lemma_usize_pow2_no_overflow(n); }
        let ptr = self.ptr.read(Tracked(&st.ptr_perm));
        if size > ptr - self.start { return Err(AllocErr::Exhausted); }
        proof {
            lemma_align_down((ptr - size) as usize, align, n);
        }
        let new = (ptr - size) & !(align - 1);
        if new < self.start { return Err(AllocErr::Exhausted); }
        let ghost m = st.auth@;
        let ghost id = st.next_id;
        proof { assert(!st.auth.dom().contains(id)); }
        self.ptr.write(Tracked(&mut st.ptr_perm), new);
        let p = with_exposed_provenance::<u8>(new, Tracked(st.exposed));
        let tracked perm;
        let tracked pt;
        proof {
            let ghost a = Alloc { addr: new, size };
            let ghost rng = range_of(a);
            assert(rng <= Set::range(self.start as int, ptr as int));
            assert(rng <= st.free.dom());
            let ghost old_used = st.used();
            let tracked mut f = PointsToRaw::empty(st.free.provenance());
            vstd::modes::tracked_swap(&mut f, &mut st.free);
            let tracked (allocated, rest) = f.split(rng);
            perm = allocated;
            st.free = rest;
            pt = st.auth.insert(id, a);
            st.next_id = id + 1;
            lemma_used_upto_frame(m, id, a, id);
            assert forall|k: nat| #[trigger] st.auth.dom().contains(k)
                implies range_of(st.auth@[k]).disjoint(used_upto(st.auth@, k)) by {
                lemma_used_upto_frame(m, id, a, k);
                if k == id {
                    assert forall|x: int| #[trigger] rng.contains(x)
                        implies !used_upto(m, id).contains(x) by { }
                }
            }
            assert(st.used() == old_used + rng);
            assert(st.free.dom().disjoint(st.used()));
            assert(st.free.dom() + st.used() =~= Set::range(self.start as int, self.end as int));
            assert(Set::range(self.start as int, new as int) <= st.free.dom());
        }
        Ok((p, Tracked(perm), Tracked(BumpTok { pt })))
    }

    /// `try_alloc` with `layout.size()` and `layout.align()`.
    ///
    /// # Errors
    /// Returns `Exhausted` without changing the arena if size or alignment exhausts it.
    #[inline(always)]
    pub fn try_alloc_layout(&self, layout: Layout, Tracked(st): Tracked<&mut BumpState>)
        -> (r: Result<(*mut u8, Tracked<PointsToRaw>, Tracked<BumpTok>), AllocErr>)
        requires self.wf(*old(st)),
        ensures
            self.wf(*final(st)),
            final(st).inst() == old(st).inst(),
            final(st).provenance() == old(st).provenance(),
            self.remaining(*final(st)) <= self.remaining(*old(st)),
            r matches Ok((p, perm, tok)) ==> {
                &&& p.addr() != 0
                &&& perm@.is_range(p.addr() as int, layout.size() as int)
                &&& perm@.provenance() == p@.provenance
                &&& perm@.provenance() == final(st).provenance()
                &&& p.addr() as int % layout.align() as int == 0
                &&& self.in_arena(p.addr(), layout.size())
                &&& p.addr() == align_down(self.cursor(*old(st)) - layout.size(), layout.align() as int)
                &&& self.cursor(*final(st)) == p.addr()
                &&& tok@.inst() == final(st).inst()
                &&& tok@.alloc() == Alloc { addr: p.addr(), size: layout.size() }
                &&& !old(st).outstanding().contains(tok@.id())
                &&& final(st).outstanding() == old(st).outstanding().insert(tok@.id())
            },
            r is Err ==> *final(st) == *old(st) && r == Err(AllocErr::Exhausted),
            r is Ok <==> layout.size() <= self.remaining(*old(st))
                && self.start() <= align_down(self.cursor(*old(st)) - layout.size(), layout.align() as int),
            layout.size() + layout.align() - 1 <= self.remaining(*old(st)) ==> r is Ok,
    {
        self.try_alloc(layout.size(), layout.align(), Tracked(st))
    }
}

proof fn lemma_used_upto_frame(m: Map<nat, Alloc>, k: nat, a: Alloc, i: nat)
    requires i <= k,
    ensures
        used_upto(m.insert(k, a), i) == used_upto(m, i),
        used_upto(m.remove(k), i) == used_upto(m, i),
    decreases i,
{
    if i > 0 { lemma_used_upto_frame(m, k, a, (i - 1) as nat); }
}

proof fn lemma_used_upto_submap(m1: Map<nat, Alloc>, m2: Map<nat, Alloc>, i: nat)
    requires m1 <= m2,
    ensures used_upto(m1, i) <= used_upto(m2, i),
    decreases i,
{
    if i > 0 { lemma_used_upto_submap(m1, m2, (i - 1) as nat); }
}

/// Every used byte below i belongs to some recorded allocation with id < i.
proof fn lemma_used_upto_elem(m: Map<nat, Alloc>, i: nat, x: int) -> (k: nat)
    requires used_upto(m, i).contains(x),
    ensures m.dom().contains(k), k < i, range_of(m[k]).contains(x),
    decreases i,
{
    let j = (i - 1) as nat;
    if m.dom().contains(j) && range_of(m[j]).contains(x) {
        j
    } else {
        lemma_used_upto_elem(m, j, x)
    }
}

/// Rounds x down to a multiple of a.
pub open spec fn align_down(x: int, a: int) -> int { x - x % a }

/// Rounds x down to a multiple of a == pow2(n).
#[verifier::spinoff_prover]
proof fn lemma_align_down(x: usize, a: usize, n: nat)
    requires n < usize::BITS, a == pow2(n),
    ensures
        a >= 1,
        (x & !((a - 1) as usize)) as int == x - (x as int % a as int),
        ((x & !((a - 1) as usize)) as int) % (a as int) == 0,
        x - (x & !((a - 1) as usize)) < a,
{
    vstd::bits::lemma_usize_pow2_no_overflow(n);
    vstd::bits::lemma_usize_low_bits_mask_is_mod(x, n);
    let m = (a - 1) as usize;
    assert((x & !m) + (x & m) == x) by (bit_vector);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, a as int);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic((x as int) / (a as int), a as int);
}

/// Every power of two is `pow2(n)` for some exponent.
pub proof fn lemma_pow2_exponent(a: int) -> (n: nat)
    requires is_pow2(a),
    ensures a == pow2(n),
{
    broadcast use vstd::arithmetic::power2::is_pow2_equiv;
    let n = choose|i: nat| pow(2, i) == a;
    vstd::arithmetic::power2::lemma_pow2(n);
    n
}

/// A power of two that fits in `usize` has an exponent below `usize::BITS`.
pub proof fn lemma_pow2_witness(a: usize)
    requires is_pow2(a as int),
    ensures exists|n: nat| n < usize::BITS && a == pow2(n),
{
    let n = lemma_pow2_exponent(a as int);
    if n >= usize::BITS {
        vstd::layout::unsigned_int_max_values();
        if n > usize::BITS {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(usize::BITS as nat, n);
        }
        assert(false);
    }
}

/// A power-of-two alignment at most `CHUNK_ALIGN` divides every `CHUNK_ALIGN`-aligned address.
pub proof fn lemma_chunk_align_divides(x: int, a: int)
    requires is_pow2(a), a <= CHUNK_ALIGN, x % CHUNK_ALIGN as int == 0,
    ensures x % a == 0,
{
    let n = lemma_pow2_exponent(a);
    vstd::arithmetic::power2::lemma2_to64();
    if n > 4 {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, n);
    }
    let k = (4 - n) as nat;
    vstd::arithmetic::power2::lemma_pow2_adds(n, k);
    vstd::arithmetic::power2::lemma_pow2_pos(k);
    let b = pow2(k) as int;
    assert(a * b == CHUNK_ALIGN);
    vstd::arithmetic::div_mod::lemma_mod_mod(x, a, b);
    assert((x % (a * b)) % a == x % a);
    assert(x % (a * b) == 0);
    vstd::arithmetic::div_mod::lemma_small_mod(0, a as nat);
}

/// Rounding `c - s` down to `a` is the identity when both terms are multiples of `a`.
pub proof fn lemma_align_down_exact(c: int, s: int, a: int)
    requires a > 0, c % a == 0, s % a == 0,
    ensures align_down(c - s, a) == c - s,
{
    vstd::arithmetic::div_mod::lemma_small_mod(0, a as nat);
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(c, s, a);
}

/// Caller-side well-formedness of permissions returned for reclamation.
pub open spec fn back_wf(st: BumpState, back: Map<Id, (PointsToRaw, BumpTok)>) -> bool {
    &&& back.dom() <= st.outstanding()
    &&& forall|k: Id| #[trigger] back.dom().contains(k) ==> {
        &&& back[k].1.inst() == st.inst()
        &&& back[k].1.id() == k
        &&& back[k].0.is_range(back[k].1.alloc().addr as int, back[k].1.alloc().size as int)
        &&& back[k].0.provenance() == st.provenance()
    }
}

/// Consumes every returned token below i and joins its permission into acc.
proof fn collect(
    tracked auth: &mut GhostMapAuth<nat, Alloc>,
    tracked back: &mut Map<Id, (PointsToRaw, BumpTok)>,
    tracked acc: PointsToRaw,
    i: nat,
) -> (tracked out: PointsToRaw)
    requires
        old(back).dom() <= old(auth).dom(),
        forall|k: Id| old(back).dom().contains(k) ==> k < i,
        forall|k: Id| #[trigger] old(back).dom().contains(k) ==>
            old(back)[k].1.inst() == old(auth).id() && old(back)[k].1.id() == k
            && old(back)[k].0.is_range(old(back)[k].1.alloc().addr as int, old(back)[k].1.alloc().size as int)
            && old(back)[k].0.provenance() == acc.provenance(),
        acc.dom().disjoint(used_upto(old(auth)@, i)),
        forall|k: nat| #[trigger] old(auth).dom().contains(k)
            ==> range_of(old(auth)@[k]).disjoint(used_upto(old(auth)@, k)),
    ensures
        final(auth).id() == old(auth).id(),
        final(auth)@ == old(auth)@.remove_keys(old(back).dom()),
        out.provenance() == acc.provenance(),
        out.dom() + used_upto(final(auth)@, i) == acc.dom() + used_upto(old(auth)@, i),
        out.dom().disjoint(used_upto(final(auth)@, i)),
    decreases i,
{
    let m = auth@;
    let s = back.dom();
    if i == 0 {
        assert(s =~= Set::empty());
        assert(m.remove_keys(Set::empty()) =~= m);
        assert(acc.dom() + Set::<int>::empty() =~= acc.dom());
        acc
    } else {
        let k = (i - 1) as nat;
        if back.dom().contains(k) {
            let tracked (perm, tok) = back.tracked_remove(k);
            tok.pt.agree(auth);
            auth.delete_points_to(tok.pt);
            let m1 = auth@;
            let rest = back.dom();
            lemma_used_upto_frame(m, k, m[k], k);
            assert forall|j: nat| #[trigger] auth.dom().contains(j)
                implies range_of(auth@[j]).disjoint(used_upto(auth@, j)) by {
                lemma_used_upto_submap(m1, m, j);
            }
            let tracked acc2 = acc.join(perm);
            assert(acc2.dom().disjoint(used_upto(m1, k)));
            let tracked out = collect(auth, back, acc2, k);
            assert(m1.remove_keys(rest) =~= m.remove_keys(s));
            assert(used_upto(auth@, i) =~= used_upto(auth@, k));
            assert(out.dom() + used_upto(auth@, i) =~= acc.dom() + used_upto(m, i));
            out
        } else {
            let tracked out = collect(auth, back, acc, k);
            reveal(used_upto);
            assert(out.dom() + used_upto(auth@, k) == acc.dom() + used_upto(m, k));
            assert(out.dom() <= acc.dom() + used_upto(m, k));
            assert(auth.dom().contains(k) == m.dom().contains(k));
            if m.dom().contains(k) {
                assert(auth@[k] == m[k]);
                assert(out.dom().disjoint(range_of(m[k])));
                assert(used_upto(auth@, i) == used_upto(auth@, k) + range_of(m[k]));
                assert(used_upto(m, i) == used_upto(m, k) + range_of(m[k]));
            } else {
                assert(used_upto(auth@, i) == used_upto(auth@, k));
                assert(used_upto(m, i) == used_upto(m, k));
            }
            vstd::assert_sets_equal!(out.dom() + used_upto(auth@, i) == acc.dom() + used_upto(m, i), x => {
                assert((out.dom() + used_upto(auth@, k)).contains(x)
                    == (acc.dom() + used_upto(m, k)).contains(x));
                if m.dom().contains(k) {
                    assert(used_upto(auth@, i).contains(x)
                        == (used_upto(auth@, k).contains(x) || range_of(m[k]).contains(x)));
                    assert(used_upto(m, i).contains(x)
                        == (used_upto(m, k).contains(x) || range_of(m[k]).contains(x)));
                }
            });
            assert(out.dom().disjoint(used_upto(auth@, i)));
            out
        }
    }
}

proof fn reclaim(
    tracked st: &mut BumpState,
    tracked back: Map<Id, (PointsToRaw, BumpTok)>,
    b: Bump,
)
    requires b.wf(*old(st)), back_wf(*old(st), back),
    ensures
        final(st).ptr_perm == old(st).ptr_perm,
        final(st).dealloc == old(st).dealloc,
        final(st).exposed == old(st).exposed,
        final(st).inst() == old(st).inst(),
        final(st).provenance() == old(st).provenance(),
        final(st).next_id == old(st).next_id,
        final(st).auth@ == old(st).auth@.remove_keys(back.dom()),
        final(st).free.dom().disjoint(final(st).used()),
        final(st).free.dom() + final(st).used() == Set::range(b.start as int, b.end as int),
        forall|k: nat| #[trigger] final(st).auth.dom().contains(k)
            ==> range_of(final(st).auth@[k]).disjoint(used_upto(final(st).auth@, k)),
{
    let m = st.auth@;
    let tracked mut free = PointsToRaw::empty(st.free.provenance());
    vstd::modes::tracked_swap(&mut free, &mut st.free);
    let tracked mut back = back;
    st.free = collect(&mut st.auth, &mut back, free, st.next_id);
    assert forall|k: nat| #[trigger] st.auth.dom().contains(k)
        implies range_of(st.auth@[k]).disjoint(used_upto(st.auth@, k)) by {
        lemma_used_upto_submap(st.auth@, m, k);
    }
}

impl Bump {
    /// Returns the allocations in `back` and rewinds the cursor to `mark`.
    /// Allocations not returned must lie at or above `mark`; they stay valid.
    pub fn reset_to(
        &self,
        mark: usize,
        Tracked(st): Tracked<&mut BumpState>,
        Tracked(back): Tracked<Map<Id, (PointsToRaw, BumpTok)>>,
    )
        requires
            self.wf(*old(st)),
            back_wf(*old(st), back),
            self.in_arena(mark, 0),
            forall|k: Id| #[trigger] old(st).outstanding().contains(k) && !back.dom().contains(k)
                ==> mark <= old(st).addr_of(k),
        ensures
            self.wf(*final(st)),
            final(st).inst() == old(st).inst(),
            final(st).provenance() == old(st).provenance(),
            final(st).outstanding() == old(st).outstanding() - back.dom(),
            self.cursor(*final(st)) == mark,
    {
        let ghost st0 = *st;
        proof {
            reveal(Bump::wf);
            reveal(BumpState::used);
            reveal(BumpState::outstanding);
            reveal(BumpState::inst);
            reveal(BumpState::provenance);
            reveal(BumpState::addr_of);
            reveal(range_of);
            reclaim(st, back, *self);
        }
        self.ptr.write(Tracked(&mut st.ptr_perm), mark);
        proof {
            assert(st.free.dom() + st.used() == Set::range(self.start as int, self.end as int));
            assert(self.start <= mark <= self.end);
            assert forall|x: int| Set::range(self.start as int, mark as int).contains(x)
                implies st.free.dom().contains(x) by {
                if !st.free.dom().contains(x) {
                    assert(Set::range(self.start as int, self.end as int).contains(x));
                    assert(st.used().contains(x));
                    let k = lemma_used_upto_elem(st.auth@, st.next_id, x);
                    assert(st.auth@[k] == st0.auth@[k]);
                }
            }
            assert(st.outstanding() =~= st0.outstanding() - back.dom());
            assert(st.free.dom() + st.used() =~= Set::range(self.start as int, self.end as int));
        }
    }

    /// Returns all allocations to this arena and restores its full capacity.
    pub fn reset(
        &mut self,
        Tracked(st): Tracked<&mut BumpState>,
        Tracked(back): Tracked<Map<Id, (PointsToRaw, BumpTok)>>,
    )
        requires
            old(self).wf(*old(st)), back_wf(*old(st), back),
            back.dom() == old(st).outstanding(),
        ensures
            *final(self) == *old(self),
            final(self).wf(*final(st)),
            final(st).inst() == old(st).inst(),
            final(st).provenance() == old(st).provenance(),
            final(st).outstanding().is_empty(),
            final(self).remaining(*final(st)) == final(self).capacity(),
    {
        self.reset_to(self.end, Tracked(st), Tracked(back));
        proof { assert(st.outstanding() =~= Set::<Id>::empty()); }
    }

    /// Consumes the arena and returns its chunk to the global allocator.
    ///
    /// Every outstanding allocation permission and token must be returned.
    /// There is no `Drop` implementation because it cannot receive tracked state:
    /// dropping an arena without explicitly calling `free` leaks its chunk.
    pub fn free(
        self,
        Tracked(st): Tracked<BumpState>,
        Tracked(back): Tracked<Map<Id, (PointsToRaw, BumpTok)>>,
    )
        requires self.wf(st), back_wf(st, back), back.dom() == st.outstanding(),
    {
        let tracked mut st = st;
        proof {
            reclaim(&mut st, back, self);
            assert forall|x: int| !st.used().contains(x) by {
                if st.used().contains(x) {
                    let k = lemma_used_upto_elem(st.auth@, st.next_id, x);
                }
            }
            assert(st.free.dom() =~= Set::range(self.start as int, self.end as int));
        }
        let base: *mut u8 = with_exposed_provenance(self.start, Tracked(st.exposed));
        let tracked BumpState { free, dealloc, .. } = st;
        deallocate(base, self.end - self.start, CHUNK_ALIGN, Tracked(free), Tracked(dealloc));
    }
}

/// Preserves a u64 across a partial rewind and proves partial/full address reuse.
pub fn smoke() -> (r: Result<u64, AllocErr>)
    ensures r matches Ok(v) ==> v == 42,
{
    let (bump, Tracked(mut st)) = Bump::try_with_capacity(4096)?;
    let mut bump = bump;
    vstd::layout::layout_for_type_is_valid::<u64>();
    let size = core::mem::size_of::<u64>();
    let align = core::mem::align_of::<u64>();
    proof { lemma_pow2_witness(align); }
    let (a, Tracked(pa), Tracked(ta)) = bump.try_alloc(size, align, Tracked(&mut st))?;
    let (b, Tracked(pb), Tracked(tb)) = bump.try_alloc(size, align, Tracked(&mut st))?;
    let a64 = a as *mut u64;
    let tracked mut pta = pa.into_typed::<u64>(a.addr());
    vstd::raw_ptr::ptr_mut_write(a64, Tracked(&mut pta), 42u64);
    let tracked mut back = Map::tracked_empty();
    proof {
        back.tracked_insert(tb.id(), (pb, tb));
        ta.agree(&st);
    }
    bump.reset_to(a.addr(), Tracked(&mut st), Tracked(back));
    let (c, Tracked(pc), Tracked(tc)) = bump.try_alloc(size, align, Tracked(&mut st))?;
    assert!(c.addr() == b.addr());
    let v = vstd::raw_ptr::ptr_mut_read(a64, Tracked(&mut pta));
    let tracked raw = pta.into_raw();
    let tracked mut back = Map::tracked_empty();
    proof {
        back.tracked_insert(ta.id(), (raw, ta));
        back.tracked_insert(tc.id(), (pc, tc));
        assert(back.dom() =~= st.outstanding());
    }
    bump.reset(Tracked(&mut st), Tracked(back));
    let (d, Tracked(pd), Tracked(td)) = bump.try_alloc(size, align, Tracked(&mut st))?;
    assert!(d.addr() == a.addr());
    let tracked mut back_d = Map::tracked_empty();
    proof { back_d.tracked_insert(td.id(), (pd, td)); }
    bump.free(Tracked(st), Tracked(back_d));
    Ok(v)
}

}
