#![cfg_attr(not(verus_only), allow(dead_code, unused_braces))]
//! Verified hash consing with heap (`Arc<T>`) and fixed-capacity arena storage.
//!
//! # Contract
//! A consign's view is a duplicate-free sequence of shallow key views, indexed
//! by dense `usize` uids. Interning returns the existing uid exactly when the
//! key view is already present; otherwise it appends one value. Existing values
//! and owned handles remain valid after insertion and reservation. For handles
//! owned by the same consign, uid equality is equivalent to shallow view equality.
//! Both consigns export this sharing contract via `lemma_uid_eq` and
//! `lemma_no_duplicates` (the duplicate-free view theorem).
//! Handle comparison is by consign id, then uid: handles from different consigns
//! are never equal. Iterate using `len` and `elem`.
//!
//! Arena insertion returns the original input unchanged on exhaustion. Arena
//! handles are inert `(consign id, uid)` pairs: access requires the owning consign
//! and its verified ownership predicate. `free` returns the whole chunk; stored destructors never
//! run. Dropping an arena without `free` leaks its chunk, as in `verus-bumpalo`.
//!
//! # Trust and compatibility
//! This crate has no local trusted specifications or `global` layout axioms;
//! its proofs do not fix the pointer width. On Verus `0.2026.10.04.426d8b0`,
//! `cargo verus verify --fwd-verus-args-to roots -- --no-cheating` passes for
//! this crate.
//!
//! The trusted base includes the Verus verifier, erasure macros, Z3, and rustc;
//! vstd's `Arc::new`, cloning/dereference, `Vec` push/reserve/capacity and length
//! specs (allocation has no failure case), raw-pointer permissions and pointer
//! comparison model (address/metadata, not provenance), layout validity,
//! `core::mem::size_of`/`align_of`, checked arithmetic, `usize` comparisons,
//! wrapping `u64` arithmetic, `core::sync::atomic::AtomicUsize::new`/`fetch_add`
//! (result unspecified), and `Map`/`Seq`/`Set` axioms. `verus-bumpalo`
//! contributes trusted `try_allocate` and `slice_ref` bridges; the slice bridge
//! is compiled but unused here.
//! Native Send/Sync markers rely on exclusive arena ownership, immutable shared
//! access, and T: Send/Sync respectively; Rust enforces those bounds outside SMT.
//!
//! This local snapshot and its adjacent `verus-bumpalo` dependency pin vstd
//! `=0.0.0-2026-10-04-0306`. Cargo manifests record their upstream revisions.
//! Verification of this revised dependency pair is a separate integration gate.
//!
//! For unverified callers, `BHConsign::get` checks uid bounds and the handle's
//! consign id and panics on mismatch; `HConsign` handles carry the same id. Ids
//! come from a process-wide `AtomicUsize` counter, so stale (freed-arena) and
//! foreign handles are rejected unless the counter wraps after 2^64 consigns.
//! Uniqueness is a runtime property: vstd's `fetch_add` spec is unconstrained and
//! no proof depends on it; `owns` is the verified contract. Other preconditions,
//! including arena insertion's `size_of::<T>() > 0`, and `HashKey::hash`/`key_eq`
//! postconditions are unenforced; an incorrect `key_eq` can silently break sharing.
//!
//! Owned uids are equal iff their shallow views are equal (`lemma_uid_eq`,
//! `lemma_no_duplicates`); ownership requires the handle's consign id. vstd has no
//! `Arc` allocation-identity spec, so pointer sharing is unstated. The lambda
//! clients in `demo` prove deep sharing with `scoped`, `deep_eq`, and
//! `lemma_deep_sharing`, whose child identity is `(cid, uid)`; interning a child
//! owned by another consign is allowed but never collapses with a local child.
//!
//! Global-heap growth of `Vec` and `Arc` is outside the verified failure model
//! and aborts on OOM in both storage modes. Arena bookkeeping (`ptrs` and the
//! index) is heap-allocated and grows; only `T` payloads are fixed-capacity.
//! The verified insertion failure path is bump exhaustion; construction can
//! return `AllocErr` but has no condition guaranteeing success.
//!
//! Lookup complexity is unspecified: the index doubles at load factor one,
//! but adversarial hashes degrade lookups to O(n). `free` never runs stored
//! `T` destructors, so resources owned by payloads leak; `tests/` is unverified
//! Rust, not part of the proof.
//!
//! | Original component | Verification boundary and replacement |
//! | --- | --- |
//! | `HashMap<T, _>` / `HashMap<&T, _>` | Generic key-model obligations cannot be proved for arbitrary client keys; replaced by verified uid-indexed `index::Buckets`. |
//! | Derived `Hash + Eq` | Not verified by Verus; replaced by the verified `HashKey` contract. |
//! | `Weak`, weak handles, collection, reference counts | No vstd `Weak` specification; dropped in favor of consign-held strong `Arc`s, without `T: Clone`. |
//! | `bumpalo::Bump` | Replaced by verified `verus-bumpalo` and tracked allocation permissions/tokens. |
//! | Arena `&T` handles | Replaced by inert copyable (consign id, uid) handles; references require `consign.get(handle)` and ownership. |
//! | `consign!`, collection wrappers/hashers, formatting, handle hashing, derives, folds, shrinking/capacity | External or out of scope; omitted. Use uid-keyed client collections. |
//! | `Arc` | Kept; its allocation, cloning, dereference, and view use vstd's trusted model. |
//!
//! User keys supply a verified `HashKey` implementation instead of `Hash + Eq`.
//! Heap storage retains strong references until the consign drops. Arena payload
//! capacity is fixed and insertion and construction are fallible.
//! Unlike `hashconsing`, uids are `usize`; weak handles/collection, global macros,
//! custom collection wrappers/hashers, formatting/derive helpers, folds, and shrinking
//! are not provided. Clients can key maps by `handle.uid()`.
//! Arena capacity, alignment, and remaining payload bytes have exact verified contracts.
//! Disable the default `std` feature for arena/index-only `no_std` + `alloc` clients.

#![no_std]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

use vstd::prelude::*;

pub use verus_bumpalo::AllocErr;
#[cfg(feature = "std")]
pub mod heap;
pub mod index;
#[cfg(feature = "std")]
pub use heap::{HConsed, HConsign};
pub mod arena;
pub use arena::{BHConsed, BHConsign};
#[cfg(feature = "std")]
pub mod demo;

verus! {

/// A shallow key view with verified hashing and equality.
pub trait HashKey: View + Sized {
    spec fn spec_hash(v: Self::V) -> u64;

    fn hash(&self) -> (h: u64)
        ensures h == Self::spec_hash(self@);

    fn key_eq(&self, other: &Self) -> (b: bool)
        ensures b == (self@ == other@);
}

pub open spec fn spec_mix(h: u64, x: u64) -> u64 {
    vstd::wrapping::u64_specs::wrapping_mul(h ^ x, 0x100000001b3)
}

/// Combines one word into a hash using wrapping arithmetic.
#[verifier::when_used_as_spec(spec_mix)]
pub fn mix(h: u64, x: u64) -> (r: u64)
    ensures r == spec_mix(h, x),
{
    (h ^ x).wrapping_mul(0x100000001b3)
}

exec static NEXT_CID: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

/// Process-unique consign id. vstd's `fetch_add` spec leaves the result unconstrained, so no
/// proof depends on uniqueness; it is a runtime guard property only.
// ponytail: usize counter wraps after 2^64 consigns per process; no verified panic primitive exists to abort on wrap
pub(crate) fn fresh_cid() -> usize {
    NEXT_CID.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
}

}
