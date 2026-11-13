//! Tests of the assumed specifications in `crates/junco-core/src/verify/history_assumptions.rs`
//! against the real std and smallvec implementations, with verus-spec-check.
//!
//! Each `#[vcheck]` wrapper restates one `assume_specification` at element type `u32` and calls
//! the native function; a failing harness means that specification does not describe the
//! implementation. Wrappers are needed because verus-spec-check cannot attach to methods of
//! generic inherent impls. Keep each contract identical to the one it restates.
//! `core::mem::drop` has no contract and is not tested. Run with `scripts/spec-check.sh`.

use smallvec::SmallVec;
use verus_spec_check::*;
use vstd::prelude::*;

/// Inline capacity 4, so sampled inputs exercise both inline and spilled storage.
type Small = SmallVec<[u32; 4]>;

verus! {

// ===== SmallVec =====

/// `SmallVec::<A>::new`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_new() -> (r: Vec<u32>)
    ensures r@ == Seq::<u32>::empty(),
{
    Small::new().to_vec()
}

/// `SmallVec::<A>::len`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_len(v: Vec<u32>) -> (n: usize)
    ensures n == v@.len(),
{
    Small::from_slice(&v).len()
}

/// `SmallVec::<A>::is_empty`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_is_empty(v: Vec<u32>) -> (r: bool)
    ensures r == (v@.len() == 0),
{
    Small::from_slice(&v).is_empty()
}

/// `SmallVec::<A>::push`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_push(v: Vec<u32>, value: u32) -> (r: Vec<u32>)
    ensures r@ == v@.push(value),
{
    let mut s = Small::from_slice(&v);
    s.push(value);
    s.to_vec()
}

/// `SmallVec::<A>::extend_from_slice`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_extend_from_slice(v: Vec<u32>, values: Vec<u32>) -> (r: Vec<u32>)
    ensures r@ == v@ + values@,
{
    let mut s = Small::from_slice(&v);
    s.extend_from_slice(&values);
    s.to_vec()
}

/// `SmallVec::<A>::remove`; returns the removed item and the remaining contents.
#[vcheck(mode = "fuzz")]
#[verifier::external_body]
pub fn smallvec_remove(v: Vec<u32>, index: usize) -> (r: (u32, Vec<u32>))
    requires index < v@.len(),
    ensures r.0 == v@[index as int], r.1@ == v@.remove(index as int),
{
    let mut s = Small::from_slice(&v);
    let removed = s.remove(index);
    (removed, s.to_vec())
}

/// `SmallVec::<A>::pop`; returns the popped item and the remaining contents.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_pop(v: Vec<u32>) -> (r: (Option<u32>, Vec<u32>))
    ensures
        v@.len() == 0 ==> r.0 is None && r.1@ == v@,
        v@.len() > 0 ==> r.0 == Some(v@.last()) && r.1@ == v@.drop_last(),
{
    let mut s = Small::from_slice(&v);
    let popped = s.pop();
    (popped, s.to_vec())
}

/// `SmallVec::<A>::truncate`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_truncate(v: Vec<u32>, len: usize) -> (r: Vec<u32>)
    ensures
        len <= v@.len() ==> r@ == v@.subrange(0, len as int),
        len > v@.len() ==> r@ == v@,
{
    let mut s = Small::from_slice(&v);
    s.truncate(len);
    s.to_vec()
}

/// `SmallVec::<A>::resize`; `cloned` is equality for `u32`. The `len` bound only keeps the
/// test's allocations small.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_resize(v: Vec<u32>, len: usize, value: u32) -> (r: Vec<u32>)
    requires len <= 64,
    ensures
        len <= v@.len() ==> r@ == v@.subrange(0, len as int),
        len > v@.len() ==> {
            &&& r@.len() == len
            &&& r@.subrange(0, v@.len() as int) == v@
            &&& forall|i: int| v@.len() <= i < len ==> r@[i] == value
        },
{
    let mut s = Small::from_slice(&v);
    s.resize(len, value);
    s.to_vec()
}

/// `SmallVec::<A>::try_reserve_exact`: contents are unchanged on success and on failure.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_try_reserve_exact(v: Vec<u32>, additional: usize) -> (r: Vec<u32>)
    ensures r@ == v@,
{
    let mut s = Small::from_slice(&v);
    let _ = s.try_reserve_exact(additional);
    s.to_vec()
}

/// `<SmallVec<A> as Deref>::deref`.
#[vcheck]
#[verifier::external_body]
pub fn smallvec_deref(v: Vec<u32>) -> (r: Vec<u32>)
    ensures r@ == v@,
{
    let s = Small::from_slice(&v);
    let slice: &[u32] = &s;
    slice.to_vec()
}

/// `SmallVec::<A>::as_mut_slice`: the slice views the contents, and writes through it are
/// writes to the vector.
#[vcheck(mode = "fuzz")]
#[verifier::external_body]
pub fn smallvec_as_mut_slice(v: Vec<u32>, index: usize, value: u32) -> (r: Vec<u32>)
    requires index < v@.len(),
    ensures r@ == v@.update(index as int, value),
{
    let mut s = Small::from_slice(&v);
    s.as_mut_slice()[index] = value;
    s.to_vec()
}

// ===== slices, Vec, Option, mem, String =====

/// Occurrences of `x` in `s` (`usize`: verus-spec-check compiles spec functions over machine
/// integers, and test inputs are far shorter than `usize::MAX`).
pub open spec fn count(s: Seq<u32>, x: u32) -> usize
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if s.last() == x {
        (count(s.drop_last(), x) + 1) as usize
    } else {
        count(s.drop_last(), x)
    }
}

/// `<[T]>::sort_unstable` at `u32`, whose `cmp_spec` is the integer order.
#[vcheck]
#[verifier::external_body]
pub fn slice_sort_unstable(v: Vec<u32>) -> (r: Vec<u32>)
    ensures
        // `r@.to_multiset() == v@.to_multiset()`, which verus-spec-check cannot evaluate:
        // equal lengths and equal counts of every input element are the same condition.
        r@.len() == v@.len(),
        forall|k: int| 0 <= k < v@.len() ==> count(r@, v@[k]) == count(v@, v@[k]),
        forall|i: int, j: int| 0 <= i < r@.len() && i < j < r@.len() ==> r@[i] <= r@[j],
{
    let mut sorted = v.clone();
    sorted.as_mut_slice().sort_unstable();
    sorted
}

/// `dedup_spec` at `u32`, whose `eq_spec` is equality.
pub open spec fn dedup_spec(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() <= 1 {
        s
    } else if s[s.len() - 1] == s[s.len() - 2] {
        dedup_spec(s.drop_last())
    } else {
        dedup_spec(s.drop_last()).push(s.last())
    }
}

/// `Vec::<T, A>::dedup`.
#[vcheck]
#[verifier::external_body]
pub fn vec_dedup(v: Vec<u32>) -> (r: Vec<u32>)
    ensures r@ == dedup_spec(v@),
{
    let mut deduped = v.clone();
    deduped.dedup();
    deduped
}

/// `<[T]>::binary_search` on a strictly sorted slice.
#[vcheck(mode = "fuzz")]
#[verifier::external_body]
pub fn slice_binary_search(s: Vec<u32>, value: u32) -> (r: Result<usize, usize>)
    requires forall|i: int, j: int| 0 <= i < s@.len() && i < j < s@.len() ==> s@[i] < s@[j],
    ensures
        match r {
            Ok(i) => i < s@.len() && s@[i as int] == value,
            Err(_) => forall|i: int| 0 <= i < s@.len() ==> s@[i] != value,
        },
{
    s.as_slice().binary_search(&value)
}

/// `Option::<&T>::copied`.
#[vcheck]
#[verifier::external_body]
pub fn option_copied(v: Option<u32>) -> (r: Option<u32>)
    ensures r == v,
{
    v.as_ref().copied()
}

/// `Vec::<T, A>::into_boxed_slice`, read back through `into_vec`.
#[vcheck]
#[verifier::external_body]
pub fn vec_into_boxed_slice(v: Vec<u32>) -> (r: Vec<u32>)
    ensures r@ == v@,
{
    v.clone().into_boxed_slice().into_vec()
}

/// `String::try_reserve`: contents are unchanged on success and on failure.
#[vcheck]
#[verifier::external_body]
pub fn string_try_reserve(value: String, additional: usize) -> (r: String)
    ensures r@ == value@,
{
    let mut reserved = value.clone();
    let _ = reserved.try_reserve(additional);
    reserved
}

} // verus!
