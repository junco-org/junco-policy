//! Verified clients: shallow lambda terms identify their children by consign id and uid.
#[cfg(verus_only)]
use crate::spec_mix;
use crate::{mix, AllocErr, BHConsed, BHConsign, HConsed, HConsign, HashKey};
use vstd::prelude::*;

verus! {

pub type Term = HConsed<ActualTerm>;
pub type BTerm = BHConsed<BActualTerm>;
pub enum ActualTerm { Var(usize), Lam(Term), App(Term, Term) }
/// Identity of an interned child: its consign id and uid.
pub ghost struct Ident { pub cid: nat, pub uid: nat }
pub ghost enum TermV { Var(nat), Lam(Ident), App(Ident, Ident) }
pub open spec fn ident(h: Term) -> Ident { Ident { cid: h.spec_cid() as nat, uid: h.spec_uid() as nat } }
pub open spec fn bident(h: BTerm) -> Ident { Ident { cid: h.spec_cid() as nat, uid: h.spec_uid() as nat } }

/// Children of a shallow term view belong to consign `cid` and have uids strictly below `n`.
pub open spec fn children_in(v: TermV, cid: nat, n: int) -> bool {
    match v {
        TermV::Var(_) => true,
        TermV::Lam(u) => u.cid == cid && u.uid < n,
        TermV::App(a, b) => a.cid == cid && a.uid < n && b.cid == cid && b.uid < n,
    }
}

/// Every element's children were interned earlier in the same consign `cid`.
pub open spec fn scoped(s: Seq<TermV>, cid: nat) -> bool {
    forall|i: int| 0 <= i < s.len() ==> children_in(#[trigger] s[i], cid, i)
}

/// Structural (deep) equality of the terms at uids `i` and `j`, unfolding children by uid.
pub open spec fn deep_eq(s: Seq<TermV>, i: int, j: int) -> bool
    decreases i,
{
    0 <= i < s.len() && 0 <= j < s.len() && match (s[i], s[j]) {
        (TermV::Var(a), TermV::Var(b)) => a == b,
        (TermV::Lam(u), TermV::Lam(v)) => u.uid < i && deep_eq(s, u.uid as int, v.uid as int),
        (TermV::App(a, b), TermV::App(c, d)) =>
            a.uid < i && b.uid < i && deep_eq(s, a.uid as int, c.uid as int) && deep_eq(s, b.uid as int, d.uid as int),
        _ => false,
    }
}

pub proof fn lemma_scoped_mk(before: Seq<TermV>, after: Seq<TermV>, cid: nat, v: TermV)
    requires
        scoped(before, cid), children_in(v, cid, before.len() as int),
        after == before || after == before.push(v),
    ensures scoped(after, cid),
{
    assert forall|i: int| 0 <= i < after.len() implies children_in(#[trigger] after[i], cid, i) by {
        if i < before.len() { assert(after[i] == before[i]); }
    }
}

/// Perfect sharing at depth: structurally equal terms of a scoped, duplicate-free consign have one uid.
pub proof fn lemma_deep_sharing(s: Seq<TermV>, cid: nat, i: int, j: int)
    requires scoped(s, cid), s.no_duplicates(), deep_eq(s, i, j),
    ensures 0 <= i < s.len(), i == j,
    decreases i,
{
    match (s[i], s[j]) {
        (TermV::Lam(u), TermV::Lam(v)) => lemma_deep_sharing(s, cid, u.uid as int, v.uid as int),
        (TermV::App(a, b), TermV::App(c, d)) => {
            lemma_deep_sharing(s, cid, a.uid as int, c.uid as int);
            lemma_deep_sharing(s, cid, b.uid as int, d.uid as int);
        }
        _ => {}
    }
    assert(children_in(s[i], cid, i));
    assert(children_in(s[j], cid, j));
    assert(s[i] == s[j]);
}

impl View for ActualTerm {
    type V = TermV;
    open spec fn view(&self) -> TermV {
        match self {
            ActualTerm::Var(n) => TermV::Var(*n as nat),
            ActualTerm::Lam(t) => TermV::Lam(ident(*t)),
            ActualTerm::App(a, b) => TermV::App(ident(*a), ident(*b)),
        }
    }
}
impl HashKey for ActualTerm {
    open spec fn spec_hash(v: TermV) -> u64 {
        match v {
            TermV::Var(n) => spec_mix(0, n as u64),
            TermV::Lam(u) => spec_mix(1, u.uid as u64),
            TermV::App(a, b) => spec_mix(spec_mix(2, a.uid as u64), b.uid as u64),
        }
    }
    fn hash(&self) -> (h: u64)
        ensures h == Self::spec_hash(self@),
    {
        match self {
            ActualTerm::Var(n) => mix(0, *n as u64),
            ActualTerm::Lam(t) => mix(1, t.uid() as u64),
            ActualTerm::App(a, b) => mix(mix(2, a.uid() as u64), b.uid() as u64),
        }
    }
    fn key_eq(&self, o: &Self) -> (b: bool)
        ensures b == (self@ == o@),
    {
        match (self, o) {
            (ActualTerm::Var(a), ActualTerm::Var(b)) => *a == *b,
            (ActualTerm::Lam(a), ActualTerm::Lam(b)) => a.cid() == b.cid() && a.uid() == b.uid(),
            (ActualTerm::App(a, b), ActualTerm::App(c, d)) =>
                a.cid() == c.cid() && a.uid() == c.uid() && b.cid() == d.cid() && b.uid() == d.uid(),
            _ => false,
        }
    }
}

/// Reproduces the original heap example, proving sharing and fresh-node accounting.
pub fn heap_smoke() -> (n: usize)
    ensures n == 4,
{
    let mut f: HConsign<ActualTerm> = HConsign::empty();
    let ghost s = f@;
    let v = f.mk(ActualTerm::Var(0));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(0)); }
    let ghost s = f@;
    let v2 = f.mk(ActualTerm::Var(3));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(3)); }
    let ghost s = f@;
    let _lam = f.mk(ActualTerm::Lam(v2.clone()));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Lam(ident(v2))); }
    let ghost s = f@;
    let v3 = f.mk(ActualTerm::Var(3));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(3)); }
    proof {
        f.lemma_uid_eq(v2, v3);
        assert(v2.uid() == v3.uid());
    }
    let ghost s = f@;
    let lam2 = f.mk(ActualTerm::Lam(v3));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Lam(ident(v3))); }
    proof {
        f.lemma_uid_eq(_lam, lam2);
        assert(_lam.uid() == lam2.uid());
    }
    proof { assert(f.owns(v)); }
    let ghost s = f@;
    let _app = f.mk(ActualTerm::App(lam2, v));
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::App(ident(lam2), ident(v))); }
    assert(f@.len() == 4);
    proof {
        f.lemma_no_duplicates();
        assert forall|i: int, j: int| deep_eq(f@, i, j) implies i == j by {
            lemma_deep_sharing(f@, f.spec_cid() as nat, i, j);
        }
    }
    f.len()
}

pub enum BActualTerm { Var(usize), Lam(BTerm), App(BTerm, BTerm) }

impl View for BActualTerm {
    type V = TermV;
    open spec fn view(&self) -> TermV {
        match self {
            BActualTerm::Var(n) => TermV::Var(*n as nat),
            BActualTerm::Lam(t) => TermV::Lam(bident(*t)),
            BActualTerm::App(a, b) => TermV::App(bident(*a), bident(*b)),
        }
    }
}
impl HashKey for BActualTerm {
    open spec fn spec_hash(v: TermV) -> u64 { ActualTerm::spec_hash(v) }
    fn hash(&self) -> (h: u64)
        ensures h == Self::spec_hash(self@),
    {
        match self {
            BActualTerm::Var(n) => mix(0, *n as u64),
            BActualTerm::Lam(t) => mix(1, t.uid() as u64),
            BActualTerm::App(a, b) => mix(mix(2, a.uid() as u64), b.uid() as u64),
        }
    }
    fn key_eq(&self, o: &Self) -> (b: bool)
        ensures b == (self@ == o@),
    {
        match (self, o) {
            (BActualTerm::Var(a), BActualTerm::Var(b)) => *a == *b,
            (BActualTerm::Lam(a), BActualTerm::Lam(b)) => a.cid() == b.cid() && a.uid() == b.uid(),
            (BActualTerm::App(a, b), BActualTerm::App(c, d)) =>
                a.cid() == c.cid() && a.uid() == c.uid() && b.cid() == d.cid() && b.uid() == d.uid(),
            _ => false,
        }
    }
}

/// Proves every insertion succeeds once runtime sizing and arena construction succeed.
/// Returns `AllocErr` for zero-sized terms, sizing overflow, or chunk-allocation failure.
pub fn arena_smoke() -> (r: Result<usize, AllocErr>)
    ensures r matches Ok(n) ==> n == 4,
{
    vstd::layout::layout_for_type_is_valid::<BActualTerm>();
    let size = core::mem::size_of::<BActualTerm>();
    let align = core::mem::align_of::<BActualTerm>();
    if size == 0 { return Err(AllocErr::Capacity); }
    let Some(sa) = size.checked_add(align) else { return Err(AllocErr::Exhausted) };
    let need = sa - 1;
    let Some(bytes) = need.checked_mul(5) else { return Err(AllocErr::Exhausted) };
    let mut f: BHConsign<BActualTerm> = match BHConsign::new(bytes) {
        Ok(f) => f,
        Err(e) => return Err(e),
    };
    let ghost s = f@;
    let v = match f.try_mk(BActualTerm::Var(0)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(0)); }
    let ghost s = f@;
    let v2 = match f.try_mk(BActualTerm::Var(3)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(3)); }
    let ghost s = f@;
    let _lam = match f.try_mk(BActualTerm::Lam(v2)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Lam(bident(v2))); }
    let ghost s = f@;
    let v3 = match f.try_mk(BActualTerm::Var(3)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Var(3)); }
    proof {
        f.lemma_uid_eq(v2, v3);
        assert(v2.uid() == v3.uid());
    }
    let ghost s = f@;
    let lam2 = match f.try_mk(BActualTerm::Lam(v3)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::Lam(bident(v3))); }
    proof {
        f.lemma_uid_eq(_lam, lam2);
        assert(_lam.uid() == lam2.uid());
    }
    proof { assert(f.owns(v)); }
    let ghost s = f@;
    let _app = match f.try_mk(BActualTerm::App(lam2, v)) {
        Ok(h) => h, Err(_) => vstd::pervasive::unreached(),
    };
    proof { lemma_scoped_mk(s, f@, f.spec_cid() as nat, TermV::App(bident(lam2), bident(v))); }
    assert(f@.len() == 4);
    proof {
        f.lemma_no_duplicates();
        assert forall|i: int, j: int| deep_eq(f@, i, j) implies i == j by {
            lemma_deep_sharing(f@, f.spec_cid() as nat, i, j);
        }
    }
    let n = f.len();
    f.free();
    Ok(n)
}

}
