//! Chained hash index; user-key comparison stays in the consign.
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

pub struct Buckets { b: Vec<Vec<(u64, usize)>> }

impl Buckets {
    pub closed spec fn nb(self) -> int { self.b@.len() as int }

    pub closed spec fn bucket_of(self, h: u64) -> Seq<(u64, usize)>
        recommends self.nb() > 0,
    { self.b@[h as int % (self.b@.len() as int)]@ }

    pub closed spec fn inv(self, hashes: Seq<u64>) -> bool {
        &&& self.b@.len() > 0
        &&& forall|i: int, j: int| 0 <= i < self.b@.len() && 0 <= j < self.b@[i]@.len() ==> {
            let e = #[trigger] self.b@[i]@[j];
            &&& e.1 < hashes.len()
            &&& hashes[e.1 as int] == e.0
            &&& e.0 as int % (self.b@.len() as int) == i
        }
        &&& forall|u: int| 0 <= u < hashes.len() ==>
            #[trigger] self.bucket_of(hashes[u]).contains((hashes[u], u as usize))
    }

    pub fn new(capacity: usize) -> (r: Self)
        ensures r.inv(Seq::empty()), r.nb() == if capacity == 0 { 1int } else { capacity as int },
    {
        let n = if capacity == 0 { 1 } else { capacity };
        let mut b: Vec<Vec<(u64, usize)>> = Vec::with_capacity(n);
        while b.len() < n
            invariant b@.len() <= n, forall|i: int| 0 <= i < b@.len() ==> #[trigger] b@[i]@.len() == 0,
            decreases n - b@.len(),
        { b.push(Vec::new()); }
        Self { b }
    }

    pub proof fn lemma_nonempty(self, hashes: Seq<u64>)
        requires self.inv(hashes),
        ensures self.nb() > 0,
    { }

    pub fn bucket(&self, h: u64) -> (r: &Vec<(u64, usize)>)
        requires self.nb() > 0,
        ensures r@ == self.bucket_of(h),
    {
        let n = self.b.len();
        &self.b[(h % (n as u64)) as usize]
    }

    pub fn insert(&mut self, h: u64, uid: usize, Ghost(hashes): Ghost<Seq<u64>>)
        requires old(self).inv(hashes), uid == hashes.len(), hashes.len() < usize::MAX,
        ensures final(self).inv(hashes.push(h)),
    {
        let n = self.b.len();
        let i = (h % (n as u64)) as usize;
        let ghost before = self.b@;
        let ghost old_index = *self;
        self.b[i].push((h, uid));
        proof {
            assert forall|u: int| 0 <= u < hashes.push(h).len()
                implies #[trigger] self.bucket_of(hashes.push(h)[u]).contains((hashes.push(h)[u], u as usize)) by {
                if u < hashes.len() {
                    old_index.lemma_complete(hashes, u);
                    let k = hashes[u] as int % (n as int);
                    assert(before[k]@.contains((hashes[u], u as usize)));
                    let j = before[k]@.lemma_contains_to_index((hashes[u], u as usize));
                    assert(self.b@[k]@[j] == (hashes[u], u as usize));
                } else {
                    assert(self.b@[i as int]@.last() == (h, uid));
                }
            }
            assert(self.inv(hashes.push(h)));
        }
        if self.b.len() < uid + 1 && n <= usize::MAX / 2 {
            self.grow_to(2 * n, Ghost(hashes.push(h)));
        }
    }

    pub fn reserve(&mut self, total: usize, Ghost(hashes): Ghost<Seq<u64>>)
        requires old(self).inv(hashes),
        ensures final(self).inv(hashes), final(self).nb() >= total,
    {
        if total > self.b.len() { self.grow_to(total, Ghost(hashes)); }
    }

    fn grow_to(&mut self, target: usize, Ghost(hashes): Ghost<Seq<u64>>)
        requires old(self).inv(hashes), target >= 1,
        ensures final(self).inv(hashes), final(self).nb() == target,
    {
        let mut next = Self::new(target);
        let mut i = 0;
        while i < self.b.len()
            invariant
                self.inv(hashes), next.nb() == target, target >= 1,
                0 <= i <= self.b@.len(),
                forall|a: int, c: int| 0 <= a < next.b@.len() && 0 <= c < next.b@[a]@.len() ==> {
                    let e = #[trigger] next.b@[a]@[c];
                    e.1 < hashes.len() && hashes[e.1 as int] == e.0 && e.0 as int % (target as int) == a
                },
                forall|a: int, c: int| 0 <= a < i && 0 <= c < self.b@[a]@.len() ==>
                    #[trigger] next.bucket_of(self.b@[a]@[c].0).contains(self.b@[a]@[c]),
            decreases self.b@.len() - i,
        {
            let bucket = &self.b[i];
            let mut j = 0;
            while j < bucket.len()
                invariant
                    self.inv(hashes), next.nb() == target, target >= 1,
                    0 <= i < self.b@.len(), bucket == self.b@[i as int],
                    0 <= j <= bucket@.len(),
                    forall|a: int, c: int| 0 <= a < next.b@.len() && 0 <= c < next.b@[a]@.len() ==> {
                        let e = #[trigger] next.b@[a]@[c];
                        e.1 < hashes.len() && hashes[e.1 as int] == e.0 && e.0 as int % (target as int) == a
                    },
                    forall|a: int, c: int| 0 <= a < self.b@.len() && 0 <= c < self.b@[a]@.len()
                        && (a < i || (a == i && c < j)) ==>
                        #[trigger] next.bucket_of(self.b@[a]@[c].0).contains(self.b@[a]@[c]),
                decreases bucket@.len() - j,
            {
                let e = bucket[j];
                let k = (e.0 % (target as u64)) as usize;
                let ghost before = next;
                next.b[k].push(e);
                proof {
                    assert(e.1 < hashes.len() && hashes[e.1 as int] == e.0);
                    assert forall|a: int, c: int| 0 <= a < self.b@.len() && 0 <= c < self.b@[a]@.len()
                        && (a < i || (a == i && c < j + 1))
                        implies #[trigger] next.bucket_of(self.b@[a]@[c].0).contains(self.b@[a]@[c]) by {
                        let old_e = self.b@[a]@[c];
                        if a == i && c == j {
                            assert(old_e == e);
                            assert(next.b@[k as int]@.last() == e);
                        } else {
                            let bidx = old_e.0 as int % (target as int);
                            assert(before.bucket_of(old_e.0).contains(old_e));
                            let pos = before.bucket_of(old_e.0).lemma_contains_to_index(old_e);
                            assert(next.b@[bidx]@[pos] == old_e);
                        }
                    }
                }
                j += 1;
            }
            i += 1;
        }
        proof {
            assert forall|u: int| 0 <= u < hashes.len()
                implies #[trigger] next.bucket_of(hashes[u]).contains((hashes[u], u as usize)) by {
                let bidx = hashes[u] as int % (self.b@.len() as int);
                assert(self.bucket_of(hashes[u]).contains((hashes[u], u as usize)));
                let pos = self.bucket_of(hashes[u]).lemma_contains_to_index((hashes[u], u as usize));
                assert(self.b@[bidx]@[pos] == (hashes[u], u as usize));
            }
        }
        self.b = next.b;
    }

    pub proof fn lemma_sound(self, hashes: Seq<u64>, h: u64, j: int)
        requires self.inv(hashes), 0 <= j < self.bucket_of(h).len(),
        ensures self.bucket_of(h)[j].1 < hashes.len(),
            hashes[self.bucket_of(h)[j].1 as int] == self.bucket_of(h)[j].0,
    { }

    pub proof fn lemma_complete(self, hashes: Seq<u64>, u: int)
        requires self.inv(hashes), 0 <= u < hashes.len(),
        ensures self.bucket_of(hashes[u]).contains((hashes[u], u as usize)),
    { }
}

}
