use hashconsius::demo::{self, ActualTerm, BActualTerm};
use hashconsius::{BHConsign, HConsign};
use std::cmp::Ordering;

#[test]
fn verified_lambda_examples() {
    assert_eq!(demo::heap_smoke(), 4);
    assert_eq!(demo::arena_smoke().unwrap(), 4);
}

#[test]
fn heap_sharing_lookup_and_retained_handles() {
    let mut f = HConsign::with_capacity(0);
    assert!(f.is_empty());
    let (a, fresh) = f.mk_is_new(ActualTerm::Var(0));
    assert!(fresh);
    let (same, fresh) = f.mk_is_new(ActualTerm::Var(0));
    assert!(!fresh && a == same);
    let b = f.mk(ActualTerm::Var(3));
    assert!(a < b && a.partial_cmp(&b) == Some(Ordering::Less));
    assert_eq!(a.cmp(&same), Ordering::Equal);
    assert!(f.contains(&ActualTerm::Var(0)));
    assert!(!f.contains(&ActualTerm::Var(4)));
    f.reserve(100);
    assert_eq!(f.len(), 2);
    assert!(matches!(f.elem(b.uid()), ActualTerm::Var(3)));
    drop(f);
    assert!(matches!(a.get(), ActualTerm::Var(0)));
}

#[test]
fn heap_index_growth_preserves_sharing() {
    let mut f = HConsign::empty();
    for i in 0..1000 {
        let (h, fresh) = f.mk_is_new(ActualTerm::Var(i));
        assert!(fresh);
        assert_eq!(h.uid(), i);
    }
    assert_eq!(f.len(), 1000);
    let (h, fresh) = f.mk_is_new(ActualTerm::Var(500));
    assert!(!fresh);
    assert_eq!(h.uid(), 500);
    assert_eq!(f.len(), 1000);
    f.reserve(100);
    for uid in 0..f.len() {
        assert!(matches!(f.elem(uid), ActualTerm::Var(n) if *n == uid));
    }
}

#[test]
fn arena_exhaustion_preserves_input_and_state() {
    let mut small = BHConsign::<BActualTerm>::new(std::mem::size_of::<BActualTerm>() - 1).unwrap();
    assert!(matches!(
        small.try_mk(BActualTerm::Var(0)),
        Err(BActualTerm::Var(0))
    ));
    assert_eq!(small.len(), 0);
    small.reserve(100);
    assert!(small.is_empty());
    small.free();

    let mut f = BHConsign::new(std::mem::size_of::<BActualTerm>()).unwrap();
    let a = match f.try_mk(BActualTerm::Var(3)) {
        Ok(h) => h,
        Err(_) => panic!("one value must fit the chunk"),
    };
    assert!(matches!(
        f.try_mk(BActualTerm::Var(8)),
        Err(BActualTerm::Var(8))
    ));
    let (same, fresh) = match f.try_mk_is_new(BActualTerm::Var(3)) {
        Ok(pair) => pair,
        Err(_) => panic!("existing values do not need arena space"),
    };
    assert!(!fresh && a == same);
    assert_eq!(a.cmp(&same), Ordering::Equal);
    assert_eq!(f.len(), 1);
    assert!(f.contains(&BActualTerm::Var(3)));
    assert!(!f.contains(&BActualTerm::Var(8)));
    f.reserve(100);
    assert!(matches!(f.get(a), BActualTerm::Var(3)));
    assert!(matches!(f.elem(a.uid()), BActualTerm::Var(3)));
    f.free();
}

#[test]
fn arena_get_rejects_foreign_handle() {
    let mut a = BHConsign::new(4096).unwrap();
    let mut b = BHConsign::new(4096).unwrap();
    let Ok(h) = a.try_mk(BActualTerm::Var(1)) else {
        panic!("fits")
    };
    let Ok(_) = b.try_mk(BActualTerm::Var(2)) else {
        panic!("fits")
    };
    let hit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = b.get(h);
    }));
    assert!(hit.is_err(), "foreign handle must panic, not read");
    assert!(matches!(a.get(h), BActualTerm::Var(1)));
    a.free();
    b.free();
}

#[test]
fn arena_get_rejects_stale_handle_after_free() {
    let mut a = BHConsign::new(4096).unwrap();
    let Ok(h) = a.try_mk(BActualTerm::Var(1)) else {
        panic!("fits")
    };
    assert!(matches!(a.get(h), BActualTerm::Var(1)));
    a.free();
    for _ in 0..16 {
        let mut b = BHConsign::new(4096).unwrap();
        let Ok(_) = b.try_mk(BActualTerm::Var(2)) else {
            panic!("fits")
        };
        let hit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = b.get(h);
        }));
        assert!(
            hit.is_err(),
            "stale handle must panic even when the chunk address is reused"
        );
        b.free();
    }
}

#[test]
fn heap_foreign_child_does_not_collapse() {
    let mut f = HConsign::empty();
    let mut g = HConsign::empty();
    let f0 = f.mk(ActualTerm::Var(0));
    let g0 = g.mk(ActualTerm::Var(99));
    let f1 = f.mk(ActualTerm::Lam(f0));
    let g1 = g.mk(ActualTerm::Lam(g0));
    assert_eq!((f1.uid(), g1.uid()), (1, 1));
    assert!(
        f1 != g1,
        "same uid in different consigns must not compare equal"
    );
    let foreign = f.mk(ActualTerm::Lam(g1));
    let local = f.mk(ActualTerm::Lam(f1));
    assert_ne!(foreign.uid(), local.uid());
    assert_eq!(f.len(), 4);
    let ActualTerm::Lam(c) = local.get() else {
        panic!("Lam")
    };
    let ActualTerm::Lam(l) = c.get() else {
        panic!("Lam")
    };
    assert!(matches!(l.get(), ActualTerm::Var(0)));
}

#[test]
fn arena_foreign_child_does_not_collapse() {
    let mut f = BHConsign::new(4096).unwrap();
    let mut g = BHConsign::new(4096).unwrap();
    let Ok(f0) = f.try_mk(BActualTerm::Var(0)) else {
        panic!("fits")
    };
    let Ok(g0) = g.try_mk(BActualTerm::Var(99)) else {
        panic!("fits")
    };
    let Ok(f1) = f.try_mk(BActualTerm::Lam(f0)) else {
        panic!("fits")
    };
    let Ok(g1) = g.try_mk(BActualTerm::Lam(g0)) else {
        panic!("fits")
    };
    assert!(
        f1 != g1,
        "same uid in different arenas must not compare equal"
    );
    let Ok(foreign) = f.try_mk(BActualTerm::Lam(g1)) else {
        panic!("fits")
    };
    let Ok(local) = f.try_mk(BActualTerm::Lam(f1)) else {
        panic!("fits")
    };
    assert_ne!(foreign.uid(), local.uid());
    assert_eq!(f.len(), 4);
    f.free();
    g.free();
}
