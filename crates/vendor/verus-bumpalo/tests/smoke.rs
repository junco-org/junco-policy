use core::alloc::Layout;
use verus_bumpalo::Bump;
use vstd::prelude::Tracked;

#[test]
fn verified_smoke() {
    assert_eq!(verus_bumpalo::smoke(), Ok(42));
}

#[test]
fn runtime_behaviour() {
    assert!(Bump::try_with_capacity(0).is_err());
    assert!(Bump::try_with_capacity(usize::MAX).is_err());

    let (mut bump, _st) = Bump::try_with_capacity(256).unwrap();
    let oversized = Layout::from_size_align(257, 1).unwrap();
    assert!(bump
        .try_alloc_layout(oversized, Tracked::assume_new())
        .is_err());

    let aligned = Layout::from_size_align(8, 64).unwrap();
    let (p, _, _) = bump
        .try_alloc_layout(aligned, Tracked::assume_new())
        .unwrap();
    assert_eq!(p as usize % 64, 0);

    let byte = Layout::new::<u8>();
    let mut n = 0;
    while bump.try_alloc_layout(byte, Tracked::assume_new()).is_ok() {
        n += 1;
        assert!(n < 256, "allocation must consume the fixed chunk");
    }
    assert!(n >= 256 - 64 - 8);
    assert!(bump.try_alloc_layout(byte, Tracked::assume_new()).is_err());

    bump.reset(Tracked::assume_new(), Tracked::assume_new());
    let (p2, _, _) = bump
        .try_alloc_layout(aligned, Tracked::assume_new())
        .unwrap();
    assert_eq!(p2, p);

    let (q, _, _) = bump
        .try_alloc_layout(aligned, Tracked::assume_new())
        .unwrap();
    bump.reset_to(p2 as usize, Tracked::assume_new(), Tracked::assume_new());
    let (q2, _, _) = bump
        .try_alloc_layout(aligned, Tracked::assume_new())
        .unwrap();
    assert_eq!(q2, q);

    bump.reset(Tracked::assume_new(), Tracked::assume_new());
    let zero = Layout::from_size_align(0, 64).unwrap();
    let (z1, _, _) = bump.try_alloc_layout(zero, Tracked::assume_new()).unwrap();
    let (z2, _, _) = bump.try_alloc_layout(zero, Tracked::assume_new()).unwrap();
    assert_eq!(z1 as usize % 64, 0);
    assert_eq!(z1, z2);

    bump.reset(Tracked::assume_new(), Tracked::assume_new());
    let whole = Layout::from_size_align(256, 1).unwrap();
    assert!(bump.try_alloc_layout(whole, Tracked::assume_new()).is_ok());
    assert!(bump.try_alloc_layout(byte, Tracked::assume_new()).is_err());
    bump.free(Tracked::assume_new(), Tracked::assume_new());
}
