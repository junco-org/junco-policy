use verus_bumpalo::{AllocErr, SliceArena, TypedArena};

#[test]
fn arena_round_trips() {
    let mut values = TypedArena::with_capacity(4096).unwrap();
    for value in [11u64, 22, 33] {
        let index = values.try_push(value).unwrap();
        assert_eq!(values.get(index), Some(&value));
    }
    assert_eq!(values.len(), 3);
    assert_eq!(values.get(0), Some(&11));
    assert_eq!(values.get(1), Some(&22));
    assert_eq!(values.get(2), Some(&33));
    assert_eq!(values.get(values.len()), None);
    values.free();

    let mut slices = SliceArena::with_capacity(4096).unwrap();
    for slice in [&[][..], &[1u32][..], &[2, 3, 4][..]] {
        let index = slices.try_push(slice).unwrap();
        assert_eq!(slices.get(index), Some(slice));
    }
    assert_eq!(slices.len(), 3);
    assert_eq!(slices.get(0), Some(&[][..]));
    assert_eq!(slices.get(1), Some(&[1][..]));
    assert_eq!(slices.get(2), Some(&[2, 3, 4][..]));
    assert_eq!(slices.get(slices.len()), None);
    slices.free();
}

#[test]
fn allocation_failure_preserves_contents() {
    assert_eq!(
        TypedArena::<u64>::with_capacity(0).err(),
        Some(AllocErr::Capacity)
    );
    assert_eq!(
        TypedArena::<u64>::with_capacity(usize::MAX).err(),
        Some(AllocErr::Capacity)
    );
    let mut values = TypedArena::with_capacity(64).unwrap();
    for index in 0..8 {
        assert_eq!(values.try_push(index as u64), Ok(index));
    }
    assert_eq!(values.try_push(99), Err(AllocErr::Exhausted));
    assert_eq!(values.len(), 8);
    for index in 0..8 {
        assert_eq!(values.get(index), Some(&(index as u64)));
    }
    values.free();

    let mut slices = SliceArena::with_capacity(64).unwrap();
    assert_eq!(slices.try_push(&[1u64, 2, 3]), Ok(0));
    assert_eq!(slices.try_push(&[4, 5, 6]), Ok(1));
    assert_eq!(slices.try_push(&[7, 8, 9]), Err(AllocErr::Exhausted));
    assert_eq!(slices.len(), 2);
    assert_eq!(slices.get(0), Some(&[1, 2, 3][..]));
    assert_eq!(slices.get(1), Some(&[4, 5, 6][..]));
    slices.free();

    // Aligned cursor, first push already too large: exhausted exactly when w > remaining.
    let mut wide = TypedArena::<[u8; 32]>::with_capacity(16).unwrap();
    assert_eq!(wide.try_push([0; 32]), Err(AllocErr::Exhausted));
    assert_eq!(wide.len(), 0);
    wide.free();
}

#[test]
fn zero_sized_values_and_empty_slices() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[repr(align(64))]
    struct Aligned;

    let mut values = TypedArena::with_capacity(256).unwrap();
    assert_eq!(values.try_push(Aligned), Ok(0));
    assert_eq!(values.try_push(Aligned), Ok(1));
    assert_eq!(values.get(0), Some(&Aligned));
    assert_eq!(values.get(1), Some(&Aligned));
    values.free();

    let mut slices = SliceArena::with_capacity(256).unwrap();
    assert_eq!(slices.try_push(&[] as &[Aligned]), Ok(0));
    assert_eq!(slices.try_push(&[Aligned, Aligned]), Ok(1));
    assert_eq!(slices.get(0), Some(&[][..]));
    assert_eq!(slices.get(1), Some(&[Aligned, Aligned][..]));
    slices.free();
}
