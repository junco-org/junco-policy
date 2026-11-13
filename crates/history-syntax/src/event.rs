//! Compact, statically dispatched events with policy-selected coordinates.

use core::fmt::Debug;
use core::hash::Hash;
use frunk_core::coproduct::{CNil, Coproduct};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::spec::events::{AritySpec, EventSpec, EventSpecImpl};

verus! {
/// Largest arity any event type may declare; sizes inline numeric tuples.
pub const MAX_ARITY: usize = 8;
}

pub(crate) mod sealed {
    #[vstd::prelude::verus_verify]
    pub trait Sealed {}
}

/// Type-level event arity. Only [`N1`] through [`N8`] implement this trait.
pub trait Arity: sealed::Sealed {
    /// Number of coordinates, between one and [`MAX_ARITY`] inclusive.
    fn value() -> usize;
}

macro_rules! arities {
    ($($name:ident = $value:literal),+ $(,)?) => {$ (
        #[doc = concat!("An event with ", stringify!($value), " coordinates.")]
        #[verus_verify]
        pub struct $name;

        #[verus_verify]
        impl sealed::Sealed for $name {}

        #[verus_verify]
        impl Arity for $name {
            fn value() -> usize { $value }
        }

        #[cfg(verus_keep_ghost)]
        verus! {
            impl crate::spec::events::AritySpecImpl for $name {
                open spec fn value_spec() -> nat { $value }
            }
        }
    )+};
}

arities!(
    N1 = 1,
    N2 = 2,
    N3 = 3,
    N4 = 4,
    N5 = 5,
    N6 = 6,
    N7 = 7,
    N8 = 8
);

/// Event matched by heads and tail atoms.
///
/// Equality and hashing describe the full event, including its variant and payload.
/// Projections, equality and hashing must remain stable while values are used by a policy.
pub trait Event: Copy + Debug + Eq + Hash {
    /// Tagged value of one coordinate, with one variant per coordinate.
    type Component: Copy + Debug + Eq + Hash;
    /// Number of coordinates in this event.
    type Arity: Arity;

    /// Projects coordinate `index`; out-of-range indices map to the last coordinate.
    fn component(self, index: usize) -> Self::Component;
    /// Returns the coordinate of a tagged value.
    ///
    /// For every valid `i`, `Self::coordinate(event.component(i)) == i`.
    fn coordinate(component: Self::Component) -> usize;
}

/// Tagged coordinates of a two-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component2<A, B> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
}

/// Tagged coordinates of a three-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component3<A, B, C> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
    /// Coordinate two.
    C2(C),
}

/// Tagged coordinates of a four-component tuple event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Component4<A, B, C, D> {
    /// Coordinate zero.
    C0(A),
    /// Coordinate one.
    C1(B),
    /// Coordinate two.
    C2(C),
    /// Coordinate three.
    C3(D),
}

#[verus_verify]
impl<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash> Event for (A, B)
where
    (A, B): Copy,
{
    type Component = Component2<A, B>;
    type Arity = N2;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component2::C0(self.0),
            _ => Component2::C1(self.1),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component2::C0(_) => 0,
            Component2::C1(_) => 1,
        }
    }
}

#[verus_verify]
impl<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash, C: Copy + Debug + Eq + Hash> Event
    for (A, B, C)
where
    (A, B, C): Copy,
{
    type Component = Component3<A, B, C>;
    type Arity = N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component3::C0(self.0),
            1 => Component3::C1(self.1),
            _ => Component3::C2(self.2),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component3::C0(_) => 0,
            Component3::C1(_) => 1,
            Component3::C2(_) => 2,
        }
    }
}

#[verus_verify]
impl<
    A: Copy + Debug + Eq + Hash,
    B: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash,
    D: Copy + Debug + Eq + Hash,
> Event for (A, B, C, D)
where
    (A, B, C, D): Copy,
{
    type Component = Component4<A, B, C, D>;
    type Arity = N4;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component4::C0(self.0),
            1 => Component4::C1(self.1),
            2 => Component4::C2(self.2),
            _ => Component4::C3(self.3),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component4::C0(_) => 0,
            Component4::C1(_) => 1,
            Component4::C2(_) => 2,
            Component4::C3(_) => 3,
        }
    }
}

// The pinned verifier rejects zero-arm matches; this leaf eliminates only Frunk's empty CNil.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures false)]
fn absurd_nil<T>(nil: CNil) -> T {
    match nil {}
}

/// Final variant of a Frunk event union.
#[verus_verify]
impl<H: Event> Event for Coproduct<H, CNil> {
    type Component = H::Component;
    type Arity = H::Arity;

    fn component(self, index: usize) -> Self::Component {
        match self {
            Coproduct::Inl(head) => head.component(index),
            Coproduct::Inr(nil) => absurd_nil(nil),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        H::coordinate(component)
    }
}

/// Head variant of a Frunk event union sharing tagged coordinates and arity.
#[verus_verify]
impl<H, T, Rest> Event for Coproduct<H, Coproduct<T, Rest>>
where
    H: Event,
    Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>,
{
    type Component = H::Component;
    type Arity = H::Arity;

    fn component(self, index: usize) -> Self::Component {
        match self {
            Coproduct::Inl(head) => head.component(index),
            Coproduct::Inr(tail) => tail.component(index),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        H::coordinate(component)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash> EventSpecImpl for (A, B)
    where (A, B): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component2::C0(self.0) } else { Component2::C1(self.1) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component { Component2::C0(_) => 0, Component2::C1(_) => 1 }
        }
    }

    impl<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash, C: Copy + Debug + Eq + Hash>
        EventSpecImpl for (A, B, C)
    where (A, B, C): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component3::C0(self.0) }
            else if index == 1 { Component3::C1(self.1) }
            else { Component3::C2(self.2) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component { Component3::C0(_) => 0, Component3::C1(_) => 1, Component3::C2(_) => 2 }
        }
    }

    impl<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash,
        C: Copy + Debug + Eq + Hash, D: Copy + Debug + Eq + Hash> EventSpecImpl for (A, B, C, D)
    where (A, B, C, D): Copy,
    {
        open spec fn obeys_projection_spec() -> bool { true }
        open spec fn component_spec(self, index: int) -> Self::Component {
            if index == 0 { Component4::C0(self.0) }
            else if index == 1 { Component4::C1(self.1) }
            else if index == 2 { Component4::C2(self.2) }
            else { Component4::C3(self.3) }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            match component {
                Component4::C0(_) => 0, Component4::C1(_) => 1,
                Component4::C2(_) => 2, Component4::C3(_) => 3,
            }
        }
    }

    impl<H: Event> EventSpecImpl for Coproduct<H, CNil> {
        open spec fn obeys_projection_spec() -> bool { H::obeys_projection_spec() }
        // CNil has no native values; its logical extension uses one coherent head projection.
        open spec fn component_spec(self, index: int) -> Self::Component {
            match self {
                Coproduct::Inl(head) => head.component_spec(index),
                Coproduct::Inr(_) => arbitrary::<H>().component_spec(index),
            }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            H::coordinate_spec(component)
        }
    }

    impl<H, T, Rest> EventSpecImpl for Coproduct<H, Coproduct<T, Rest>>
    where
        H: Event,
        Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>,
    {
        open spec fn obeys_projection_spec() -> bool {
            H::obeys_projection_spec() && <Coproduct<T, Rest> as EventSpec>::obeys_projection_spec()
        }
        open spec fn component_spec(self, index: int) -> Self::Component {
            match self {
                Coproduct::Inl(head) => head.component_spec(index),
                Coproduct::Inr(tail) => tail.component_spec(index),
            }
        }
        open spec fn coordinate_spec(component: Self::Component) -> nat {
            H::coordinate_spec(component)
        }
    }
}
