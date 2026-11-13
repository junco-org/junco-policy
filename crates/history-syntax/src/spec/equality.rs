//! Equality specifications for derived tagged-component values, also used by coproduct events.

use crate::event::{Component2, Component3, Component4};
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

verus! {

impl<A, B> PartialEqSpecImpl for Component2<A, B>
where
    A: PartialEq + PartialEqSpec,
    B: PartialEq + PartialEqSpec,
{
    open spec fn obeys_eq_spec() -> bool {
        A::obeys_eq_spec() && B::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Component2::C0(left), Component2::C0(right)) => left.eq_spec(&right),
            (Component2::C1(left), Component2::C1(right)) => left.eq_spec(&right),
            _ => false,
        }
    }
}

impl<A, B, C> PartialEqSpecImpl for Component3<A, B, C>
where
    A: PartialEq + PartialEqSpec,
    B: PartialEq + PartialEqSpec,
    C: PartialEq + PartialEqSpec,
{
    open spec fn obeys_eq_spec() -> bool {
        A::obeys_eq_spec() && B::obeys_eq_spec() && C::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Component3::C0(left), Component3::C0(right)) => left.eq_spec(&right),
            (Component3::C1(left), Component3::C1(right)) => left.eq_spec(&right),
            (Component3::C2(left), Component3::C2(right)) => left.eq_spec(&right),
            _ => false,
        }
    }
}

impl<A, B, C, D> PartialEqSpecImpl for Component4<A, B, C, D>
where
    A: PartialEq + PartialEqSpec,
    B: PartialEq + PartialEqSpec,
    C: PartialEq + PartialEqSpec,
    D: PartialEq + PartialEqSpec,
{
    open spec fn obeys_eq_spec() -> bool {
        A::obeys_eq_spec() && B::obeys_eq_spec() && C::obeys_eq_spec() && D::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Component4::C0(left), Component4::C0(right)) => left.eq_spec(&right),
            (Component4::C1(left), Component4::C1(right)) => left.eq_spec(&right),
            (Component4::C2(left), Component4::C2(right)) => left.eq_spec(&right),
            (Component4::C3(left), Component4::C3(right)) => left.eq_spec(&right),
            _ => false,
        }
    }
}

/// Exposes the structural equality model used by the derived native three-coordinate key.
pub proof fn lemma_component3_equality<A: PartialEq, B: PartialEq, C: PartialEq>(
    left: Component3<A, B, C>, right: Component3<A, B, C>,
)
    ensures <Component3<A, B, C> as PartialEqSpec>::eq_spec(&left, &right) == match (left, right) {
        (Component3::C0(a), Component3::C0(b)) => a.eq_spec(&b),
        (Component3::C1(a), Component3::C1(b)) => a.eq_spec(&b),
        (Component3::C2(a), Component3::C2(b)) => a.eq_spec(&b),
        _ => false,
    },
{}

}
