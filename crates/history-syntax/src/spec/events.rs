//! R1: real events, coordinate projections, and the structural policy vocabulary.
//! The paper's product-event model is represented by a tagged component type.

use crate::Event;
use crate::event::{Arity, MAX_ARITY, sealed};
use crate::{Comparison, RuleMode};
use alloc::boxed::Box;
use core::fmt::Debug;
use core::hash::Hash;
use frunk_core::coproduct::{CNil, Coproduct};
use vstd::prelude::*;

verus! {
    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(AritySpec via AritySpecImpl)]
    pub trait ExArity: sealed::Sealed {
        type ExternalTraitSpecificationFor: Arity;
        spec fn value_spec() -> nat;
        fn value() -> (result: usize)
            ensures 1 <= result <= MAX_ARITY, result == Self::value_spec();
    }

    // Transparent specifications expose exactly the Frunk enum variants to body proofs.
    #[verifier::external_type_specification]
    #[verifier::accept_recursive_types(H)]
    #[verifier::reject_recursive_types_in_ground_variants(T)]
    pub struct ExCoproduct<H, T>(Coproduct<H, T>);

    #[verifier::external_type_specification]
    // Like vstd's Infallible: the pinned verifier cannot represent a zero-variant datatype.
    #[verifier::external_body]
    pub struct ExCNil(CNil);

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(EventSpec via EventSpecImpl)]
    pub trait ExEvent: Copy + Debug + Eq + Hash {
        type ExternalTraitSpecificationFor: Event;
        type Component: Copy + Debug + Eq + Hash;
        type Arity: Arity;

        spec fn obeys_projection_spec() -> bool;
        spec fn component_spec(self, index: int) -> Self::Component;
        spec fn coordinate_spec(component: Self::Component) -> nat;

        fn component(self, index: usize) -> (result: Self::Component)
            ensures Self::obeys_projection_spec() ==> result == self.component_spec(index as int);
        fn coordinate(component: Self::Component) -> (result: usize)
            ensures Self::obeys_projection_spec() ==>
                result as nat == Self::coordinate_spec(component)
                && result < Self::Arity::value_spec();
        fn coordinate_cardinality(index: usize) -> (result: Option<usize>)
            ensures result matches Some(count) ==> (Self::obeys_projection_spec()
                ==> finite_coordinate_values::<Self::Component>(
                    |value: Self::Component| Self::coordinate_spec(value),
                    Self::Arity::value_spec(), index as nat, count as nat));
    }
/// A head coordinate is either a typed constant or a named candidate binding (Section 3).
pub enum PatternView<T> {
    Constant(T),
    Variable(Seq<char>),
}

/// Coordinate-ordered head patterns (Section 3).
pub type HeadView<C> = Seq<PatternView<C>>;

/// A component-local tail atom and its source pattern (Section 3).
pub struct AtomView<C> {
    pub component: nat,
    pub pattern: PatternView<C>,
}

/// Boolean tail tests over component-local atoms (Section 3).
pub enum TestView<C> {
    True,
    False,
    Atom { comparison: Comparison, pattern: AtomView<C> },
    And(Seq<TestView<C>>),
    Or(Seq<TestView<C>>),
}

/// The same algebra as the numeric history model, over concrete component values.
pub enum RegexView<C> {
    Empty, All, Epsilon,
    Test(TestView<C>),
    Union(Seq<RegexView<C>>),
    Concat(Seq<RegexView<C>>),
    Star(Box<RegexView<C>>),
    Intersect(Seq<RegexView<C>>),
    Not(Box<RegexView<C>>),
}

/// The source rule mode, head and tail, projected without numeric encoding (Section 3).
pub struct RuleView<C> {
    pub mode: RuleMode,
    pub head: HeadView<C>,
    pub tail: RegexView<C>,
}

/// Number of coordinates of an event (paper Section 3, product events).
pub open spec fn arity<E: Event>() -> nat { E::Arity::value_spec() }

/// Coordinate values of one real event, in coordinate order (paper Section 3).
pub open spec fn event_view<E: Event>(event: E) -> Seq<E::Component> {
    Seq::new(arity::<E>(), |i: int| event.component_spec(i))
}

/// A tuple has exactly the event arity and the correct tag at each coordinate.
pub open spec fn well_tagged<E: Event>(values: Seq<E::Component>) -> bool {
    values.len() == arity::<E>() && forall|i: int| 0 <= i < values.len()
        ==> E::coordinate_spec(#[trigger] values[i]) == i
}

/// Every real event projects to a well-tagged tuple (paper Section 3).
pub open spec fn projection_laws<E: Event>() -> bool {
    forall|event: E| #[trigger] well_tagged::<E>(event_view(event))
}

/// Every well-tagged tuple represents a real event, not merely a symbolic tuple.
pub open spec fn surjectivity<E: Event>() -> bool {
    forall|values: Seq<E::Component>| #[trigger] well_tagged::<E>(values)
        ==> exists|event: E| #[trigger] event_view(event) == values
}

/// The tagged values at one coordinate have exactly `count` equality classes (Section 3).
pub open spec fn finite_coordinate<E: Event>(index: nat, count: nat) -> bool {
    finite_coordinate_values::<E::Component>(|value: E::Component| E::coordinate_spec(value),
        arity::<E>(), index, count)
}

/// Coordinate cardinality stated over a tagged carrier, usable at the external trait boundary.
pub open spec fn finite_coordinate_values<C: PartialEq>(tag: spec_fn(C) -> nat,
    arity: nat, index: nat, count: nat) -> bool {
    index < arity && exists|values: Seq<C>|
        values.len() == count
        && (forall|j: int| 0 <= j < values.len()
            ==> tag(#[trigger] values[j]) == index)
        && (forall|j: int, k: int| #![trigger values[j], values[k]]
            0 <= j < k < values.len() ==> !values[j].eq_spec(&values[k]))
        && (forall|value: C| #[trigger] tag(value) == index
            ==> exists|j: int| 0 <= j < values.len() && value.eq_spec(&values[j]))
}

/// Native projections obey their models, tags are correct, and all product tuples are realizable.
pub open spec fn event_laws<E: Event>() -> bool {
    1 <= arity::<E>() <= crate::MAX_ARITY && E::obeys_projection_spec()
        && projection_laws::<E>() && surjectivity::<E>()
}

}
