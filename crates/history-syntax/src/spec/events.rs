//! R1: real events, coordinate projections, and the structural policy vocabulary.
//! The paper's product-event model is represented by a tagged component type.

use crate::Event;
use crate::event::{Arity, MAX_ARITY, sealed};
use crate::{Comparison, Component2, Component3, Component4, RuleMode};
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
    index < arity::<E>() && exists|values: Seq<E::Component>|
        values.len() == count
        && (forall|j: int| 0 <= j < values.len()
            ==> E::coordinate_spec(#[trigger] values[j]) == index)
        && (forall|j: int, k: int| #![trigger values[j], values[k]]
            0 <= j < k < values.len() ==> !values[j].eq_spec(&values[k]))
        && (forall|value: E::Component| #[trigger] E::coordinate_spec(value) == index
            ==> exists|j: int| 0 <= j < values.len() && value.eq_spec(&values[j]))
}

/// Native projections obey their models, tags are correct, and all product tuples are realizable.
pub open spec fn event_laws<E: Event>() -> bool {
    1 <= arity::<E>() <= crate::MAX_ARITY && E::obeys_projection_spec()
        && projection_laws::<E>() && surjectivity::<E>()
}

/// Built-in two-coordinate tuples realize every correctly tagged product tuple.
pub proof fn lemma_tuple2_event_laws<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash>()
    ensures event_laws::<(A, B)>(),
{
    assert forall|event: (A, B)| #[trigger] well_tagged::<(A, B)>(event_view(event)) by {
        assert(event_view(event) =~= seq![Component2::C0(event.0), Component2::C1(event.1)]);
    }
    assert forall|values: Seq<Component2<A, B>>| #[trigger] well_tagged::<(A, B)>(values)
        implies exists|event: (A, B)| #[trigger] event_view(event) == values by {
        assert(values[0] is C0);
        assert(values[1] is C1);
        let a = match values[0] { Component2::C0(value) => value, _ => arbitrary() };
        let b = match values[1] { Component2::C1(value) => value, _ => arbitrary() };
        assert(event_view((a, b)) =~= values);
    }
}

/// Built-in three-coordinate tuples realize every correctly tagged product tuple.
pub proof fn lemma_tuple3_event_laws<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash>()
    ensures event_laws::<(A, B, C)>(),
{
    assert forall|event: (A, B, C)| #[trigger] well_tagged::<(A, B, C)>(event_view(event)) by {
        assert(event_view(event) =~= seq![Component3::C0(event.0), Component3::C1(event.1), Component3::C2(event.2)]);
    }
    assert forall|values: Seq<Component3<A, B, C>>| #[trigger] well_tagged::<(A, B, C)>(values)
        implies exists|event: (A, B, C)| #[trigger] event_view(event) == values by {
        assert(values[0] is C0);
        assert(values[1] is C1);
        assert(values[2] is C2);
        let a = match values[0] { Component3::C0(value) => value, _ => arbitrary() };
        let b = match values[1] { Component3::C1(value) => value, _ => arbitrary() };
        let c = match values[2] { Component3::C2(value) => value, _ => arbitrary() };
        assert(event_view((a, b, c)) =~= values);
    }
}

/// Built-in four-coordinate tuples realize every correctly tagged product tuple.
pub proof fn lemma_tuple4_event_laws<A: Copy + Debug + Eq + Hash, B: Copy + Debug + Eq + Hash,
    C: Copy + Debug + Eq + Hash, D: Copy + Debug + Eq + Hash>()
    ensures event_laws::<(A, B, C, D)>(),
{
    assert forall|event: (A, B, C, D)| #[trigger] well_tagged::<(A, B, C, D)>(event_view(event)) by {
        assert(event_view(event) =~= seq![Component4::C0(event.0), Component4::C1(event.1),
            Component4::C2(event.2), Component4::C3(event.3)]);
    }
    assert forall|values: Seq<Component4<A, B, C, D>>| #[trigger] well_tagged::<(A, B, C, D)>(values)
        implies exists|event: (A, B, C, D)| #[trigger] event_view(event) == values by {
        assert(values[0] is C0);
        assert(values[1] is C1);
        assert(values[2] is C2);
        assert(values[3] is C3);
        let a = match values[0] { Component4::C0(value) => value, _ => arbitrary() };
        let b = match values[1] { Component4::C1(value) => value, _ => arbitrary() };
        let c = match values[2] { Component4::C2(value) => value, _ => arbitrary() };
        let d = match values[3] { Component4::C3(value) => value, _ => arbitrary() };
        assert(event_view((a, b, c, d)) =~= values);
    }
}

/// The final coproduct variant inherits realization of every tagged tuple from its event arm.
pub proof fn lemma_coproduct_last_surjectivity<H: Event>()
    requires surjectivity::<H>(),
    ensures surjectivity::<Coproduct<H, CNil>>(),
{
    assert forall|values: Seq<H::Component>|
        #[trigger] well_tagged::<Coproduct<H, CNil>>(values)
        implies exists|event: Coproduct<H, CNil>| #[trigger] event_view(event) == values by {
        assert(well_tagged::<H>(values));
        let head = choose|head: H| #[trigger] event_view(head) == values;
        assert(event_view(Coproduct::<H, CNil>::Inl(head)) =~= values);
    }
}

/// A terminal coproduct inherits lawful projections and product realization from its event arm.
pub proof fn lemma_coproduct_last_event_laws<H: Event>()
    requires event_laws::<H>(),
    ensures event_laws::<Coproduct<H, CNil>>(),
{
    lemma_coproduct_last_surjectivity::<H>();
    assert forall|event: Coproduct<H, CNil>|
        #[trigger] well_tagged::<Coproduct<H, CNil>>(event_view(event)) by {
        let head = match event {
            Coproduct::Inl(head) => head,
            Coproduct::Inr(_) => arbitrary::<H>(),
        };
        assert(well_tagged::<H>(event_view(head)));
        assert(event_view(event) =~= event_view(head));
    }
}

/// A coproduct with shared coordinate types inherits tuple realization from its head event arm.
pub proof fn lemma_coproduct_surjectivity<H: Event, T, Rest>()
    where Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>
    requires surjectivity::<H>(),
    ensures surjectivity::<Coproduct<H, Coproduct<T, Rest>>>(),
{
    assert forall|values: Seq<H::Component>|
        #[trigger] well_tagged::<Coproduct<H, Coproduct<T, Rest>>>(values)
        implies exists|event: Coproduct<H, Coproduct<T, Rest>>| #[trigger] event_view(event) == values by {
        assert(well_tagged::<H>(values));
        let head = choose|head: H| #[trigger] event_view(head) == values;
        assert(event_view(Coproduct::<H, Coproduct<T, Rest>>::Inl(head)) =~= values);
    }
}

/// Shared-coordinate coproducts preserve event laws when both arms agree on component tags.
pub proof fn lemma_coproduct_event_laws<H: Event, T, Rest>()
    where Coproduct<T, Rest>: Event<Component = H::Component, Arity = H::Arity>
    requires
        event_laws::<H>(), event_laws::<Coproduct<T, Rest>>(),
        forall|value: H::Component| #[trigger] H::coordinate_spec(value)
            == <Coproduct<T, Rest> as EventSpec>::coordinate_spec(value),
    ensures event_laws::<Coproduct<H, Coproduct<T, Rest>>>(),
{
    lemma_coproduct_surjectivity::<H, T, Rest>();
    assert forall|event: Coproduct<H, Coproduct<T, Rest>>|
        #[trigger] well_tagged::<Coproduct<H, Coproduct<T, Rest>>>(event_view(event)) by {
        match event {
            Coproduct::Inl(head) => {
                assert(well_tagged::<H>(event_view(head)));
                assert(event_view(event) =~= event_view(head));
            },
            Coproduct::Inr(tail) => {
                assert(well_tagged::<Coproduct<T, Rest>>(event_view(tail)));
                assert(event_view(event) =~= event_view(tail));
            },
        }
    }
}

}
