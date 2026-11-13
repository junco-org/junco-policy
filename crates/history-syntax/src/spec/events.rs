//! R1: real events, coordinate projections, and the structural policy vocabulary.
//! The paper's product-event model is represented by a tagged component type.

use crate::Event;
use crate::event::specs::{AritySpec, EventSpec};
use vstd::prelude::*;

// Track B moves these declarations here and removes their former definitions.
pub use crate::verify::dsl::{AtomView, HeadView, PatternView, RegexView, RuleView, TestView};

verus! {

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


/// Native projections obey their models, tags are correct, and all product tuples are realizable.
pub open spec fn event_laws<E: Event>() -> bool {
    1 <= arity::<E>() <= crate::MAX_ARITY && E::obeys_projection_spec()
        && projection_laws::<E>() && surjectivity::<E>()
}

}
