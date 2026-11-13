//! Structural and semantic clients of the actual iterative owned-source lowering.

use crate::error::CompileError;
use crate::flat::verify as flat;
use crate::flat::{FlatHead, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::flatten::Work;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use crate::verify::dsl;
use history_syntax::Event;
use history_syntax::spec::events::{AtomView, HeadView, PatternView, RegexView, TestView};
use history_syntax::spec::events::{EventSpec, arity};
use history_syntax::syntax::{
    Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
type SourceHead<E> = HeadView<<E as Event>::Component>;
type SourceTest<E> = TestView<<E as Event>::Component>;
type SourceRegex<E> = RegexView<<E as Event>::Component>;
type SourceEvent<E> = Seq<<E as Event>::Component>;

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Tagged component equality is already the event type's own equality contract.
pub open spec fn component_eq<E: Event>(_field: Component, left: E::Component, right: E::Component) -> bool {
    left.eq_spec(&right)
}

pub open spec fn component_equality<E: Event>() -> spec_fn(Component, E::Component, E::Component) -> bool {
    |field: Component, left: E::Component, right: E::Component| component_eq::<E>(field, left, right)
}

/// A typed constant belongs only to its declared product coordinate.
pub open spec fn component_domain<E: Event>() -> crate::verify::encoding::Domain<E::Component> {
    |field: Component, value: E::Component| E::coordinate_spec(value) == field.0 as nat
}

pub open spec fn head_coordinates_wf<E: Event>(head: SourceHead<E>) -> bool {
    head.len() == arity::<E>() && forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
        PatternView::Constant(value) => E::coordinate_spec(value) == i,
        _ => true,
    }
}

pub open spec fn atom_coordinates_wf<E: Event>(atom: AtomView<E::Component>) -> bool {
    atom.component < arity::<E>() && match atom.pattern {
        PatternView::Constant(value) => E::coordinate_spec(value) == atom.component,
        _ => true,
    }
}

pub open spec fn head_slot_represents<C>(flat: FlatHead<C>, source: PatternView<C>) -> bool {
    match (flat, source) {
        (FlatHead::Constant(a), PatternView::Constant(b)) => a == b,
        (FlatHead::Bind, PatternView::Variable(_)) => true,
        _ => false,
    }
}

pub open spec fn head_represents<E: Event>(flat: Seq<FlatHead<E::Component>>, head: SourceHead<E>) -> bool {
    flat.len() == head.len() && head.len() == arity::<E>()
        && 1 <= head.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < head.len() ==> head_slot_represents(#[trigger] flat[i], head[i])
}

pub open spec fn scope_matches<E: Event>(scope: VariableScope<'_>, head: SourceHead<E>) -> bool {
    scope.wf() && scope.arity_spec() == head.len() && head.len() == arity::<E>()
        && 1 <= head.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < head.len() ==> match scope.name_spec(Component(i as u8)) {
            Some(name) => dsl::pattern_name(#[trigger] head[i]) == Some(name@),
            None => dsl::pattern_name(#[trigger] head[i]) is None,
        }
}

pub open spec fn atom_term_represents<E: Event>(field: Component, term: FlatTerm<E::Component>,
    atom: AtomView<E::Component>, head: SourceHead<E>) -> bool
{
    field.0 as nat == atom.component && atom.component < head.len() && match (term, atom.pattern) {
        (FlatTerm::Constant(a), PatternView::Constant(b)) => a == b,
        (FlatTerm::Variable(bound), PatternView::Variable(name)) => bound == field
            && dsl::pattern_name(head[atom.component as int]) == Some(name),
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn test_operands<C>(node: FlatTest<C>) -> Seq<u32> {
    match node { FlatTest::And(ids) | FlatTest::Or(ids) => ids@, _ => Seq::empty() }
}

#[verifier::opaque]
pub open spec fn regex_operands(node: FlatRegex) -> Seq<u32> {
    match node { FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@, _ => Seq::empty() }
}

pub proof fn lemma_test_operands<C>(node: FlatTest<C>)
    ensures test_operands(node) == match node { FlatTest::And(ids) | FlatTest::Or(ids) => ids@, _ => Seq::empty() },
{ reveal(test_operands); }

pub proof fn lemma_regex_operands(node: FlatRegex)
    ensures regex_operands(node) == match node {
        FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@, _ => Seq::empty(),
    },
{ reveal(regex_operands); }

/// This is a structural relation, not the semantic equivalence that the bridge must prove.
pub open spec fn test_represents<E: Event>(tests: Seq<FlatTest<E::Component>>, id: nat,
    source: SourceTest<E>, head: SourceHead<E>) -> bool
    decreases source,
{
    id < tests.len() && dsl::test_scoped(source, head) && match source {
        TestView::True => tests[id as int] == FlatTest::Bool(true),
        TestView::False => tests[id as int] == FlatTest::Bool(false),
        TestView::Atom { comparison, pattern } => match tests[id as int] {
            FlatTest::Atom { field, term, positive } => positive == (comparison is Eq)
                && atom_term_represents::<E>(field, term, pattern, head),
            _ => false,
        },
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            ((source is And && tests[id as int] is And) || (source is Or && tests[id as int] is Or))
                && children.len() == ids.len() && flat::references_before(ids, id)
                && forall|i: int| #![trigger ids[i]] 0 <= i < children.len() ==>
                    test_represents::<E>(tests, ids[i] as nat, children[i], head)
        },
    }
}

pub open spec fn regex_represents<E: Event>(tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>) -> bool
    decreases source,
{
    id < regexes.len() && dsl::regex_scoped(source, head) && match source {
        RegexView::Empty => regexes[id as int] is Empty,
        RegexView::All => regexes[id as int] is All,
        RegexView::Epsilon => regexes[id as int] is Epsilon,
        RegexView::Test(test) => match regexes[id as int] {
            FlatRegex::Test(test_id) => test_represents::<E>(tests, test_id as nat, test, head),
            _ => false,
        },
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            ((source is Concat && regexes[id as int] is Concat)
                || (source is Union && regexes[id as int] is Union)
                || (source is Intersect && regexes[id as int] is Intersect))
                && children.len() == ids.len() && flat::references_before(ids, id)
                && forall|i: int| #![trigger ids[i]] 0 <= i < children.len() ==>
                    regex_represents::<E>(tests, regexes, ids[i] as nat, children[i], head)
        },
        RegexView::Star(child) | RegexView::Not(child) =>
            ((source is Star && regexes[id as int] is Star) || (source is Not && regexes[id as int] is Complement))
            && match regexes[id as int] {
                FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) => child_id < id
                    && regex_represents::<E>(tests, regexes, child_id as nat, *child, head),
                _ => false,
            },
    }
}

pub open spec fn flattened<E: Event>(rule: Rule<E>, flat_rule: FlatRule<E::Component>) -> bool {
    flat_rule.mode == rule.mode && flat::structural_wf(flat_rule.source)
        && dsl::head_scoped(rule.head@) && head_represents::<E>(flat_rule.source.head@, rule.head@)
        && regex_represents::<E>(flat_rule.source.tests@, flat_rule.source.regexes@,
            flat_rule.source.root as nat, rule.tail@, rule.head@)
}

/// Constants of a reachable flat test are contained in the per-coordinate known sets.
pub open spec fn test_constants_bounded<C>(tests: Seq<FlatTest<C>>, id: nat, known: Seq<Set<C>>) -> bool
    decreases id,
{
    id < tests.len() && match tests[id as int] {
        FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } =>
            (field.0 as nat) < known.len() && known[field.0 as int].contains(value),
        FlatTest::And(children) => flat::references_before(children@, id)
            && forall|i: int| 0 <= i < children@.len() ==>
                test_constants_bounded(tests, #[trigger] children@[i] as nat, known),
        FlatTest::Or(children) => flat::references_before(children@, id)
            && forall|i: int| 0 <= i < children@.len() ==>
                test_constants_bounded(tests, #[trigger] children@[i] as nat, known),
        _ => true,
    }
}

/// Only nodes reachable from the regex root contribute constants to the source rule.
pub open spec fn regex_constants_bounded<C>(tests: Seq<FlatTest<C>>, regexes: Seq<FlatRegex>,
    id: nat, known: Seq<Set<C>>) -> bool
    decreases id,
{
    id < regexes.len() && match regexes[id as int] {
        FlatRegex::Test(test) => test_constants_bounded(tests, test as nat, known),
        FlatRegex::Union(children) => flat::references_before(children@, id)
            && forall|i: int| 0 <= i < children@.len() ==>
                regex_constants_bounded(tests, regexes, #[trigger] children@[i] as nat, known),
        FlatRegex::Concat(children) => flat::references_before(children@, id)
            && forall|i: int| 0 <= i < children@.len() ==>
                regex_constants_bounded(tests, regexes, #[trigger] children@[i] as nat, known),
        FlatRegex::Intersect(children) => flat::references_before(children@, id)
            && forall|i: int| 0 <= i < children@.len() ==>
                regex_constants_bounded(tests, regexes, #[trigger] children@[i] as nat, known),
        FlatRegex::Star(child) | FlatRegex::Complement(child) => child < id
            && regex_constants_bounded(tests, regexes, child as nat, known),
        _ => true,
    }
}

/// Source test constants bound the reachable nodes of their actual flattened representation.
pub proof fn lemma_test_constants_bounded<E: Event>(
    tests: Seq<FlatTest<E::Component>>, id: nat, source: SourceTest<E>,
    head: SourceHead<E>, known: Seq<Set<E::Component>>,
)
    requires test_represents::<E>(tests, id, source, head), known.len() == head.len(),
        forall|j: int| 0 <= j < known.len() ==>
            crate::spec::questions::test_constants(source, head.len())[j].subset_of(known[j]),
    ensures test_constants_bounded(tests, id, known),
    decreases source,
{
    reveal_with_fuel(test_represents, 2);
    reveal_with_fuel(test_constants_bounded, 2);
    lemma_test_operands(tests[id as int]);
    match source {
        TestView::Atom { pattern, .. } => {
            if let FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } = tests[id as int] {
                crate::spec::questions::lemma_test_constants_index(source, head.len(), field.0 as int);
                assert(known[field.0 as int].contains(value));
            }
        },
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                test_constants_bounded(tests, ids[i] as nat, known) by {
                assert forall|j: int| 0 <= j < known.len() implies
                    crate::spec::questions::test_constants(children[i], head.len())[j].subset_of(known[j]) by {
                    crate::spec::questions::lemma_test_constants_index(source, head.len(), j);
                    let sets = Seq::new(children.len(), |k: int| if 0 <= k < children.len() {
                        crate::spec::questions::test_constants(children[k], head.len())[j]
                    } else { Set::empty() });
                    crate::spec::questions::lemma_constants_union(sets, i);
                }
                lemma_test_constants_bounded::<E>(tests, ids[i] as nat, children[i], head, known);
            }
        },
        _ => {},
    }
}

/// Source regex constants bound every test reachable through its flat DAG root.
pub proof fn lemma_regex_constants_bounded<E: Event>(
    tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>, known: Seq<Set<E::Component>>,
)
    requires regex_represents::<E>(tests, regexes, id, source, head), known.len() == head.len(),
        forall|j: int| 0 <= j < known.len() ==>
            crate::spec::questions::regex_constants(source, head.len())[j].subset_of(known[j]),
    ensures regex_constants_bounded(tests, regexes, id, known),
    decreases source,
{
    reveal_with_fuel(regex_represents, 2);
    reveal_with_fuel(regex_constants_bounded, 2);
    lemma_regex_operands(regexes[id as int]);
    match source {
        RegexView::Test(test) => {
            if let FlatRegex::Test(test_id) = regexes[id as int] {
                assert forall|j: int| 0 <= j < known.len() implies
                    crate::spec::questions::test_constants(test, head.len())[j].subset_of(known[j]) by {
                    crate::spec::questions::lemma_regex_constants_index(source, head.len(), j);
                }
                lemma_test_constants_bounded::<E>(tests, test_id as nat, test, head, known);
            }
        },
        RegexView::Union(children) | RegexView::Concat(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                regex_constants_bounded(tests, regexes, ids[i] as nat, known) by {
                assert forall|j: int| 0 <= j < known.len() implies
                    crate::spec::questions::regex_constants(children[i], head.len())[j].subset_of(known[j]) by {
                    crate::spec::questions::lemma_regex_constants_index(source, head.len(), j);
                    let sets = Seq::new(children.len(), |k: int| if 0 <= k < children.len() {
                        crate::spec::questions::regex_constants(children[k], head.len())[j]
                    } else { Set::empty() });
                    crate::spec::questions::lemma_constants_union(sets, i);
                }
                lemma_regex_constants_bounded::<E>(tests, regexes, ids[i] as nat, children[i], head, known);
            }
        },
        RegexView::Star(child) | RegexView::Not(child) => {
            assert forall|j: int| 0 <= j < known.len() implies
                crate::spec::questions::regex_constants(*child, head.len())[j].subset_of(known[j]) by {
                crate::spec::questions::lemma_regex_constants_index(source, head.len(), j);
            }
            match regexes[id as int] {
                FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) =>
                    lemma_regex_constants_bounded::<E>(tests, regexes, child_id as nat, *child, head, known),
                _ => {},
            }
        },
        _ => {},
    }
}

/// Executable lowering cannot introduce a reachable constant absent from the source rule.
pub proof fn lemma_flattened_constants<E: Event>(rule: Rule<E>, lowered: FlatRule<E::Component>)
    requires flattened::<E>(rule, lowered),
    ensures
        (forall|i: int| 0 <= i < lowered.source.head@.len() ==>
            match #[trigger] lowered.source.head@[i] {
                FlatHead::Constant(value) => crate::spec::questions::rule_constants(rule@)[i].contains(value),
                _ => true,
            }),
        regex_constants_bounded(lowered.source.tests@, lowered.source.regexes@,
            lowered.source.root as nat, crate::spec::questions::rule_constants(rule@)),
{
    let known = crate::spec::questions::rule_constants(rule@);
    assert forall|i: int| 0 <= i < lowered.source.head@.len() implies
        match #[trigger] lowered.source.head@[i] {
            FlatHead::Constant(value) => known[i].contains(value),
            _ => true,
        } by {
        assert(head_slot_represents(lowered.source.head@[i], rule.head@[i]));
    }
    assert forall|j: int| 0 <= j < known.len() implies
        crate::spec::questions::regex_constants(rule.tail@, rule.head@.len())[j].subset_of(known[j]) by {}
    lemma_regex_constants_bounded::<E>(lowered.source.tests@, lowered.source.regexes@,
        lowered.source.root as nat, rule.tail@, rule.head@, known);
}

/// The executable test table's coordinate validation transfers to its source tree.
pub proof fn lemma_represented_test_wf<E: Event>(
    tests: Seq<FlatTest<E::Component>>, id: nat, source: SourceTest<E>, head: SourceHead<E>,
)
    requires test_represents::<E>(tests, id, source, head),
        head.len() == arity::<E>(),
        forall|i: int| 0 <= i < tests.len() ==>
            crate::verify::encoding::test_in_domain(tests[i], component_domain::<E>()),
    ensures crate::spec::semantics::test_wf::<E>(source, head),
    decreases source,
{
    reveal_with_fuel(test_represents, 2);
    reveal_with_fuel(crate::spec::semantics::test_wf, 2);
    match source {
        TestView::Atom { pattern, .. } => {
            if let FlatTest::Atom { field, term, .. } = tests[id as int] {
                match (term, pattern.pattern) {
                    (FlatTerm::Constant(_), PatternView::Constant(_)) => {},
                    (FlatTerm::Variable(_), PatternView::Variable(_)) => {
                        match head[pattern.component as int] {
                            PatternView::Variable(_) => {},
                            PatternView::Constant(_) => {},
                        }
                    },
                    _ => {},
                }
            }
        },
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                crate::spec::semantics::test_wf::<E>(children[i], head) by {
                lemma_represented_test_wf::<E>(tests, ids[i] as nat, children[i], head);
            }
        },
        _ => {},
    }
}

/// Transfer coordinate validation and scope through the source-regex representation.
pub proof fn lemma_represented_regex_wf<E: Event>(
    tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>,
)
    requires regex_represents::<E>(tests, regexes, id, source, head),
        head.len() == arity::<E>(),
        forall|i: int| 0 <= i < tests.len() ==>
            crate::verify::encoding::test_in_domain(tests[i], component_domain::<E>()),
    ensures crate::spec::semantics::regex_wf::<E>(source, head),
    decreases source,
{
    reveal_with_fuel(regex_represents, 2);
    reveal_with_fuel(crate::spec::semantics::regex_wf, 2);
    match source {
        RegexView::Test(test) => {
            if let FlatRegex::Test(test_id) = regexes[id as int] {
                lemma_represented_test_wf::<E>(tests, test_id as nat, test, head);
            }
        },
        RegexView::Union(children) | RegexView::Concat(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                crate::spec::semantics::regex_wf::<E>(children[i], head) by {
                lemma_represented_regex_wf::<E>(tests, regexes, ids[i] as nat, children[i], head);
            }
        },
        RegexView::Star(child) | RegexView::Not(child) => {
            match regexes[id as int] {
                FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) =>
                    lemma_represented_regex_wf::<E>(tests, regexes, child_id as nat, *child, head),
                _ => {},
            }
        },
        _ => {},
    }
}

/// A successful structural lowering plus validated constants establishes the public rule invariant.
pub proof fn lemma_flattened_rule_wf<E: Event>(rule: Rule<E>, lowered: FlatRule<E::Component>)
    requires flattened::<E>(rule, lowered),
        crate::verify::encoding::constants_in_domain(lowered.source, component_domain::<E>()),
    ensures crate::spec::semantics::rule_wf::<E>(rule),
{
    let head = rule.head@;
    assert forall|i: int| 0 <= i < head.len() implies match #[trigger] head[i] {
        PatternView::Constant(value) => E::coordinate_spec(value) == i,
        PatternView::Variable(_) => true,
    } by {
        assert(head_slot_represents(lowered.source.head@[i], head[i]));
        assert(crate::verify::encoding::head_in_domain(lowered.source.head@[i],
            crate::verify::encoding::field_at(i), component_domain::<E>()));
        assert((i as u8) as nat == i);
    }
    assert forall|i: int, j: int| 0 <= i < j < head.len() implies
        match (#[trigger] head[i], #[trigger] head[j]) {
            (PatternView::Variable(a), PatternView::Variable(b)) => a != b,
            _ => true,
        } by {
        assert(dsl::distinct_names(head[i], head[j]));
    }
    lemma_represented_regex_wf::<E>(lowered.source.tests@, lowered.source.regexes@,
        lowered.source.root as nat, rule.tail@, head);
}

/// Canonical head well-formedness entails the lowering scope and coordinate predicates.
pub proof fn lemma_head_wf_lowering<E: Event>(head: SourceHead<E>)
    requires crate::spec::semantics::head_wf::<E>(head),
    ensures dsl::head_scoped(head), head_coordinates_wf::<E>(head),
{
    assert forall|i: int, j: int| 0 <= i < j < head.len() implies
        dsl::distinct_names(#[trigger] head[i], #[trigger] head[j]) by {
        match (head[i], head[j]) {
            (PatternView::Variable(_), PatternView::Variable(_)) => {},
            _ => {},
        }
    }
}

/// Canonical test well-formedness entails the scoping needed by the lowering worklist.
pub proof fn lemma_test_wf_scoped<E: Event>(test: SourceTest<E>, head: SourceHead<E>)
    requires crate::spec::semantics::test_wf::<E>(test, head),
    ensures dsl::test_scoped(test, head),
    decreases test,
{
    reveal_with_fuel(crate::spec::semantics::test_wf, 2);
    reveal_with_fuel(dsl::test_scoped, 2);
    match test {
        TestView::And(children) | TestView::Or(children) => {
            assert forall|i: int| 0 <= i < children.len() implies dsl::test_scoped(children[i], head) by {
                lemma_test_wf_scoped::<E>(children[i], head);
            }
        },
        _ => {},
    }
}

/// Canonical regex well-formedness entails the worklist's structural scope predicate.
pub proof fn lemma_regex_wf_scoped<E: Event>(regex: SourceRegex<E>, head: SourceHead<E>)
    requires crate::spec::semantics::regex_wf::<E>(regex, head),
    ensures dsl::regex_scoped(regex, head),
    decreases regex,
{
    reveal_with_fuel(crate::spec::semantics::regex_wf, 2);
    reveal_with_fuel(dsl::regex_scoped, 2);
    match regex {
        RegexView::Test(test) => lemma_test_wf_scoped::<E>(test, head),
        RegexView::Union(children) | RegexView::Concat(children) | RegexView::Intersect(children) => {
            assert forall|i: int| 0 <= i < children.len() implies dsl::regex_scoped(children[i], head) by {
                lemma_regex_wf_scoped::<E>(children[i], head);
            }
        },
        RegexView::Star(child) | RegexView::Not(child) => lemma_regex_wf_scoped::<E>(*child, head),
        _ => {},
    }
}


pub open spec fn test_views<E: Event>(children: Seq<TestExpr<E>>) -> Seq<SourceTest<E>> {
    children.map(|i: int, child: TestExpr<E>| child@)
}
pub open spec fn regex_views<E: Event>(children: Seq<RegexExpr<E>>) -> Seq<SourceRegex<E>> {
    children.map(|i: int, child: RegexExpr<E>| child@)
}

pub open spec fn result_stacks<E: Event>(tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>,
    test_ids: Seq<u32>, regex_ids: Seq<u32>, test_sources: Seq<SourceTest<E>>, regex_sources: Seq<SourceRegex<E>>,
    head: SourceHead<E>) -> bool
{
    test_ids.len() == test_sources.len() && regex_ids.len() == regex_sources.len()
        && (forall|i: int| 0 <= i < test_ids.len() ==>
            #[trigger] test_represents::<E>(tests, test_ids[i] as nat, test_sources[i], head))
        && (forall|i: int| 0 <= i < regex_ids.len() ==>
            #[trigger] regex_represents::<E>(tests, regexes, regex_ids[i] as nat, regex_sources[i], head))
}

/// Pending source visits inherit scope; finish frames retain that same source.
#[verifier::opaque]
pub(crate) open spec fn work_scoped<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>) -> bool {
    forall|i: int| 0 <= i < work.len() ==> match #[trigger] work[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    }
}
/// Pending visits and finish frames retain R2 source well-formedness.
#[verifier::opaque]
pub(crate) open spec fn work_wf<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>) -> bool {
    forall|i: int| 0 <= i < work.len() ==> match #[trigger] work[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) =>
            crate::spec::semantics::regex_wf::<E>(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) =>
            crate::spec::semantics::test_wf::<E>(source@, head),
    }
}

pub(crate) proof fn lemma_work_wf_push<'a, E: Event>(work: Seq<Work<'a, E>>,
    task: Work<'a, E>, head: SourceHead<E>)
    requires work_wf::<E>(work, head), match task {
        Work::Regex(source) | Work::FinishRegex(source, _) =>
            crate::spec::semantics::regex_wf::<E>(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) =>
            crate::spec::semantics::test_wf::<E>(source@, head),
    },
    ensures work_wf::<E>(work.push(task), head),
{
    reveal(work_wf);
    assert forall|i: int| 0 <= i < work.push(task).len() implies match #[trigger] work.push(task)[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) =>
            crate::spec::semantics::regex_wf::<E>(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) =>
            crate::spec::semantics::test_wf::<E>(source@, head),
    } by {
        if i < work.len() { assert(work.push(task)[i] == work[i]); }
        else { assert(i == work.len()); }
    }
}

pub(crate) proof fn lemma_work_wf_pop<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>)
    requires work_wf::<E>(work, head), work.len() > 0,
    ensures work_wf::<E>(work.drop_last(), head), match work.last() {
        Work::Regex(source) | Work::FinishRegex(source, _) =>
            crate::spec::semantics::regex_wf::<E>(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) =>
            crate::spec::semantics::test_wf::<E>(source@, head),
    },
{
    reveal(work_wf);
    assert forall|i: int| 0 <= i < work.drop_last().len() implies match #[trigger] work.drop_last()[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) =>
            crate::spec::semantics::regex_wf::<E>(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) =>
            crate::spec::semantics::test_wf::<E>(source@, head),
    } by { assert(work.drop_last()[i] == work[i]); }
}


pub(crate) proof fn lemma_work_scoped_push<'a, E: Event>(work: Seq<Work<'a, E>>,
    task: Work<'a, E>, head: SourceHead<E>)
    requires work_scoped::<E>(work, head), match task {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    },
    ensures work_scoped::<E>(work.push(task), head),
{
    reveal(work_scoped);
    assert forall|i: int| 0 <= i < work.push(task).len() implies match #[trigger] work.push(task)[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    } by {
        if i < work.len() { assert(work.push(task)[i] == work[i]); }
        else { assert(i == work.len()); }
    }
}

pub(crate) proof fn lemma_work_scoped_pop<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>)
    requires work_scoped::<E>(work, head), work.len() > 0,
    ensures work_scoped::<E>(work.drop_last(), head), match work.last() {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    },
{
    reveal(work_scoped);
    assert forall|i: int| 0 <= i < work.drop_last().len() implies match #[trigger] work.drop_last()[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    } by { assert(work.drop_last()[i] == work[i]); }
}

/// Erased continuation interpreter: visits contribute original views; finish frames check order.
/// It neither evaluates policies nor reconstructs any executable source tree.
#[verifier::opaque]
pub(crate) open spec fn run_work<E: Event>(work: Seq<Work<'_, E>>, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    -> Option<(Seq<SourceTest<E>>, Seq<SourceRegex<E>>)>
    decreases work.len(),
{
    if work.len() == 0 { Some((tests, regexes)) }
    else {
        let rest = work.drop_last();
        match work.last() {
            Work::Regex(source) => run_work::<E>(rest, tests, regexes.push(source@)),
            Work::Test(source) => run_work::<E>(rest, tests.push(source@), regexes),
            Work::FinishTest(source, start) => match source@ {
                TestView::And(children) | TestView::Or(children) =>
                    if start <= tests.len() && tests.subrange(start as int, tests.len() as int) == children {
                        run_work::<E>(rest, tests.take(start as int).push(source@), regexes)
                    } else { None },
                _ => None,
            },
            Work::FinishRegex(source, start) => match source@ {
                RegexView::Test(child) =>
                    if tests.len() == start + 1 && tests[start as int] == child {
                        run_work::<E>(rest, tests.take(start as int), regexes.push(source@))
                    } else { None },
                RegexView::Star(child) | RegexView::Not(child) =>
                    if regexes.len() == start + 1 && regexes[start as int] == *child {
                        run_work::<E>(rest, tests, regexes.take(start as int).push(source@))
                    } else { None },
                RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) =>
                    if start <= regexes.len() && regexes.subrange(start as int, regexes.len() as int) == children {
                        run_work::<E>(rest, tests, regexes.take(start as int).push(source@))
                    } else { None },
                _ => None,
            },
        }
    }
}

/// A successful continuation fixes the next frame's operands and successor stacks.
pub(crate) proof fn lemma_run_work_step<E: Event>(work: Seq<Work<'_, E>>,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    requires work.len() > 0, run_work::<E>(work, tests, regexes) is Some,
    ensures match work.last() {
        Work::Regex(source) => run_work::<E>(work.drop_last(), tests, regexes.push(source@))
            == run_work::<E>(work, tests, regexes),
        Work::Test(source) => run_work::<E>(work.drop_last(), tests.push(source@), regexes)
            == run_work::<E>(work, tests, regexes),
        Work::FinishTest(source, start) => match source@ {
            TestView::And(children) | TestView::Or(children) => start <= tests.len()
                && tests.subrange(start as int, tests.len() as int) == children
                && run_work::<E>(work.drop_last(), tests.take(start as int).push(source@), regexes)
                    == run_work::<E>(work, tests, regexes),
            _ => false,
        },
        Work::FinishRegex(source, start) => match source@ {
            RegexView::Test(child) => tests.len() == start + 1 && tests[start as int] == child
                && run_work::<E>(work.drop_last(), tests.take(start as int), regexes.push(source@))
                    == run_work::<E>(work, tests, regexes),
            RegexView::Star(child) | RegexView::Not(child) => regexes.len() == start + 1
                && regexes[start as int] == *child
                && run_work::<E>(work.drop_last(), tests, regexes.take(start as int).push(source@))
                    == run_work::<E>(work, tests, regexes),
            RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) =>
                start <= regexes.len()
                && regexes.subrange(start as int, regexes.len() as int) == children
                && run_work::<E>(work.drop_last(), tests, regexes.take(start as int).push(source@))
                    == run_work::<E>(work, tests, regexes),
            _ => false,
        },
    },
{
    reveal_with_fuel(run_work, 1);
}

pub(crate) proof fn lemma_finish_test<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a TestExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceTest<E>>, head: SourceHead<E>)
    requires start == tests.len(), source@ == TestView::And(children) || source@ == TestView::Or(children),
    ensures run_work::<E>(work.push(Work::FinishTest(source, start)), tests + children, regexes)
        == run_work::<E>(work, tests.push(source@), regexes),
        work_scoped::<E>(work, head) && dsl::test_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishTest(source, start)), head)
            && (forall|i: int| 0 <= i < children.len() ==> dsl::test_scoped(#[trigger] children[i], head)),
{
    hide(dsl::test_scoped);
    if work_scoped::<E>(work, head) && dsl::test_scoped(source@, head) {
        assert(forall|i: int| 0 <= i < children.len() ==> dsl::test_scoped(#[trigger] children[i], head)) by {
            reveal_with_fuel(dsl::test_scoped, 1);
        }
        lemma_work_scoped_push::<E>(work, Work::FinishTest(source, start), head);
    }
    let operands = tests + children;
    assert(operands.subrange(start as int, operands.len() as int) =~= children);
    assert(operands.take(start as int) =~= tests);
    assert(work.push(Work::FinishTest(source, start)).drop_last() =~= work);
    reveal_with_fuel(run_work, 2);
}

pub(crate) proof fn lemma_visit_test_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a TestExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, head: SourceHead<E>)
    requires start == tests.len(), source@ == RegexView::Test(child@),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), head),
{
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        reveal_with_fuel(dsl::regex_scoped, 1);
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
        lemma_work_scoped_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Test(child), head);
    }
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Test(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(tests.push(child@).take(start as int) =~= tests);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_visit_unary_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a RegexExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, head: SourceHead<E>)
    requires start == regexes.len(), source@ == RegexView::Star(alloc::boxed::Box::new(child@))
        || source@ == RegexView::Not(alloc::boxed::Box::new(child@)),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), head),
{
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        reveal_with_fuel(dsl::regex_scoped, 1);
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
        lemma_work_scoped_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Regex(child), head);
    }
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Regex(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(regexes.push(child@).take(start as int) =~= regexes);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_finish_many_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceRegex<E>>, head: SourceHead<E>)
    requires start == regexes.len(), source@ == RegexView::Concat(children)
        || source@ == RegexView::Union(children) || source@ == RegexView::Intersect(children),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)), tests, regexes + children)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)), head)
            && (forall|i: int| 0 <= i < children.len() ==> dsl::regex_scoped(#[trigger] children[i], head)),
{
    hide(dsl::regex_scoped);
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        assert(forall|i: int| 0 <= i < children.len() ==> dsl::regex_scoped(#[trigger] children[i], head)) by {
            reveal_with_fuel(dsl::regex_scoped, 1);
        }
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
    }
    let operands = regexes + children;
    assert(operands.subrange(start as int, operands.len() as int) =~= children);
    assert(operands.take(start as int) =~= regexes);
    assert(work.push(Work::FinishRegex(source, start)).drop_last() =~= work);
    reveal_with_fuel(run_work, 2);
}

pub open spec fn test_cost<E: Event>(test: SourceTest<E>) -> nat
    decreases test,
{
    match test {
        TestView::And(children) | TestView::Or(children) => 2 + test_forest_cost::<E>(children),
        _ => 1,
    }
}
pub open spec fn test_forest_cost<E: Event>(tests: Seq<SourceTest<E>>) -> nat
    decreases tests,
{
    if tests.len() == 0 { 0 } else { test_forest_cost::<E>(tests.drop_last()) + test_cost::<E>(tests.last()) }
}
pub open spec fn regex_cost<E: Event>(regex: SourceRegex<E>) -> nat
    decreases regex,
{
    match regex {
        RegexView::Test(test) => 2 + test_cost::<E>(test),
        RegexView::Star(child) | RegexView::Not(child) => 2 + regex_cost::<E>(*child),
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => 2 + regex_forest_cost::<E>(children),
        _ => 1,
    }
}
pub open spec fn regex_forest_cost<E: Event>(regexes: Seq<SourceRegex<E>>) -> nat
    decreases regexes,
{
    if regexes.len() == 0 { 0 } else { regex_forest_cost::<E>(regexes.drop_last()) + regex_cost::<E>(regexes.last()) }
}
pub(crate) open spec fn work_cost<E: Event>(work: Seq<Work<'_, E>>) -> nat
    decreases work.len(),
{
    if work.len() == 0 { 0 }
    else { work_cost::<E>(work.drop_last()) + match work.last() {
        Work::Regex(source) => regex_cost::<E>(source@),
        Work::Test(source) => test_cost::<E>(source@),
        _ => 1,
    } }
}

pub(crate) proof fn lemma_work_cost_push<'a, E: Event>(work: Seq<Work<'a, E>>, task: Work<'a, E>)
    ensures work_cost::<E>(work.push(task)) == work_cost::<E>(work) + match task {
        Work::Regex(source) => regex_cost::<E>(source@),
        Work::Test(source) => test_cost::<E>(source@),
        _ => 1,
    },
{
    assert(work.push(task).drop_last() =~= work);
    assert(work.push(task).last() == task);
    reveal_with_fuel(work_cost, 1);
}


pub proof fn lemma_test_forest_cost_append<E: Event>(left: Seq<SourceTest<E>>, right: Seq<SourceTest<E>>)
    ensures test_forest_cost::<E>(left + right) == test_forest_cost::<E>(left) + test_forest_cost::<E>(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_test_forest_cost_append::<E>(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    } else { assert(left + right =~= left); }
}

pub proof fn lemma_regex_forest_cost_append<E: Event>(left: Seq<SourceRegex<E>>, right: Seq<SourceRegex<E>>)
    ensures regex_forest_cost::<E>(left + right) == regex_forest_cost::<E>(left) + regex_forest_cost::<E>(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_regex_forest_cost_append::<E>(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    } else { assert(left + right =~= left); }
}

pub proof fn lemma_test_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more: Seq<FlatTest<E::Component>>,
    id: nat, source: SourceTest<E>, head: SourceHead<E>)
    requires more.len() >= tests.len(), more.take(tests.len() as int) == tests,
        test_represents::<E>(tests, id, source, head),
    ensures test_represents::<E>(more, id, source, head),
    decreases source,
{
    reveal_with_fuel(test_represents, 2);
    assert(more[id as int] == tests[id as int]);
    match source {
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            assert(ids.len() == children.len());
            assert(flat::references_before(ids, id));
            assert forall|i: int| 0 <= i < children.len() implies
                test_represents::<E>(tests, ids[i] as nat, children[i], head) by {}
            assert forall|i: int| 0 <= i < children.len() implies
                test_represents::<E>(more, ids[i] as nat, children[i], head) by {
                lemma_test_extension::<E>(tests, more, ids[i] as nat, children[i], head);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_regex_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more_tests: Seq<FlatTest<E::Component>>,
    regexes: Seq<FlatRegex>, more_regexes: Seq<FlatRegex>, id: nat, source: SourceRegex<E>, head: SourceHead<E>)
    requires more_tests.len() >= tests.len(), more_tests.take(tests.len() as int) == tests,
        more_regexes.len() >= regexes.len(), more_regexes.take(regexes.len() as int) == regexes,
        regex_represents::<E>(tests, regexes, id, source, head),
    ensures regex_represents::<E>(more_tests, more_regexes, id, source, head),
    decreases source,
{
    reveal_with_fuel(regex_represents, 2);
    assert(more_regexes[id as int] == regexes[id as int]);
    match source {
        RegexView::Test(test) => match regexes[id as int] {
            FlatRegex::Test(test_id) => lemma_test_extension::<E>(tests, more_tests, test_id as nat, test, head),
            _ => {},
        },
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                regex_represents::<E>(more_tests, more_regexes, ids[i] as nat, children[i], head) by {
                lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, ids[i] as nat, children[i], head);
            }
        },
        RegexView::Star(child) | RegexView::Not(child) => match regexes[id as int] {
            FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) =>
                lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, child_id as nat, *child, head),
            _ => {},
        },
        _ => {},
    }
}

pub proof fn lemma_stack_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more_tests: Seq<FlatTest<E::Component>>,
    regexes: Seq<FlatRegex>, more_regexes: Seq<FlatRegex>, test_ids: Seq<u32>, regex_ids: Seq<u32>,
    test_sources: Seq<SourceTest<E>>, regex_sources: Seq<SourceRegex<E>>, head: SourceHead<E>)
    requires more_tests.len() >= tests.len(), more_tests.take(tests.len() as int) == tests,
        more_regexes.len() >= regexes.len(), more_regexes.take(regexes.len() as int) == regexes,
        result_stacks::<E>(tests, regexes, test_ids, regex_ids, test_sources, regex_sources, head),
    ensures result_stacks::<E>(more_tests, more_regexes, test_ids, regex_ids, test_sources, regex_sources, head),
{
    assert forall|i: int| 0 <= i < test_ids.len() implies
        test_represents::<E>(more_tests, test_ids[i] as nat, test_sources[i], head) by {
        lemma_test_extension::<E>(tests, more_tests, test_ids[i] as nat, test_sources[i], head);
    }
    assert forall|i: int| 0 <= i < regex_ids.len() implies
        regex_represents::<E>(more_tests, more_regexes, regex_ids[i] as nat, regex_sources[i], head) by {
        lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, regex_ids[i] as nat, regex_sources[i], head);
    }
}

/// The flat head compares the actual event's projections, not an arbitrary component tuple.
pub proof fn lemma_event_head_semantics<E: Event>(
    head: Seq<FlatHead<E::Component>>, source: SourceHead<E>, candidate: E,
)
    requires head_represents::<E>(head, source),
    ensures flat::head_matches(head, history_syntax::spec::events::event_view(candidate),
        component_equality::<E>()) == crate::spec::semantics::head_matches::<E>(source, candidate),
{
    let projected = history_syntax::spec::events::event_view(candidate);
    assert(projected.len() == arity::<E>());
    assert(head.len() == source.len());
    assert(flat::event_wf(projected, head.len()));
    assert forall|i: int| 0 <= i < head.len() implies
        (match #[trigger] head[i] {
            FlatHead::Constant(expected) =>
                component_equality::<E>()(Component(i as u8), projected[i], expected),
            _ => true,
        }) == (match source[i] {
            PatternView::Constant(expected) => projected[i].eq_spec(&expected),
            PatternView::Variable(_) => true,
        }) by {
        assert(head_slot_represents(head[i], source[i]));
    }
    assert forall|i: int| 0 <= i < source.len() implies match #[trigger] source[i] {
        PatternView::Constant(expected) => projected[i].eq_spec(&expected),
        PatternView::Variable(_) => true,
    } == (match head[i] {
        FlatHead::Constant(expected) => component_equality::<E>()(Component(i as u8), projected[i], expected),
        _ => true,
    }) by {
        assert(head_slot_represents(head[i], source[i]));
    }
}

/// Flat tests evaluate R2's tests on real events under their structural representation.
pub proof fn lemma_event_test_semantics<E: Event>(
    tests: Seq<FlatTest<E::Component>>, id: nat, source: SourceTest<E>,
    head: SourceHead<E>, candidate: E, event: E,
)
    requires test_represents::<E>(tests, id, source, head), head.len() == arity::<E>(),
    ensures flat::test_sem(tests, id, history_syntax::spec::events::event_view(candidate),
        history_syntax::spec::events::event_view(event), component_equality::<E>())
        == crate::spec::semantics::test_sem::<E>(source, head, candidate, event),
    decreases source,
{
    let c = history_syntax::spec::events::event_view(candidate);
    let e = history_syntax::spec::events::event_view(event);
    assert(c.len() == head.len() && e.len() == head.len());
    reveal_with_fuel(flat::test_sem, 2);
    reveal_with_fuel(crate::spec::semantics::test_sem, 2);
    reveal_with_fuel(test_represents, 2);
    lemma_test_operands(tests[id as int]);
    match source {
        TestView::Atom { pattern, .. } => {
            if let FlatTest::Atom { term, .. } = tests[id as int] {
                if let FlatTerm::Variable(_) = term {
                    match head[pattern.component as int] {
                        PatternView::Constant(_) => {}, PatternView::Variable(_) => {},
                    }
                }
            }
            assert(flat::test_sem(tests, id, c, e, component_equality::<E>())
                == crate::spec::semantics::test_sem::<E>(source, head, candidate, event));
        },
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                flat::test_sem(tests, ids[i] as nat, c, e, component_equality::<E>())
                    == crate::spec::semantics::test_sem::<E>(children[i], head, candidate, event) by {
                lemma_event_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
            }
            if source is And {
                if crate::spec::semantics::test_sem::<E>(source, head, candidate, event) {
                    assert forall|i: int| 0 <= i < ids.len() implies
                        flat::test_sem(tests, ids[i] as nat, c, e, component_equality::<E>()) by {
                        lemma_event_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                    }
                }
                if flat::test_sem(tests, id, c, e, component_equality::<E>()) {
                    assert forall|i: int| 0 <= i < children.len() implies
                        crate::spec::semantics::test_sem::<E>(children[i], head, candidate, event) by {
                        lemma_event_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                    }
                }
            } else {
                if crate::spec::semantics::test_sem::<E>(source, head, candidate, event) {
                    let i = choose|i: int| 0 <= i < children.len()
                        && crate::spec::semantics::test_sem::<E>(children[i], head, candidate, event);
                    lemma_event_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                }
                if flat::test_sem(tests, id, c, e, component_equality::<E>()) {
                    let i = choose|i: int| 0 <= i < ids.len()
                        && flat::test_sem(tests, ids[i] as nat, c, e, component_equality::<E>());
                    lemma_event_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                }
            }
            assert(flat::test_sem(tests, id, c, e, component_equality::<E>())
                == crate::spec::semantics::test_sem::<E>(source, head, candidate, event));
        },
        _ => {},
    }
}
/// Relates a history of real events to the component words consumed by the flat machine.
pub open spec fn projected_history<E: Event>(history: Seq<E>, word: Seq<SourceEvent<E>>) -> bool {
    crate::verify::encoding::pointwise(history, word,
        |event: E, projected: SourceEvent<E>|
            history_syntax::spec::events::event_view(event) == projected)
}

/// Structural regex lowering preserves R2 membership on real histories.
pub proof fn lemma_event_regex_semantics<E: Event>(
    tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>, candidate: E,
    history: Seq<E>, word: Seq<SourceEvent<E>>,
)
    requires regex_represents::<E>(tests, regexes, id, source, head),
        head.len() == arity::<E>(), projected_history::<E>(history, word),
    ensures flat::lang(tests, regexes, id, history_syntax::spec::events::event_view(candidate),
        word, component_equality::<E>())
        == crate::spec::semantics::lang::<E>(source, head, candidate, history),
    decreases source,
{
    let c = history_syntax::spec::events::event_view(candidate);
    assert forall|i: int| 0 <= i < word.len() implies flat::event_wf(#[trigger] word[i], c.len()) by {
        assert(word[i] == history_syntax::spec::events::event_view(history[i]));
    }
    reveal_with_fuel(flat::lang, 2);
    reveal_with_fuel(crate::spec::semantics::lang, 2);
    reveal_with_fuel(regex_represents, 2);
    lemma_regex_operands(regexes[id as int]);
    match source {
        RegexView::Test(test) => {
            if let FlatRegex::Test(test_id) = regexes[id as int] {
                if history.len() == 1 {
                    lemma_event_test_semantics::<E>(tests, test_id as nat, test, head, candidate, history[0]);
                }
            }
            assert(flat::lang(tests, regexes, id, c, word, component_equality::<E>())
                == crate::spec::semantics::lang::<E>(source, head, candidate, history));
        },
        RegexView::Union(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                flat::lang(tests, regexes, ids[i] as nat, c, word, component_equality::<E>())
                    == crate::spec::semantics::lang::<E>(children[i], head, candidate, history) by {
                lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                    head, candidate, history, word);
            }
            if source is Intersect {
                if crate::spec::semantics::lang::<E>(source, head, candidate, history) {
                    assert forall|i: int| 0 <= i < ids.len() implies
                        flat::lang(tests, regexes, ids[i] as nat, c, word, component_equality::<E>()) by {
                        lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                            head, candidate, history, word);
                    }
                }
                if flat::lang(tests, regexes, id, c, word, component_equality::<E>()) {
                    assert forall|i: int| 0 <= i < children.len() implies
                        crate::spec::semantics::lang::<E>(children[i], head, candidate, history) by {
                        lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                            head, candidate, history, word);
                    }
                }
            } else {
                if crate::spec::semantics::lang::<E>(source, head, candidate, history) {
                    let i = choose|i: int| 0 <= i < children.len()
                        && crate::spec::semantics::lang::<E>(children[i], head, candidate, history);
                    lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                        head, candidate, history, word);
                }
                if flat::lang(tests, regexes, id, c, word, component_equality::<E>()) {
                    let i = choose|i: int| 0 <= i < ids.len()
                        && flat::lang(tests, regexes, ids[i] as nat, c, word, component_equality::<E>());
                    lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                        head, candidate, history, word);
                }
            }
            assert(flat::lang(tests, regexes, id, c, word, component_equality::<E>())
                == crate::spec::semantics::lang::<E>(source, head, candidate, history));
        },
        RegexView::Not(child) => {
            if let FlatRegex::Complement(child_id) = regexes[id as int] {
                lemma_event_regex_semantics::<E>(tests, regexes, child_id as nat, *child,
                    head, candidate, history, word);
            }
            assert(flat::lang(tests, regexes, id, c, word, component_equality::<E>())
                == crate::spec::semantics::lang::<E>(source, head, candidate, history));
        },
        RegexView::Concat(children) => {
            let ids = regex_operands(regexes[id as int]);
            if crate::spec::semantics::lang::<E>(source, head, candidate, history) {
                let parts = choose|parts: Seq<Seq<E>>| parts.len() == children.len()
                    && history == parts.flatten() && forall|i: int| 0 <= i < children.len() ==>
                        crate::spec::semantics::lang::<E>(children[i], head, candidate, parts[i]);
                let relation = |p: SourceEvent<E>, event: E| history_syntax::spec::events::event_view(event) == p;
                assert(crate::verify::encoding::pointwise(word, history, relation));
                crate::verify::encoding::lemma_partition_lift(word, history, parts, relation);
                let lifted = choose|lifted: Seq<Seq<SourceEvent<E>>>| lifted.len() == parts.len()
                    && word == lifted.flatten() && forall|i: int| 0 <= i < parts.len() ==>
                        crate::verify::encoding::pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < children.len() implies
                    flat::lang(tests, regexes, ids[i] as nat, c, lifted[i], component_equality::<E>()) by {
                    assert(projected_history::<E>(parts[i], lifted[i]));
                    lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                        head, candidate, parts[i], lifted[i]);
                }
                assert(flat::lang(tests, regexes, id, c, word, component_equality::<E>()));
            }
            if flat::lang(tests, regexes, id, c, word, component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<SourceEvent<E>>>| parts.len() == ids.len()
                    && word == parts.flatten() && forall|i: int| 0 <= i < ids.len() ==>
                        flat::lang(tests, regexes, ids[i] as nat, c, parts[i], component_equality::<E>());
                let relation = |event: E, p: SourceEvent<E>| history_syntax::spec::events::event_view(event) == p;
                crate::verify::encoding::lemma_partition_lift(history, word, parts, relation);
                let lifted = choose|lifted: Seq<Seq<E>>| lifted.len() == parts.len()
                    && history == lifted.flatten() && forall|i: int| 0 <= i < parts.len() ==>
                        crate::verify::encoding::pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < children.len() implies
                    crate::spec::semantics::lang::<E>(children[i], head, candidate, lifted[i]) by {
                    lemma_event_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i],
                        head, candidate, lifted[i], parts[i]);
                }
                assert(crate::spec::semantics::lang::<E>(source, head, candidate, history));
            }
        },
        RegexView::Star(child) => {
            if let FlatRegex::Star(child_id) = regexes[id as int] {
                if crate::spec::semantics::lang::<E>(source, head, candidate, history) {
                    let parts = choose|parts: Seq<Seq<E>>| history == parts.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==>
                            crate::spec::semantics::lang::<E>(*child, head, candidate, parts[i]);
                    let relation = |p: SourceEvent<E>, event: E| history_syntax::spec::events::event_view(event) == p;
                    assert(crate::verify::encoding::pointwise(word, history, relation));
                    crate::verify::encoding::lemma_partition_lift(word, history, parts, relation);
                    let lifted = choose|lifted: Seq<Seq<SourceEvent<E>>>| lifted.len() == parts.len()
                        && word == lifted.flatten() && forall|i: int| 0 <= i < parts.len() ==>
                            crate::verify::encoding::pointwise(lifted[i], parts[i], relation);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        flat::lang(tests, regexes, child_id as nat, c, lifted[i], component_equality::<E>()) by {
                        assert(projected_history::<E>(parts[i], lifted[i]));
                        lemma_event_regex_semantics::<E>(tests, regexes, child_id as nat, *child,
                            head, candidate, parts[i], lifted[i]);
                    }
                    assert(flat::lang(tests, regexes, id, c, word, component_equality::<E>()));
                }
                if flat::lang(tests, regexes, id, c, word, component_equality::<E>()) {
                    let parts = choose|parts: Seq<Seq<SourceEvent<E>>>| word == parts.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==>
                            flat::lang(tests, regexes, child_id as nat, c, parts[i], component_equality::<E>());
                    let relation = |event: E, p: SourceEvent<E>| history_syntax::spec::events::event_view(event) == p;
                    crate::verify::encoding::lemma_partition_lift(history, word, parts, relation);
                    let lifted = choose|lifted: Seq<Seq<E>>| lifted.len() == parts.len()
                        && history == lifted.flatten() && forall|i: int| 0 <= i < parts.len() ==>
                            crate::verify::encoding::pointwise(lifted[i], parts[i], relation);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        crate::spec::semantics::lang::<E>(*child, head, candidate, lifted[i]) by {
                        lemma_event_regex_semantics::<E>(tests, regexes, child_id as nat, *child,
                            head, candidate, lifted[i], parts[i]);
                    }
                    assert(crate::spec::semantics::lang::<E>(source, head, candidate, history));
                }
            }
        },
        _ => {},
    }
}


/// Every event in a partition retains the original word's coordinate count.
pub proof fn lemma_partition_arity<C>(parts: Seq<Seq<Seq<C>>>, arity: nat)
    requires forall|i: int| 0 <= i < parts.flatten().len() ==> parts.flatten()[i].len() == arity,
    ensures forall|i: int, j: int| 0 <= i < parts.len() && 0 <= j < parts[i].len()
        ==> parts[i][j].len() == arity,
    decreases parts.len(),
{
    if parts.len() > 0 {
        assert(parts =~= parts.drop_last().push(parts.last()));
        parts.drop_last().lemma_flatten_push(parts.last());
        let prefix = parts.drop_last().flatten();
        assert forall|j: int| 0 <= j < prefix.len() implies prefix[j].len() == arity by {
            assert(prefix[j] == parts.flatten()[j]);
        }
        lemma_partition_arity(parts.drop_last(), arity);
        assert forall|i: int, j: int| 0 <= i < parts.len() && 0 <= j < parts[i].len()
            implies parts[i][j].len() == arity by {
            if i < parts.len() - 1 { assert(parts[i] == parts.drop_last()[i]); }
            else {
                assert(parts[i] == parts.last());
                assert(parts[i][j] == parts.flatten()[prefix.len() as int + j]);
            }
        }
    }
}


/// Executable flattening preserves the canonical real-event semantics.
pub proof fn flattening_preserves_semantics<E: Event>(rule: Rule<E>, lowered: FlatRule<E::Component>,
    candidate: E, history: Seq<E>)
    requires flattened::<E>(rule, lowered),
    ensures
        flat::head_matches(lowered.source.head@, history_syntax::spec::events::event_view(candidate),
            component_equality::<E>()) == crate::spec::semantics::head_matches::<E>(rule.head@, candidate),
        flat::lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            history_syntax::spec::events::event_view(candidate),
            history.map(|i: int, event: E| history_syntax::spec::events::event_view(event)),
            component_equality::<E>()) == crate::spec::semantics::lang::<E>(rule.tail@, rule.head@, candidate, history),
{
    let word = history.map(|i: int, event: E| history_syntax::spec::events::event_view(event));
    assert(projected_history::<E>(history, word));
    lemma_event_head_semantics::<E>(lowered.source.head@, rule.head@, candidate);
    lemma_event_regex_semantics::<E>(lowered.source.tests@, lowered.source.regexes@,
        lowered.source.root as nat, rule.tail@, rule.head@, candidate, history, word);
}

/// A client of the executable body obtains the semantic bridge without a correctness precondition.
pub fn flattening_client<E: Event, L: Limits>(rule: &Rule<E>, limits: &mut L, world: &mut ObservationWorld,
    Ghost(candidate): Ghost<E>, Ghost(history): Ghost<Seq<E>>)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    ensures crate::verify::errors::no_internal_compile_error(result),
        dsl::head_scoped(rule.head@) && dsl::regex_scoped(rule.tail@, rule.head@)
            ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                && !(result matches Err(CompileError::UnboundVariable { .. })),
        result matches Ok(lowered) ==>
        dsl::head_scoped(rule.head@) && dsl::regex_scoped(rule.tail@, rule.head@)
        && flat::head_matches(lowered.source.head@, history_syntax::spec::events::event_view(candidate),
            component_equality::<E>()) == crate::spec::semantics::head_matches::<E>(rule.head@, candidate)
        && flat::lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            history_syntax::spec::events::event_view(candidate),
            history.map(|i: int, event: E| history_syntax::spec::events::event_view(event)),
            component_equality::<E>()) == crate::spec::semantics::lang::<E>(rule.tail@, rule.head@, candidate, history),
{
    let result = crate::flatten::flatten_rule(rule, limits, world);
    proof {
        match &result {
            Ok(lowered) => flattening_preserves_semantics::<E>(*rule, *lowered, candidate, history),
            Err(_) => {},
        }
    }
    result
}

/// A named-variable proof client works at any declared event arity.
pub fn named_variable_client<E: Event, L: Limits>(head: Head<E>, name: alloc::string::String,
    component: Component, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    requires dsl::head_scoped(head@), component.0 < head@.len(),
        dsl::pattern_name(head@[component.0 as int]) == Some(name@),
    ensures crate::verify::errors::no_internal_compile_error(result),
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
        !(result matches Err(CompileError::UnboundVariable { .. })),
        result matches Ok(lowered) ==>
        lowered.source.head@[component.0 as int] is Bind && lowered.mode == RuleMode::Require
        && match lowered.source.regexes@[lowered.source.root as int] {
            FlatRegex::Test(id) => lowered.source.tests@[id as int] == (FlatTest::Atom { field: component,
                term: FlatTerm::Variable(component), positive: true }),
            _ => false,
        },
{
    let source = Rule::new(RuleMode::Require, head,
        RegexExpr::test(TestExpr::atom(history_syntax::syntax::Comparison::Eq,
            history_syntax::syntax::AtomPattern::new(component, ComponentPattern::Variable(name)))));
    let result = crate::flatten::flatten_rule(&source, limits, world);
    proof {
        reveal_with_fuel(history_syntax::verify::dsl::regex_view, 2);
        reveal_with_fuel(history_syntax::verify::dsl::test_view, 2);
        reveal_with_fuel(regex_represents, 2);
        reveal_with_fuel(test_represents, 2);
    }
    source.dispose();
    result
}

/// Constant-only heads need no invented head-binding premise.
pub fn constant_head_client<E: Event, L: Limits>(head: Head<E>, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    requires forall|i: int| 0 <= i < head@.len() ==> head@[i] is Constant,
    ensures crate::verify::errors::no_internal_compile_error(result),
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
        !(result matches Err(CompileError::UnboundVariable { .. })),
        !(result matches Err(CompileError::Runtime(crate::error::HistoryError::InvalidPolicy { .. }))),
{
    let source = Rule::new(RuleMode::Require, head, RegexExpr::all());
    let result = crate::flatten::flatten_rule(&source, limits, world);
    source.dispose();
    result
}

}
