//! Canonical ghost syntax for a numeric flat source, without compiling a second graph.

use super::{table, typed_numeric as typed};
use alloc::boxed::Box;
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::encoding;
use history_syntax::RuleMode;
use junco_core::flat::{FlatPair, FlatRegex, FlatTest};
use junco_core::kernel::verify as model;
use junco_core::verify::numeric_regex::{self as language, EventView, Regex, Subst};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq::group_seq_lemmas;

pub(crate) open spec fn source_model_test(p: FlatPair<u64>, index: nat) -> model::Test
    decreases index,
{
    if index >= p.tests@.len() { model::Test::False } else {
        match p.tests@[index as int] {
            FlatTest::Bool(v) => if v { model::Test::True } else { model::Test::False },
            FlatTest::Atom { field, term, positive } =>
                model::Test::Atom(model::Primitive::Eq(field, numeric::term_view(term)), positive),
            FlatTest::And(cs) => model::Test::And(cs@.map(|i: int, child: u32|
                if child < index { source_model_test(p, child as nat) } else { model::Test::False })),
            FlatTest::Or(cs) => model::Test::Or(cs@.map(|i: int, child: u32|
                if child < index { source_model_test(p, child as nat) } else { model::Test::False })),
        }
    }
}

pub(crate) open spec fn source_model(p: FlatPair<u64>, index: nat) -> Regex<model::Test>
    decreases index,
{
    if index >= p.regexes@.len() { Regex::Empty } else {
        match p.regexes@[index as int] {
            FlatRegex::Empty => Regex::Empty,
            FlatRegex::All => Regex::All,
            FlatRegex::Epsilon => Regex::Epsilon,
            FlatRegex::Test(t) => Regex::Test(source_model_test(p, t as nat)),
            FlatRegex::Union(cs) => Regex::Union(cs@.map(|i: int, child: u32|
                if child < index { source_model(p, child as nat) } else { Regex::Empty })),
            FlatRegex::Intersect(cs) => Regex::Intersect(cs@.map(|i: int, child: u32|
                if child < index { source_model(p, child as nat) } else { Regex::Empty })),
            FlatRegex::Concat(cs) => Regex::Concat(cs@.map(|i: int, child: u32|
                if child < index { source_model(p, child as nat) } else { Regex::Empty })),
            FlatRegex::Star(child) => if child < index {
                Regex::Star(Box::new(source_model(p, child as nat)))
            } else { Regex::Empty },
            FlatRegex::Complement(child) => if child < index {
                Regex::Not(Box::new(source_model(p, child as nat)))
            } else { Regex::Empty },
        }
    }
}

pub(crate) proof fn lemma_source_model_test(p: FlatPair<u64>, index: nat, theta: Subst, event: EventView)
    requires table::dag(p),
    ensures model::test_holds(theta, source_model_test(p, index), event)
        == numeric::source_test(p, index, theta, event),
    decreases index,
{
    reveal_with_fuel(source_model_test, 1);
    reveal_with_fuel(numeric::source_test, 1);
    reveal_with_fuel(model::test_holds, 2);
    if index < p.tests@.len() {
        assert(table::test_dag(p.tests@[index as int], index));
        match p.tests@[index as int] {
            FlatTest::And(cs) => {
                assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index by {}
                let actual = match source_model_test(p, index) { model::Test::And(a) => a, _ => arbitrary() };
                assert(actual.len() == cs@.len());
                assert(source_model_test(p, index) == model::Test::And(actual));
                assert forall|i: int| 0 <= i < actual.len() implies
                    model::test_holds(theta, actual[i], event)
                        == numeric::source_test(p, cs@[i] as nat, theta, event) by {
                    assert(table::test_dag(p.tests@[index as int], index));
                    assert(actual[i] == source_model_test(p, cs@[i] as nat));
                    lemma_source_model_test(p, cs@[i] as nat, theta, event);
                }
                assert(model::test_holds(theta, source_model_test(p, index), event)
                    == (forall|i: int| 0 <= i < actual.len() ==> model::test_holds(theta, actual[i], event)));
                assert(numeric::source_test(p, index, theta, event)
                    == (forall|i: int| 0 <= i < cs@.len() ==> cs@[i] < index
                        && numeric::source_test(p, cs@[i] as nat, theta, event)));
                if model::test_holds(theta, source_model_test(p, index), event) {
                    assert forall|i: int| 0 <= i < cs@.len() implies
                        cs@[i] < index && numeric::source_test(p, cs@[i] as nat, theta, event) by {
                        assert(model::test_holds(theta, actual[i], event));
                    }
                }
                if numeric::source_test(p, index, theta, event) {
                    assert forall|i: int| 0 <= i < actual.len()
                        implies model::test_holds(theta, actual[i], event) by {
                        assert(numeric::source_test(p, cs@[i] as nat, theta, event));
                    }
                }
            },
            FlatTest::Or(cs) => {
                assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index by {}
                let actual = match source_model_test(p, index) { model::Test::Or(a) => a, _ => arbitrary() };
                assert(actual.len() == cs@.len());
                assert(source_model_test(p, index) == model::Test::Or(actual));
                assert forall|i: int| 0 <= i < actual.len() implies
                    model::test_holds(theta, actual[i], event)
                        == numeric::source_test(p, cs@[i] as nat, theta, event) by {
                    assert(table::test_dag(p.tests@[index as int], index));
                    assert(actual[i] == source_model_test(p, cs@[i] as nat));
                    lemma_source_model_test(p, cs@[i] as nat, theta, event);
                }
                assert(model::test_holds(theta, source_model_test(p, index), event)
                    == (exists|i: int| 0 <= i < actual.len() && model::test_holds(theta, actual[i], event)));
                assert(numeric::source_test(p, index, theta, event)
                    == (exists|i: int| 0 <= i < cs@.len() && cs@[i] < index
                        && numeric::source_test(p, cs@[i] as nat, theta, event)));
                if model::test_holds(theta, source_model_test(p, index), event) {
                    let i = choose|i: int| 0 <= i < actual.len() && model::test_holds(theta, actual[i], event);
                    assert(numeric::source_test(p, cs@[i] as nat, theta, event));
                    assert(numeric::source_test(p, index, theta, event));
                }
                if numeric::source_test(p, index, theta, event) {
                    let i = choose|i: int| 0 <= i < cs@.len() && cs@[i] < index
                        && numeric::source_test(p, cs@[i] as nat, theta, event);
                    assert(model::test_holds(theta, actual[i], event));
                    assert(model::test_holds(theta, source_model_test(p, index), event));
                }
            },
            FlatTest::Bool(_) => {
                assert(model::test_holds(theta, source_model_test(p, index), event)
                    == numeric::source_test(p, index, theta, event));
            },
            FlatTest::Atom { .. } => {
                assert(model::test_holds(theta, source_model_test(p, index), event)
                    == numeric::source_test(p, index, theta, event));
            },
        }
    }
}

pub(crate) proof fn lemma_source_model_at(p: FlatPair<u64>, index: nat, theta: Subst, w: Seq<EventView>)
    requires table::dag(p),
    ensures encoding::n_lang(theta, source_model(p, index), w) == numeric::source_regex(p, index, theta, w),
    decreases index,
{
    reveal_with_fuel(source_model, 1);
    reveal_with_fuel(numeric::source_regex, 1);
    reveal_with_fuel(language::lang, 2);
    reveal(encoding::n_lang);
    if index < p.regexes@.len() {
        assert(junco_core::flat::verify::regex_wf(p.regexes@[index as int], index, p.tests@.len()));
        match p.regexes@[index as int] {
            FlatRegex::Test(t) => {
                if w.len() == 1 { lemma_source_model_test(p, t as nat, theta, w[0]); }
                assert(encoding::n_lang(theta, source_model(p, index), w) == numeric::source_regex(p, index, theta, w));
            },
            FlatRegex::Union(cs) => {
                assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index by {}
                let actual = match source_model(p, index) { Regex::Union(a) => a, _ => arbitrary() };
                assert(actual.len() == cs@.len());
                assert(source_model(p, index) == Regex::Union(actual));
                language::lemma_lang_union(model::gsem(theta), actual, w);
                assert forall|i: int| 0 <= i < actual.len() implies
                    encoding::n_lang(theta, actual[i], w)
                        == numeric::source_regex(p, cs@[i] as nat, theta, w) by {
                    assert(actual[i] == source_model(p, cs@[i] as nat));
                    lemma_source_model_at(p, cs@[i] as nat, theta, w);
                }
                if encoding::n_lang(theta, source_model(p, index), w) {
                    let i = choose|i: int| 0 <= i < actual.len()
                        && language::lang(model::gsem(theta), actual[i], w);
                    assert(numeric::source_regex(p, cs@[i] as nat, theta, w));
                    assert(numeric::source_regex(p, index, theta, w));
                }
                if numeric::source_regex(p, index, theta, w) {
                    let i = choose|i: int| 0 <= i < cs@.len() && cs@[i] < index
                        && numeric::source_regex(p, cs@[i] as nat, theta, w);
                    assert(language::lang(model::gsem(theta), actual[i], w));
                    assert(encoding::n_lang(theta, source_model(p, index), w));
                }
            },
            FlatRegex::Intersect(cs) => {
                assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index by {}
                let actual = match source_model(p, index) { Regex::Intersect(a) => a, _ => arbitrary() };
                assert(actual.len() == cs@.len());
                assert(source_model(p, index) == Regex::Intersect(actual));
                language::lemma_lang_intersect(model::gsem(theta), actual, w);
                assert forall|i: int| 0 <= i < actual.len() implies
                    encoding::n_lang(theta, actual[i], w)
                        == numeric::source_regex(p, cs@[i] as nat, theta, w) by {
                    assert(actual[i] == source_model(p, cs@[i] as nat));
                    lemma_source_model_at(p, cs@[i] as nat, theta, w);
                }
                if encoding::n_lang(theta, source_model(p, index), w) {
                    assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index
                        && numeric::source_regex(p, cs@[i] as nat, theta, w) by {
                        assert(language::lang(model::gsem(theta), actual[i], w));
                    }
                }
                if numeric::source_regex(p, index, theta, w) {
                    assert forall|i: int| 0 <= i < actual.len()
                        implies language::lang(model::gsem(theta), actual[i], w) by {
                        assert(numeric::source_regex(p, cs@[i] as nat, theta, w));
                    }
                }
            },
            FlatRegex::Concat(cs) => {
                assert forall|i: int| 0 <= i < cs@.len() implies cs@[i] < index by {}
                let actual = match source_model(p, index) { Regex::Concat(a) => a, _ => arbitrary() };
                assert(source_model(p, index) == Regex::Concat(actual));
                assert(actual.len() == cs@.len());
                if encoding::n_lang(theta, source_model(p, index), w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == actual.len() && parts.flatten() == w
                        && forall|i: int| 0 <= i < actual.len()
                            ==> language::lang(model::gsem(theta), actual[i], parts[i]);
                    assert forall|i: int| 0 <= i < cs@.len()
                        implies cs@[i] < index && numeric::source_regex(p, cs@[i] as nat, theta, parts[i]) by {
                        assert(actual[i] == source_model(p, cs@[i] as nat));
                        lemma_source_model_at(p, cs@[i] as nat, theta, parts[i]);
                    }
                    assert(numeric::source_regex(p, index, theta, w));
                }
                if numeric::source_regex(p, index, theta, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs@.len() && parts.flatten() == w
                        && forall|i: int| 0 <= i < cs@.len()
                            ==> cs@[i] < index && numeric::source_regex(p, cs@[i] as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < actual.len()
                        implies language::lang(model::gsem(theta), actual[i], parts[i]) by {
                        assert(actual[i] == source_model(p, cs@[i] as nat));
                        lemma_source_model_at(p, cs@[i] as nat, theta, parts[i]);
                    }
                    assert(language::lang(model::gsem(theta), source_model(p, index), w));
                }
            },
            FlatRegex::Star(child) => {
                assert(child < index);
                assert forall|piece: Seq<EventView>|
                    encoding::n_lang(theta, source_model(p, child as nat), piece)
                        == numeric::source_regex(p, child as nat, theta, piece) by {
                    lemma_source_model_at(p, child as nat, theta, piece);
                }
                if encoding::n_lang(theta, source_model(p, index), w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == w
                        && forall|i: int| 0 <= i < parts.len()
                            ==> language::lang(model::gsem(theta), source_model(p, child as nat), parts[i]);
                    assert forall|i: int| 0 <= i < parts.len()
                        implies numeric::source_regex(p, child as nat, theta, parts[i]) by {
                        lemma_source_model_at(p, child as nat, theta, parts[i]);
                    }
                }
                if numeric::source_regex(p, index, theta, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == w
                        && forall|i: int| 0 <= i < parts.len()
                            ==> numeric::source_regex(p, child as nat, theta, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len()
                        implies language::lang(model::gsem(theta), source_model(p, child as nat), parts[i]) by {
                        lemma_source_model_at(p, child as nat, theta, parts[i]);
                    }
                    assert(language::lang(model::gsem(theta), source_model(p, index), w));
                }
            },
            FlatRegex::Complement(child) => {
                lemma_source_model_at(p, child as nat, theta, w);
                assert(encoding::n_lang(theta, source_model(p, index), w) == numeric::source_regex(p, index, theta, w));
            },
            _ => {
                assert(encoding::n_lang(theta, source_model(p, index), w) == numeric::source_regex(p, index, theta, w));
            },
        }
    }
}

pub(crate) proof fn lemma_source_model(p: FlatPair<u64>)
    requires table::dag(p), p.root < p.regexes@.len(),
    ensures forall|theta: Subst, w: Seq<EventView>| #[trigger] encoding::n_lang(theta, source_model(p, p.root as nat), w)
        == numeric::source_regex(p, p.root as nat, theta, w),
{
    assert forall|theta: Subst, w: Seq<EventView>| encoding::n_lang(theta, source_model(p, p.root as nat), w)
        == numeric::source_regex(p, p.root as nat, theta, w) by {
        lemma_source_model_at(p, p.root as nat, theta, w);
    }
}

pub(crate) open spec fn numeric_rule(p: FlatPair<u64>, mode: RuleMode) -> encoding::NRule {
    encoding::NRule { mode, head: typed::template_head(p), tail: source_model(p, p.root as nat) }
}

pub(crate) proof fn lemma_numeric_rule(p: FlatPair<u64>, mode: RuleMode)
    requires table::dag(p), p.root < p.regexes@.len(),
    ensures encoding::represents(numeric_rule(p, mode), mode, p),
{
    lemma_source_model(p);
}

/// Extending flat tables cannot introduce a primitive below an existing test root.
pub(crate) proof fn lemma_test_primitives_frame(before: FlatPair<u64>, after: FlatPair<u64>, id: nat)
    requires table::dag(before), table::frame(before, after), id < before.tests@.len(),
    ensures numeric::reachable_test_primitives(after, id).subset_of(numeric::reachable_test_primitives(before, id)),
    decreases id,
{
    reveal_with_fuel(numeric::reachable_test_primitives, 1);
    assert(after.tests@[id as int] == before.tests@[id as int]);
    assert forall|p: model::Primitive| numeric::reachable_test_primitives(after, id).contains(p)
        implies numeric::reachable_test_primitives(before, id).contains(p) by {
        match before.tests@[id as int] {
            FlatTest::And(children) | FlatTest::Or(children) => {
                numeric::lemma_reachable_test_prefix_member(after, id, children@.len(), children@, p);
                let i = choose|i: int| 0 <= i < children@.len() && children@[i] < id
                    && numeric::reachable_test_primitives(after, children@[i] as nat).contains(p);
                lemma_test_primitives_frame(before, after, children@[i] as nat);
                numeric::lemma_reachable_test_child(before, id, children@.len(), i);
            },
            _ => {},
        }
    }
}

/// The corresponding frame fact for a regex follows its actual reachable references.
pub(crate) proof fn lemma_regex_primitives_frame(before: FlatPair<u64>, after: FlatPair<u64>, id: nat)
    requires table::dag(before), table::frame(before, after), id < before.regexes@.len(),
    ensures numeric::reachable_regex_primitives(after, id).subset_of(numeric::reachable_regex_primitives(before, id)),
    decreases id,
{
    reveal_with_fuel(numeric::reachable_regex_primitives, 1);
    assert(after.regexes@[id as int] == before.regexes@[id as int]);
    assert forall|p: model::Primitive| numeric::reachable_regex_primitives(after, id).contains(p)
        implies numeric::reachable_regex_primitives(before, id).contains(p) by {
        match before.regexes@[id as int] {
            FlatRegex::Test(test) => {
                assert(test < before.tests@.len());
                lemma_test_primitives_frame(before, after, test as nat);
            },
            FlatRegex::Union(children) | FlatRegex::Concat(children) | FlatRegex::Intersect(children) => {
                numeric::lemma_reachable_regex_prefix_member(after, id, children@.len(), children@, p);
                let i = choose|i: int| 0 <= i < children@.len() && children@[i] < id
                    && numeric::reachable_regex_primitives(after, children@[i] as nat).contains(p);
                lemma_regex_primitives_frame(before, after, children@[i] as nat);
                numeric::lemma_reachable_regex_child(before, id, children@.len(), i);
            },
            FlatRegex::Star(child) | FlatRegex::Complement(child) => {
                if child < id { lemma_regex_primitives_frame(before, after, child as nat); }
            },
            _ => {},
        }
    }
}

/// Offset copying preserves precisely the source test's primitive support.
pub(crate) proof fn lemma_test_primitives_copy(source: FlatPair<u64>, target: FlatPair<u64>,
    by: nat, count: nat, id: nat)
    requires table::dag(source), table::tests_copied(source, target, by, count), id < count,
    ensures numeric::reachable_test_primitives(target, by + id).subset_of(numeric::reachable_test_primitives(source, id)),
    decreases id,
{
    reveal_with_fuel(numeric::reachable_test_primitives, 1);
    assert(table::test_shift(source.tests@[id as int], target.tests@[(by + id) as int], by));
    assert forall|p: model::Primitive| numeric::reachable_test_primitives(target, by + id).contains(p)
        implies numeric::reachable_test_primitives(source, id).contains(p) by {
        match (source.tests@[id as int], target.tests@[(by + id) as int]) {
            (FlatTest::And(a), FlatTest::And(b)) | (FlatTest::Or(a), FlatTest::Or(b)) => {
                numeric::lemma_reachable_test_prefix_member(target, by + id, b@.len(), b@, p);
                let i = choose|i: int| 0 <= i < b@.len() && b@[i] < by + id
                    && numeric::reachable_test_primitives(target, b@[i] as nat).contains(p);
                assert(b@[i] as nat == a@[i] as nat + by);
                assert(a@[i] < id);
                lemma_test_primitives_copy(source, target, by, count, a@[i] as nat);
                numeric::lemma_reachable_test_child(source, id, a@.len(), i);
            },
            _ => {},
        }
    }
}

/// The test and regex offsets are distinct; both are tracked by the real copy contract.
pub(crate) proof fn lemma_regex_primitives_copy(source: FlatPair<u64>, target: FlatPair<u64>,
    tests: nat, regexes: nat, count: nat, id: nat)
    requires table::dag(source), table::tests_copied(source, target, tests, source.tests@.len()),
        table::regexes_copied(source, target, tests, regexes, count), id < count,
    ensures numeric::reachable_regex_primitives(target, regexes + id).subset_of(numeric::reachable_regex_primitives(source, id)),
    decreases id,
{
    reveal_with_fuel(numeric::reachable_regex_primitives, 1);
    assert(table::regex_shift(source.regexes@[id as int], target.regexes@[(regexes + id) as int], tests, regexes));
    assert forall|p: model::Primitive| numeric::reachable_regex_primitives(target, regexes + id).contains(p)
        implies numeric::reachable_regex_primitives(source, id).contains(p) by {
        match (source.regexes@[id as int], target.regexes@[(regexes + id) as int]) {
            (FlatRegex::Test(a), FlatRegex::Test(b)) => {
                assert(a < source.tests@.len());
                assert(b as nat == a as nat + tests);
                lemma_test_primitives_copy(source, target, tests, source.tests@.len(), a as nat);
            },
            (FlatRegex::Union(a), FlatRegex::Union(b)) | (FlatRegex::Concat(a), FlatRegex::Concat(b))
                | (FlatRegex::Intersect(a), FlatRegex::Intersect(b)) => {
                numeric::lemma_reachable_regex_prefix_member(target, regexes + id, b@.len(), b@, p);
                let i = choose|i: int| 0 <= i < b@.len() && b@[i] < regexes + id
                    && numeric::reachable_regex_primitives(target, b@[i] as nat).contains(p);
                assert(b@[i] as nat == a@[i] as nat + regexes);
                assert(a@[i] < id);
                lemma_regex_primitives_copy(source, target, tests, regexes, count, a@[i] as nat);
                numeric::lemma_reachable_regex_child(source, id, a@.len(), i);
            },
            (FlatRegex::Star(a), FlatRegex::Star(b)) | (FlatRegex::Complement(a), FlatRegex::Complement(b)) => {
                assert(b as nat == a as nat + regexes);
                if a < id { lemma_regex_primitives_copy(source, target, tests, regexes, count, a as nat); }
            },
            _ => {},
        }
    }
}

/// Appending a forbid/require denial adds no primitive outside that source tail.
pub(crate) proof fn lemma_denial_primitives(source: FlatPair<u64>, target: FlatPair<u64>,
    tests: nat, regexes: nat, mode: RuleMode, root: nat)
    requires table::dag(source), source.root < source.regexes@.len(),
        table::tests_copied(source, target, tests, source.tests@.len()),
        table::regexes_copied(source, target, tests, regexes, source.regexes@.len()),
        root < target.regexes@.len(), root <= u32::MAX,
        match mode {
            RuleMode::Forbid => root == regexes + source.root as nat,
            RuleMode::Require => root == regexes + source.regexes@.len()
                && target.regexes@[root as int] == FlatRegex::Complement((regexes + source.root as nat) as u32),
        },
    ensures numeric::reachable_regex_primitives(target, root)
        .subset_of(numeric::reachable_regex_primitives(source, source.root as nat)),
{
    lemma_regex_primitives_copy(source, target, tests, regexes, source.regexes@.len(), source.root as nat);
    if mode is Require {
        reveal_with_fuel(numeric::reachable_regex_primitives, 1);
        assert(regexes + (source.root as nat) < root);
    }
}

/// The two actual nodes built by difference contribute only the two supplied roots.
pub(crate) proof fn lemma_difference_primitives(before: FlatPair<u64>, after: FlatPair<u64>,
    left: nat, right: nat)
    requires table::dag(before), table::frame(before, after),
        left < before.regexes@.len(), right < before.regexes@.len(),
        after.root as nat == before.regexes@.len() + 1,
        after.regexes@.len() == before.regexes@.len() + 2,
        after.regexes@[before.regexes@.len() as int] == FlatRegex::Complement(right as u32),
        match after.regexes@[after.root as int] {
            FlatRegex::Intersect(children) => children@ == seq![left as u32, before.regexes@.len() as u32],
            _ => false,
        },
    ensures numeric::reachable_regex_primitives(after, after.root as nat).subset_of(
        numeric::reachable_regex_primitives(before, left).union(numeric::reachable_regex_primitives(before, right))),
{
    lemma_regex_primitives_frame(before, after, left);
    lemma_regex_primitives_frame(before, after, right);
    reveal_with_fuel(numeric::reachable_regex_primitives, 1);
    if let FlatRegex::Intersect(children) = after.regexes@[after.root as int] {
        assert forall|p: model::Primitive|
            numeric::reachable_regex_primitives(after, after.root as nat).contains(p)
            implies numeric::reachable_regex_primitives(before, left).union(
                numeric::reachable_regex_primitives(before, right)).contains(p) by {
            numeric::lemma_reachable_regex_prefix_member(after, after.root as nat, children@.len(), children@, p);
            let i = choose|i: int| 0 <= i < children@.len() && children@[i] < after.root as nat
                && numeric::reachable_regex_primitives(after, children@[i] as nat).contains(p);
            if i == 0 {
                assert(children@[i] as nat == left);
            } else {
                assert(i == 1);
                assert(children@[i] as nat == before.regexes@.len());
                assert(right as u32 as nat == right);
                assert(numeric::reachable_regex_primitives(after, right).contains(p));
            }
        }
    }
}
}
