//! Canonical ghost syntax for a numeric flat source, without compiling a second graph.

use super::{table, typed_numeric as typed};
use alloc::boxed::Box;
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::encoding;
use history_syntax::RuleMode;
use junco_core::flat::{FlatPair, FlatRegex, FlatTest};
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::{self as language, EventView, Regex, Subst};
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
    reveal_with_fuel(language::numeric_lang, 2);
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
                        && language::numeric_lang(model::gsem(theta), actual[i], w);
                    assert(numeric::source_regex(p, cs@[i] as nat, theta, w));
                    assert(numeric::source_regex(p, index, theta, w));
                }
                if numeric::source_regex(p, index, theta, w) {
                    let i = choose|i: int| 0 <= i < cs@.len() && cs@[i] < index
                        && numeric::source_regex(p, cs@[i] as nat, theta, w);
                    assert(language::numeric_lang(model::gsem(theta), actual[i], w));
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
                        assert(language::numeric_lang(model::gsem(theta), actual[i], w));
                    }
                }
                if numeric::source_regex(p, index, theta, w) {
                    assert forall|i: int| 0 <= i < actual.len()
                        implies language::numeric_lang(model::gsem(theta), actual[i], w) by {
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
                            ==> language::numeric_lang(model::gsem(theta), actual[i], parts[i]);
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
                        implies language::numeric_lang(model::gsem(theta), actual[i], parts[i]) by {
                        assert(actual[i] == source_model(p, cs@[i] as nat));
                        lemma_source_model_at(p, cs@[i] as nat, theta, parts[i]);
                    }
                    assert(language::numeric_lang(model::gsem(theta), source_model(p, index), w));
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
                            ==> language::numeric_lang(model::gsem(theta), source_model(p, child as nat), parts[i]);
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
                        implies language::numeric_lang(model::gsem(theta), source_model(p, child as nat), parts[i]) by {
                        lemma_source_model_at(p, child as nat, theta, parts[i]);
                    }
                    assert(language::numeric_lang(model::gsem(theta), source_model(p, index), w));
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
}
