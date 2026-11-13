//! Structural scoping for owned-source lowering, and real-event language facts.

use crate::spec::semantics::{lang, test_sem};
use alloc::boxed::Box;
use history_syntax::Component;
use history_syntax::Event;
use history_syntax::spec::events::{AtomView, HeadView, PatternView, RegexView, TestView};
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};



pub open spec fn pattern_name<T>(pattern: PatternView<T>) -> Option<Seq<char>> {
    match pattern { PatternView::Constant(_) => None, PatternView::Variable(name) => Some(name) }
}

pub open spec fn distinct_names<T, U>(left: PatternView<T>, right: PatternView<U>) -> bool {
    match (pattern_name(left), pattern_name(right)) {
        (Some(a), Some(b)) => a != b,
        _ => true,
    }
}

pub open spec fn head_scoped<C>(head: HeadView<C>) -> bool {
    forall|i: int, j: int| 0 <= i < j < head.len() ==>
        distinct_names(#[trigger] head[i], #[trigger] head[j])
}


pub open spec fn pattern_scoped<T>(pattern: PatternView<T>, head: PatternView<T>) -> bool {
    match pattern {
        PatternView::Constant(_) => true,
        PatternView::Variable(name) => pattern_name(head) == Some(name),
    }
}

pub open spec fn atom_scoped<C>(atom: AtomView<C>, head: HeadView<C>) -> bool {
    atom.component < head.len() && pattern_scoped(atom.pattern, head[atom.component as int])
}

pub open spec fn test_scoped<C>(test: TestView<C>, head: HeadView<C>) -> bool
    decreases test,
{
    match test {
        TestView::True | TestView::False => true,
        TestView::Atom { pattern, .. } => atom_scoped(pattern, head),
        // Separate bindings keep conditional expressions out of the quantified index triggers.
        TestView::And(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(#[trigger] children[i], head),
        TestView::Or(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(#[trigger] children[i], head),
    }
}

pub open spec fn regex_scoped<C>(regex: RegexView<C>, head: HeadView<C>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => true,
        RegexView::Test(test) => test_scoped(test, head),
        RegexView::Union(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Concat(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Intersect(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Star(child) | RegexView::Not(child) => regex_scoped(*child, head),
    }
}


/// Empty operators retain their different Boolean and language identities.
pub proof fn lemma_empty_operators<E: Event>(
    head: HeadView<E::Component>, candidate: E, word: Seq<E>,
)
    ensures
        test_sem(TestView::And(Seq::empty()), head, candidate, candidate),
        !test_sem(TestView::Or(Seq::empty()), head, candidate, candidate),
        !lang(RegexView::Union(Seq::empty()), head, candidate, word),
        lang(RegexView::Intersect(Seq::empty()), head, candidate, word),
        lang(RegexView::Concat(Seq::empty()), head, candidate, word) <==> word.len() == 0,
{
    if lang(RegexView::Concat(Seq::empty()), head, candidate, word) {
        let parts = choose|parts: Seq<Seq<E>>|
            parts.len() == 0 && word == parts.flatten()
            && forall|i: int| 0 <= i < 0 ==> lang(RegexView::Empty, head, candidate, parts[i]);
        assert(parts =~= Seq::empty());
    }
    if word.len() == 0 {
        let parts: Seq<Seq<E>> = Seq::empty();
        assert(word =~= parts.flatten());
        assert(lang(RegexView::Concat(Seq::empty()), head, candidate, word));
    }
}

proof fn lemma_star_test_lang<E: Event>(
    test: TestView<E::Component>, head: HeadView<E::Component>, candidate: E,
    word: Seq<E>,
)
    ensures
        lang(RegexView::Star(Box::new(RegexView::Test(test))), head, candidate, word)
            <==> forall|i: int| 0 <= i < word.len() ==> test_sem(test, head, candidate, word[i]),
    decreases word.len(),
{
    reveal_with_fuel(lang, 2);
    let star = RegexView::Star(Box::new(RegexView::Test(test)));
    if word.len() == 0 {
        let parts: Seq<Seq<E>> = Seq::empty();
        assert(word =~= parts.flatten());
        assert(forall|i: int| 0 <= i < parts.len() ==>
            lang(RegexView::Test(test), head, candidate, parts[i]));
        assert(lang(star, head, candidate, word));
    } else {
        let rest = word.drop_first();
        lemma_star_test_lang(test, head, candidate, rest);
        if lang(star, head, candidate, word) {
            let parts = choose|parts: Seq<Seq<E>>|
                word == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==>
                    lang(RegexView::Test(test), head, candidate, parts[i]);
            assert(parts.len() > 0);
            assert(lang(RegexView::Test(test), head, candidate, parts[0]));
            assert(parts[0].len() == 1);
            let tail = parts.drop_first();
            assert(word == parts[0] + tail.flatten());
            assert(word[0] == parts[0][0]);
            assert(parts[0] =~= seq![word[0]]);
            assert(rest =~= tail.flatten());
            assert forall|i: int| 0 <= i < tail.len() implies
                lang(RegexView::Test(test), head, candidate, tail[i]) by {
                assert(tail[i] == parts[i + 1]);
            }
            assert(lang(star, head, candidate, rest));
            assert forall|i: int| 0 <= i < word.len() implies
                test_sem(test, head, candidate, word[i]) by {
                if i > 0 {
                    assert(rest[i - 1] == word[i]);
                    assert(test_sem(test, head, candidate, rest[i - 1]));
                }
            }
        }
        if forall|i: int| 0 <= i < word.len() ==> test_sem(test, head, candidate, word[i]) {
            assert forall|i: int| 0 <= i < rest.len() implies
                test_sem(test, head, candidate, rest[i]) by {
                assert(rest[i] == word[i + 1]);
            }
            assert(lang(star, head, candidate, rest));
            let tail = choose|tail: Seq<Seq<E>>|
                rest == tail.flatten()
                && forall|i: int| 0 <= i < tail.len() ==>
                    lang(RegexView::Test(test), head, candidate, tail[i]);
            let parts = seq![seq![word[0]]] + tail;
            assert(parts.drop_first() =~= tail);
            assert(word =~= seq![word[0]] + rest);
            assert(parts.flatten() == word);
            assert forall|i: int| 0 <= i < parts.len() implies
                lang(RegexView::Test(test), head, candidate, parts[i]) by {
                if i > 0 {
                    assert(parts[i] == tail[i - 1]);
                } else {
                    assert(parts[i] == seq![word[0]]);
                }
            }
            assert(lang(star, head, candidate, word));
        }
    }
}

/// A setter followed by a stable suffix; the setter need not be unique or disjoint from stable.
/// The empty word cannot match because the setter consumes exactly one event.
pub proof fn lemma_last_state_change_lang<E: Event>(
    setter: TestView<E::Component>, stable: TestView<E::Component>, head: HeadView<E::Component>,
    candidate: E, word: Seq<E>,
)
    ensures
        lang(RegexView::Concat(seq![RegexView::All, RegexView::Test(setter),
            RegexView::Star(Box::new(RegexView::Test(stable)))]), head, candidate, word)
        <==> exists|i: int| 0 <= i < word.len()
            && test_sem(setter, head, candidate, word[i])
            && forall|j: int| i < j < word.len() ==> test_sem(stable, head, candidate, word[j]),
{
    reveal_with_fuel(lang, 2);
    reveal_with_fuel(Seq::flatten, 4);
    let children = seq![RegexView::All, RegexView::Test(setter),
        RegexView::Star(Box::new(RegexView::Test(stable)))];
    let regex = RegexView::Concat(children);
    if lang(regex, head, candidate, word) {
        let parts = choose|parts: Seq<Seq<E>>|
            parts.len() == children.len() && word == parts.flatten()
            && forall|k: int| 0 <= k < children.len() ==>
                lang(children[k], head, candidate, parts[k]);
        assert(lang(children[1], head, candidate, parts[1]));
        assert(parts[1].len() == 1);
        assert(parts =~= seq![parts[0], parts[1], parts[2]]);
        assert(parts.flatten() == parts[0] + parts[1] + parts[2]);
        let i = parts[0].len() as int;
        assert(0 <= i < word.len());
        assert(word[i] == parts[1][0]);
        assert(test_sem(setter, head, candidate, word[i]));
        assert(lang(children[2], head, candidate, parts[2]));
        lemma_star_test_lang(stable, head, candidate, parts[2]);
        assert forall|j: int| i < j < word.len() implies
            test_sem(stable, head, candidate, word[j]) by {
            assert(0 <= j - i - 1 < parts[2].len());
            assert(word[j] == parts[2][j - i - 1]);
            assert(test_sem(stable, head, candidate, parts[2][j - i - 1]));
        }
        assert(exists|i: int| 0 <= i < word.len()
            && test_sem(setter, head, candidate, word[i])
            && forall|j: int| i < j < word.len() ==> test_sem(stable, head, candidate, word[j]));
    }
    if exists|i: int| 0 <= i < word.len()
        && test_sem(setter, head, candidate, word[i])
        && forall|j: int| i < j < word.len() ==> test_sem(stable, head, candidate, word[j]) {
        let i = choose|i: int| 0 <= i < word.len()
            && test_sem(setter, head, candidate, word[i])
            && forall|j: int| i < j < word.len() ==> test_sem(stable, head, candidate, word[j]);
        let prefix = word.take(i);
        let suffix = word.skip(i + 1);
        word.lemma_split_at(i);
        word.skip(i).lemma_split_at(1);
        assert(word.skip(i).take(1) =~= seq![word[i]]);
        assert(word.skip(i).skip(1) =~= suffix);
        assert(word == prefix + seq![word[i]] + suffix);
        assert forall|j: int| 0 <= j < suffix.len() implies
            test_sem(stable, head, candidate, suffix[j]) by {
            assert(suffix[j] == word[i + 1 + j]);
            assert(test_sem(stable, head, candidate, word[i + 1 + j]));
        }
        lemma_star_test_lang(stable, head, candidate, suffix);
        let parts = seq![prefix, seq![word[i]], suffix];
        assert(parts.flatten() == word);
        assert forall|k: int| 0 <= k < children.len() implies
            lang(children[k], head, candidate, parts[k]) by {
            if k == 0 {
                assert(children[k] == RegexView::All);
            } else if k == 1 {
                assert(children[k] == RegexView::Test(setter));
                assert(parts[k] == seq![word[i]]);
            } else {
                assert(k == 2);
                assert(children[k] == RegexView::Star(Box::new(RegexView::Test(stable))));
                assert(parts[k] == suffix);
            }
        }
        assert(lang(regex, head, candidate, word));
    }
}

pub proof fn lemma_complement_is_whole_word<E: Event>(
    regex: RegexView<E::Component>, head: HeadView<E::Component>, candidate: E,
    word: Seq<E>,
)
    ensures lang(RegexView::Not(Box::new(regex)), head, candidate, word)
        <==> !lang(regex, head, candidate, word),
{}


/// The real scope bodies preserve declarations and reject a cross-coordinate use.
pub fn scope_client<'a>(name: &'a str, arity: usize, first: Component, second: Component)
    -> (result: Result<Component, crate::error::CompileError>)
    requires 1 <= arity <= history_syntax::MAX_ARITY,
        first.0 < arity, second.0 < arity, first != second,
    ensures result == Ok(first),
{
    let mut scope = crate::scope::VariableScope::new(arity);
    let bound = scope.bind(first, name);
    proof! {
        assert(bound is Ok);
        let witness = first.0 as int;
        assert(Component(witness as u8) == first);
        assert(scope.has_name(Component(witness as u8), name@));
        assert(0 <= witness < scope.arity_spec() && witness != second.0);
        assert(scope.conflicts(second, name@));
    }
    let conflict = scope.bind(second, name);
    proof! { assert(conflict is Err); }
    scope.resolve(first, name)
}

}
