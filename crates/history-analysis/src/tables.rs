//! Numeric tables of one search, assembled from the encoded tails of analysed rules.

#[cfg(verus_keep_ghost)]
use crate::verify::table::*;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use history_semantics::compile_verify as numeric;
use history_syntax::syntax::RuleMode;
use junco_core::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::flat::verify as flat;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::no_internal_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{EventView, Subst};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};
}

/// Tests and regexes of one search; every reference points backward within its own table.
#[verus_verify]
pub(crate) struct Tables {
    pub(crate) head: Vec<FlatHead<u64>>,
    pub(crate) tests: Vec<FlatTest<u64>>,
    pub(crate) regexes: Vec<FlatRegex>,
}

#[verus_verify]
impl Tables {
    #[verus_spec(result => requires 1 <= arity <= history_syntax::MAX_ARITY,
        ensures result@.head@.len() == arity,
            forall|i: int| 0 <= i < arity ==> result@.head@[i] is Any,
            result@.tests@.len() == 0, result@.regexes@.len() == 0)]
    pub(crate) fn new(arity: usize) -> Self {
        proof! { reveal(<Tables as View>::view); }
        let mut head = Vec::with_capacity(arity);
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= arity, head@.len() == index,
                forall|i: int| 0 <= i < index ==> head@[i] is Any,
            decreases arity - index,
        ))]
        while index < arity {
            head.push(FlatHead::Any);
            index += 1;
        }
        Self {
            head,
            tests: Vec::new(),
            regexes: Vec::new(),
        }
    }
}

#[verus_verify]
impl Tables {
    /// Appends `source`'s tables after the existing ones and returns its root.
    #[verus_spec(result => requires dag(old(self)@), dag(*source),
        source.root < source.regexes@.len(),
        ensures no_internal_error(result),
            dag(final(self)@), frame(old(self)@, final(self)@),
            forall|index: nat, theta: Subst, word: Seq<EventView>| index < old(self).regexes@.len()
                ==> numeric::source_regex(old(self)@, index, theta, word)
                    == numeric::source_regex(final(self)@, index, theta, word),
            result matches Ok(root) ==> root < final(self).regexes@.len()
                && root as nat == source.root as nat + old(self).regexes@.len()
                && final(self).tests@.len() == old(self).tests@.len() + source.tests@.len()
                && tests_copied(*source, final(self)@, old(self).tests@.len(), source.tests@.len())
                && regexes_copied(*source, final(self)@, old(self).tests@.len(),
                    old(self).regexes@.len(), source.regexes@.len())
                && forall|theta: Subst, word: Seq<EventView>|
                    numeric::source_regex(final(self)@, root as nat, theta, word)
                        == numeric::source_regex(*source, source.root as nat, theta, word))]
    pub(crate) fn append(&mut self, source: &FlatPair<u64>) -> Result<u32, HistoryError> {
        proof_decl! { let ghost before = self@; }
        proof! { reveal(<Tables as View>::view); reveal(dag); reveal(frame); }
        let tests = index(self.tests.len())?;
        let regexes = index(self.regexes.len())?;
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= source.tests@.len(), dag(self@), frame(before, self@),
                dag(before), dag(*source),
                before == old(self)@,
                self.regexes@ == before.regexes@,
                self.tests@.len() == before.tests@.len() + i,
                tests as nat == before.tests@.len(), regexes as nat == before.regexes@.len(),
                tests_copied(*source, self@, tests as nat, i as nat),
            decreases source.tests@.len() - i,
        ))]
        while i < source.tests.len() {
            let copied = match copy_test(&source.tests[i], tests) {
                Ok(copied) => copied,
                Err(error) => {
                    proof! { lemma_frame_languages(before, self@); }
                    return Err(error);
                }
            };
            proof_decl! { let ghost previous = self.tests@; }
            proof! {
                lemma_test_shift_wf(source.tests@[i as int], copied, i as nat, tests as nat);
            }
            self.tests.push(copied);
            proof! {
                assert forall|j: int| 0 <= j < self.tests@.len()
                    implies test_dag(self.tests@[j], j as nat) by {
                    if j < previous.len() { assert(self.tests@[j] == previous[j]); }
                    else { assert(j == previous.len()); }
                }
                assert forall|j: int| 0 <= j < i + 1 implies
                    test_shift(source.tests@[j], self.tests@[(tests + j) as int], tests as nat) by {
                    if j < i { assert(self.tests@[(tests + j) as int] == previous[(tests + j) as int]); }
                }
            }
            i += 1;
        }
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= source.regexes@.len(), dag(self@), frame(before, self@),
                dag(before), dag(*source),
                before == old(self)@,
                self.tests@.len() == before.tests@.len() + source.tests@.len(),
                self.regexes@.len() == before.regexes@.len() + i,
                tests as nat == before.tests@.len(), regexes as nat == before.regexes@.len(),
                tests_copied(*source, self@, tests as nat, source.tests@.len()),
                regexes_copied(*source, self@, tests as nat, regexes as nat, i as nat),
            decreases source.regexes@.len() - i,
        ))]
        while i < source.regexes.len() {
            let copied = match copy_regex(&source.regexes[i], tests, regexes) {
                Ok(copied) => copied,
                Err(error) => {
                    proof! { lemma_frame_languages(before, self@); }
                    return Err(error);
                }
            };
            proof_decl! { let ghost previous = self.regexes@; }
            proof! {
                lemma_regex_shift_wf(source.regexes@[i as int], copied, i as nat,
                    source.tests@.len(), tests as nat, regexes as nat);
            }
            self.regexes.push(copied);
            proof! {
                assert forall|j: int| 0 <= j < self.regexes@.len() implies
                    flat::regex_wf(self.regexes@[j], j as nat, self.tests@.len()) by {
                    if j < previous.len() { assert(self.regexes@[j] == previous[j]); }
                    else { assert(j == previous.len()); }
                }
                assert forall|j: int| 0 <= j < i + 1 implies
                    regex_shift(source.regexes@[j], self.regexes@[(regexes + j) as int],
                        tests as nat, regexes as nat) by {
                    if j < i { assert(self.regexes@[(regexes + j) as int] == previous[(regexes + j) as int]); }
                }
            }
            i += 1;
        }
        proof! { lemma_frame_languages(before, self@); }
        let root = offset(source.root, regexes)?;
        proof! {
            assert forall|theta: Subst, word: Seq<EventView>|
                numeric::source_regex(self@, root as nat, theta, word)
                    == numeric::source_regex(*source, source.root as nat, theta, word) by {
                lemma_regex_copy(*source, self@, tests as nat, regexes as nat,
                    source.regexes@.len(), source.root as nat, theta, word);
            }
        }
        Ok(root)
    }
    /// Appends the source tail and returns its denial language.
    #[verus_spec(result => requires dag(old(self)@), dag(*source),
        source.root < source.regexes@.len(),
        ensures no_internal_error(result),
            result matches Ok(root) ==> root < final(self).regexes@.len()
                && dag(final(self)@)
                && frame(old(self)@, final(self)@)
                && final(self).tests@.len()
                    == old(self).tests@.len() + source.tests@.len()
                && tests_copied(*source, final(self)@,
                    old(self).tests@.len(), source.tests@.len())
                && regexes_copied(*source, final(self)@, old(self).tests@.len(),
                    old(self).regexes@.len(), source.regexes@.len())
                && (forall|index: nat, theta: Subst, word: Seq<EventView>|
                    index < old(self).regexes@.len()
                        ==> numeric::source_regex(old(self)@, index, theta, word)
                            == numeric::source_regex(final(self)@, index, theta, word))
                && forall|theta: Subst, word: Seq<EventView>|
                    numeric::source_regex(final(self)@, root as nat, theta, word)
                        == history_semantics::verify::refinement::semantics::violated_by(
                            mode, numeric::source_regex(*source, source.root as nat, theta, word)))]
    pub(crate) fn denial(
        &mut self,
        source: &FlatPair<u64>,
        mode: RuleMode,
    ) -> Result<u32, HistoryError> {
        let source_root = self.append(source)?;
        match mode {
            RuleMode::Forbid => Ok(source_root),
            RuleMode::Require => {
                proof_decl! { let ghost appended = self@; }
                let root = self.push(FlatRegex::Complement(source_root))?;
                proof! {
                    lemma_frame_languages(appended, self@);
                    assert forall|theta: Subst, word: Seq<EventView>|
                        numeric::source_regex(self@, root as nat, theta, word)
                            == history_semantics::verify::refinement::semantics::violated_by(
                                mode, numeric::source_regex(*source, source.root as nat, theta, word))
                        by {
                        reveal_with_fuel(numeric::source_regex, 1);
                        reveal(history_semantics::verify::refinement::semantics::violated_by);
                        assert(self.regexes@[root as int] == FlatRegex::Complement(source_root));
                        assert(numeric::source_regex(self@, root as nat, theta, word)
                            == !numeric::source_regex(self@, source_root as nat, theta, word));
                        assert(numeric::source_regex(appended, source_root as nat, theta, word)
                            == numeric::source_regex(*source, source.root as nat, theta, word));
                    }
                }
                Ok(root)
            }
        }
    }

    /// Appends one regex node over earlier nodes.
    #[verus_spec(result => requires dag(old(self)@),
        flat::regex_wf(regex, old(self).regexes@.len(), old(self).tests@.len()),
        ensures no_internal_error(result),
            dag(final(self)@), final(self).tests@ == old(self).tests@,
            frame(old(self)@, final(self)@),
            result matches Ok(id) ==> id as nat == old(self).regexes@.len()
                && final(self).regexes@ == old(self).regexes@.push(regex),
            result is Err ==> final(self).regexes@ == old(self).regexes@)]
    pub(crate) fn push(&mut self, regex: FlatRegex) -> Result<u32, HistoryError> {
        proof! {
            reveal(<Tables as View>::view); reveal(dag); reveal(frame);
            reveal(flat::regex_wf); reveal(flat::references_before);
        }
        let id = index(self.regexes.len())?;
        proof_decl! { let ghost previous = self.regexes@; }
        proof_decl! { let ghost previous_tests = self.tests@; }
        proof! {
            reveal(dag); reveal(<Tables as View>::view);
            assert(dag(self@));
            lemma_dag_elim(self@);
            assert(self@.tests@ == previous_tests);
            assert(self@.regexes@ == previous);
            assert(flat::regex_wf(regex, self.regexes@.len(), self.tests@.len()));
            assert forall|i: int| 0 <= i < previous_tests.len() implies
                test_dag(previous_tests[i], i as nat) by {}
            assert forall|i: int| 0 <= i < previous.len() implies
                flat::regex_wf(previous[i], i as nat, previous_tests.len()) by {}
        }
        self.regexes.push(regex);
        proof! {
            reveal(dag); reveal(<Tables as View>::view);
            assert forall|i: int| 0 <= i < self.tests@.len() implies
                test_dag(self.tests@[i], i as nat) by {
                assert(self.tests@[i] == previous_tests[i]);
            }
            assert forall|i: int| 0 <= i < self.regexes@.len() implies
                flat::regex_wf(self.regexes@[i], i as nat, self.tests@.len()) by {
                if i < previous.len() { assert(self.regexes@[i] == previous[i]); }
                else { assert(i == previous.len()); }
            }
            assert(dag(self@));
        }
        Ok(id)
    }

    /// `left ∩ ¬right` as the root of these tables. Heads play no part in a tail's language.
    #[verus_spec(result => requires dag(self@), left < self.regexes@.len(),
        right < self.regexes@.len(),
        ensures no_internal_error(result),
            result matches Ok(pair) ==> dag(pair) && pair.root < pair.regexes@.len()
                && frame(self@, pair)
                && pair.tests@ == self.tests@
                && forall|theta: Subst, word: Seq<EventView>|
                    numeric::source_regex(pair, pair.root as nat, theta, word)
                        == (numeric::source_regex(self@, left as nat, theta, word)
                            && !numeric::source_regex(self@, right as nat, theta, word)))]
    // vstd specifies `Vec::push`, not the `vec!` macro.
    #[allow(clippy::vec_init_then_push)]
    pub(crate) fn difference(self, left: u32, right: u32) -> Result<FlatPair<u64>, HistoryError> {
        proof_decl! { let ghost before = self@; }
        proof! {
            reveal(<Tables as View>::view); reveal(dag); reveal(frame);
            reveal(flat::regex_wf); reveal(flat::references_before);
        }
        let mut tables = self;
        let excluded = tables.push(FlatRegex::Complement(right))?;
        let mut children = Vec::with_capacity(2);
        children.push(left);
        children.push(excluded);
        let root = tables.push(FlatRegex::Intersect(children))?;
        let pair = FlatPair {
            head: tables.head,
            tests: tables.tests,
            regexes: tables.regexes,
            root,
        };
        proof! {
            lemma_frame_languages(before, pair);
            assert(dag(pair));
            assert(pair.root < pair.regexes@.len());
            assert(frame(before, pair));
            assert(pair.regexes@[root as int] == FlatRegex::Intersect(children));
            assert(pair.regexes@[excluded as int] == FlatRegex::Complement(right));
            assert(children@.len() == 2 && children@[0] == left && children@[1] == excluded);
            assert forall|theta: Subst, word: Seq<EventView>|
                numeric::source_regex(pair, pair.root as nat, theta, word)
                    == (numeric::source_regex(before, left as nat, theta, word)
                        && !numeric::source_regex(before, right as nat, theta, word)) by {
                reveal_with_fuel(numeric::source_regex, 2);
                assert(numeric::source_regex(pair, excluded as nat, theta, word)
                    == !numeric::source_regex(pair, right as nat, theta, word));
                assert(numeric::source_regex(pair, pair.root as nat, theta, word)
                    == (numeric::source_regex(pair, left as nat, theta, word)
                        && numeric::source_regex(pair, excluded as nat, theta, word)));
                assert forall|i: int| 0 <= i < 2 implies
                    children@[i] < root by {}
            }
        }
        Ok(pair)
    }
}

#[verus_verify]
#[verus_spec(result => ensures no_internal_error(result),
    result matches Ok(id) ==> id as nat == length as nat,
    result is Err ==> length > u32::MAX)]
fn index(length: usize) -> Result<u32, HistoryError> {
    match u32::try_from(length) {
        Ok(id) => Ok(id),
        Err(_) => Err(HistoryError::graph_index_overflow()),
    }
}

#[verus_verify]
#[verus_spec(result => ensures no_internal_error(result),
    result matches Ok(value) ==> value as nat == id as nat + by as nat,
    result is Err ==> id as nat + by as nat > u32::MAX)]
fn offset(id: u32, by: u32) -> Result<u32, HistoryError> {
    match id.checked_add(by) {
        Some(value) => Ok(value),
        None => Err(HistoryError::graph_index_overflow()),
    }
}

#[verus_verify]
#[verus_spec(result => ensures no_internal_error(result),
    result matches Ok(values) ==> shifted(ids@, values@, by as nat))]
fn shift(ids: &[u32], by: u32) -> Result<Vec<u32>, HistoryError> {
    let mut values = Vec::new();
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= ids@.len(), values@.len() == i,
            forall|j: int| 0 <= j < i ==> values@[j] as nat == ids@[j] as nat + by as nat,
        decreases ids@.len() - i,
    ))]
    while i < ids.len() {
        values.push(offset(ids[i], by)?);
        i += 1;
    }
    Ok(values)
}

#[verus_verify]
#[verus_spec(result => ensures no_internal_error(result),
    result matches Ok(copied) ==> test_shift(*test, copied, by as nat))]
fn copy_test(test: &FlatTest<u64>, by: u32) -> Result<FlatTest<u64>, HistoryError> {
    Ok(match test {
        FlatTest::And(children) => FlatTest::And(shift(children, by)?),
        FlatTest::Or(children) => FlatTest::Or(shift(children, by)?),
        FlatTest::Bool(value) => FlatTest::Bool(*value),
        FlatTest::Atom {
            field,
            term,
            positive,
        } => FlatTest::Atom {
            field: *field,
            term: match term {
                FlatTerm::Constant(value) => FlatTerm::Constant(*value),
                FlatTerm::Variable(variable) => FlatTerm::Variable(*variable),
            },
            positive: *positive,
        },
    })
}

#[verus_verify]
#[verus_spec(result => ensures no_internal_error(result),
    result matches Ok(copied) ==>
        regex_shift(*regex, copied, tests as nat, regexes as nat))]
fn copy_regex(regex: &FlatRegex, tests: u32, regexes: u32) -> Result<FlatRegex, HistoryError> {
    Ok(match regex {
        FlatRegex::Test(test) => FlatRegex::Test(offset(*test, tests)?),
        FlatRegex::Concat(children) => FlatRegex::Concat(shift(children, regexes)?),
        FlatRegex::Union(children) => FlatRegex::Union(shift(children, regexes)?),
        FlatRegex::Intersect(children) => FlatRegex::Intersect(shift(children, regexes)?),
        FlatRegex::Star(child) => FlatRegex::Star(offset(*child, regexes)?),
        FlatRegex::Complement(child) => FlatRegex::Complement(offset(*child, regexes)?),
        FlatRegex::Empty => FlatRegex::Empty,
        FlatRegex::All => FlatRegex::All,
        FlatRegex::Epsilon => FlatRegex::Epsilon,
    })
}
