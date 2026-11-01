//! Numeric tables of one search, assembled from the encoded tails of analysed rules.

use alloc::vec::Vec;
use history_syntax::RuleMode;
use junco_core::HistoryError;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTest};

/// Tests and regexes of one search; every reference points backward within its own table.
#[derive(Default)]
pub(crate) struct Tables {
    tests: Vec<FlatTest<u64>>,
    regexes: Vec<FlatRegex>,
}

impl Tables {
    /// Appends `source`'s tables after the existing ones and returns its root.
    pub(crate) fn append(&mut self, source: &FlatPair<u64>) -> Result<u32, HistoryError> {
        let tests = index(self.tests.len())?;
        let regexes = index(self.regexes.len())?;
        for test in &source.tests {
            self.tests.push(match test {
                FlatTest::And(children) => FlatTest::And(shift(children, tests)?),
                FlatTest::Or(children) => FlatTest::Or(shift(children, tests)?),
                FlatTest::Bool(_) | FlatTest::Atom { .. } => test.clone(),
            });
        }
        for regex in &source.regexes {
            self.regexes.push(match regex {
                FlatRegex::Test(test) => FlatRegex::Test(offset(*test, tests)?),
                FlatRegex::Concat(children) => FlatRegex::Concat(shift(children, regexes)?),
                FlatRegex::Union(children) => FlatRegex::Union(shift(children, regexes)?),
                FlatRegex::Intersect(children) => FlatRegex::Intersect(shift(children, regexes)?),
                FlatRegex::Star(child) => FlatRegex::Star(offset(*child, regexes)?),
                FlatRegex::Complement(child) => FlatRegex::Complement(offset(*child, regexes)?),
                FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => regex.clone(),
            });
        }
        offset(source.root, regexes)
    }

    /// Appends the histories a rule with this tail and mode denies: the tail for `Forbid`, its
    /// complement for `Require`.
    pub(crate) fn denial(
        &mut self,
        tail: &FlatPair<u64>,
        mode: RuleMode,
    ) -> Result<u32, HistoryError> {
        let root = self.append(tail)?;
        match mode {
            RuleMode::Forbid => Ok(root),
            RuleMode::Require => self.push(FlatRegex::Complement(root)),
        }
    }

    /// Appends one regex node over earlier nodes.
    pub(crate) fn push(&mut self, regex: FlatRegex) -> Result<u32, HistoryError> {
        let id = index(self.regexes.len())?;
        self.regexes.push(regex);
        Ok(id)
    }

    /// `left ∩ ¬right` as the root of these tables. Heads play no part in a tail's language.
    pub(crate) fn difference(
        mut self,
        left: u32,
        right: u32,
    ) -> Result<FlatPair<u64>, HistoryError> {
        let excluded = self.push(FlatRegex::Complement(right))?;
        let root = self.push(FlatRegex::Intersect(Vec::from([left, excluded])))?;
        Ok(FlatPair {
            head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
            tests: self.tests,
            regexes: self.regexes,
            root,
        })
    }
}

fn index(length: usize) -> Result<u32, HistoryError> {
    u32::try_from(length).map_err(|_| HistoryError::graph_index_overflow())
}

fn offset(id: u32, by: u32) -> Result<u32, HistoryError> {
    id.checked_add(by)
        .ok_or_else(HistoryError::graph_index_overflow)
}

fn shift(ids: &[u32], by: u32) -> Result<Vec<u32>, HistoryError> {
    ids.iter().map(|id| offset(*id, by)).collect()
}
