use bumpalo::Bump;
use hashconsing::BHConsed;
use string_interner::DefaultSymbol;

use crate::model::Action;

use super::pattern::{AtomPattern, Comparison};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CompiledAction<'a> {
    Read,
    Edit,
    Stage,
    Unstage,
    Commit(Option<&'a str>),
    Checkout,
    Stash,
    Diff,
    History,
}

impl<'a> CompiledAction<'a> {
    pub(super) fn from_action(arena: &'a Bump, action: &Action) -> Self {
        match action {
            Action::Read => Self::Read,
            Action::Edit => Self::Edit,
            Action::Stage => Self::Stage,
            Action::Unstage => Self::Unstage,
            Action::Commit { message } => {
                Self::Commit(message.as_deref().map(|m| arena.alloc_str(m) as &str))
            }
            Action::Checkout => Self::Checkout,
            Action::Stash => Self::Stash,
            Action::Diff => Self::Diff,
            Action::History => Self::History,
        }
    }

    pub(super) fn matches(self, action: &Action) -> bool {
        match (self, action) {
            (Self::Read, Action::Read)
            | (Self::Edit, Action::Edit)
            | (Self::Stage, Action::Stage)
            | (Self::Unstage, Action::Unstage)
            | (Self::Checkout, Action::Checkout)
            | (Self::Stash, Action::Stash)
            | (Self::Diff, Action::Diff)
            | (Self::History, Action::History) => true,
            (Self::Commit(expected), Action::Commit { message }) => expected == message.as_deref(),
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TestNode<'a> {
    True,
    False,
    Atom {
        comparison: Comparison,
        pattern: AtomPattern<&'a str, CompiledAction<'a>, &'a [&'a str], DefaultSymbol>,
    },
    And(&'a [TestId<'a>]),
    Or(&'a [TestId<'a>]),
}

pub(crate) type TestId<'a> = BHConsed<'a, TestNode<'a>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RegexNode<'a> {
    Empty,
    All,
    Epsilon,
    Test(TestId<'a>),
    Union(&'a [RegexId<'a>]),
    Concat(&'a [RegexId<'a>]),
    Star(RegexId<'a>),
    Intersect(&'a [RegexId<'a>]),
    Not(RegexId<'a>),
}

pub(crate) type RegexId<'a> = BHConsed<'a, RegexNode<'a>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Test<'a> {
    pub(super) context: u64,
    pub(super) scope: u64,
    pub(super) id: TestId<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Regex<'a> {
    pub(super) context: u64,
    pub(super) scope: u64,
    pub(super) id: RegexId<'a>,
}
