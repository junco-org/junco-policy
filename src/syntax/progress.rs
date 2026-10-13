//! Bounded reuse of exact evaluated-history progress for one runtime rule.
//!
//! A cursor records the normalized residual reached after folding a prefix of one tracked
//! [`History`] owner under one exact candidate substitution. Because a residual is the exact
//! Brzozowski derivative of the tail by that prefix, appending events only requires folding the
//! appended suffix; nullability of the resulting residual is the complete-history verdict. Any
//! truncation changes the owner's revision and conservatively invalidates its cursors, including
//! cursors at the absorbing `All`/`Empty` residuals.

use std::num::NonZeroUsize;

use lru::LruCache;

use crate::history::{History, HistoryId, Revision};
use crate::model::Event;

use super::component::CandidateSubstitution;
use super::node::RegexId;
use super::store::CanonicalStore;
use super::symbolic::{SymbolicDerivativeCache, SymbolicMatcher};

/// Maximum progress cursors retained per runtime rule.
///
/// This bounds only cursor entries, independently of history length. It does not bound the
/// shared canonical regex DAG or the rule's symbolic derivative tables.
pub(crate) const PROGRESS_CACHE_CAPACITY: usize = 16;

/// Residual reached after folding the first `consumed_len` events of one history revision.
#[derive(Clone, Copy)]
struct Progress<'arena, E: Event + 'arena> {
    revision: Revision,
    consumed_len: usize,
    residual: RegexId<'arena, E>,
}

/// Least-recently-used progress cursors keyed by history owner and exact candidate bindings.
pub(crate) struct ProgressCache<'arena, E: Event + 'arena> {
    cursors: LruCache<(HistoryId, CandidateSubstitution<E>), Progress<'arena, E>>,
}

impl<'arena, E: Event + 'arena> ProgressCache<'arena, E> {
    /// Creates an empty cache holding at most [`PROGRESS_CACHE_CAPACITY`] cursors.
    pub(crate) fn new() -> Self {
        Self {
            cursors: LruCache::new(
                NonZeroUsize::new(PROGRESS_CACHE_CAPACITY).expect("progress capacity is nonzero"),
            ),
        }
    }

    /// Returns whether `history` belongs to the language `root` under `substitution`.
    ///
    /// Resumes from a retained cursor when it was recorded for the same owner, bindings, and
    /// revision at a length no greater than the current one; otherwise folds from `root`. Only the
    /// unconsumed suffix is read, and an unchanged history reads no event at all.
    ///
    /// # Preconditions
    /// `root` must be a canonical regex from `store`, and `derivatives` must be the derivative
    /// cache of the rule owning both `root` and this progress cache.
    pub(crate) fn accepts(
        &mut self,
        store: &mut CanonicalStore<'arena, E>,
        derivatives: &mut SymbolicDerivativeCache<'arena, E>,
        root: RegexId<'arena, E>,
        history: &History<E>,
        substitution: &CandidateSubstitution<E>,
    ) -> bool {
        let key = (history.id(), substitution.clone());
        let (mut residual, consumed_len) = match self.cursors.get(&key).copied() {
            Some(progress)
                if progress.revision == history.revision()
                    && progress.consumed_len <= history.len() =>
            {
                (progress.residual, progress.consumed_len)
            }
            _ => (root, 0),
        };
        if consumed_len == history.len() {
            return store.nullable(residual);
        }

        if residual != store.all && residual != store.empty {
            residual = SymbolicMatcher::new(store, derivatives).residual(
                residual,
                history.as_slice()[consumed_len..].iter(),
                substitution,
            );
        }
        self.cursors.put(
            key,
            Progress {
                revision: history.revision(),
                consumed_len: history.len(),
                residual,
            },
        );
        store.nullable(residual)
    }
}

#[cfg(test)]
mod tests {
    use bumpalo::Bump;

    use super::{PROGRESS_CACHE_CAPACITY, ProgressCache};
    use crate::history::History;
    use crate::model::{Action, GitEvent, git_event};
    use crate::syntax::compile::{RuntimeRule, compile_rule};
    use crate::syntax::evaluate::accepts_direct;
    use crate::syntax::source::{
        AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
    };
    use crate::syntax::store::CanonicalStore;
    use crate::syntax::symbolic::{SymbolicDerivativeCache, SymbolicMatcher};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Actor(u32);

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Path(u32);

    const A: Action = Action::Read;
    const B: Action = Action::Edit;
    const X: Action = Action::Diff;

    const ALICE: Actor = Actor(1);
    const BOB: Actor = Actor(2);
    const SRC: Path = Path(7);
    const DOCS: Path = Path(9);

    fn event(actor: Actor, action: Action, path: Path) -> GitEvent<Actor, Path> {
        git_event(actor, action, path)
    }

    fn stage(actor: Actor, path: Path) -> GitEvent<Actor, Path> {
        event(actor, Action::Stage, path)
    }

    fn action_regex(action: Action) -> RegexExpr<GitEvent<Actor, Path>> {
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Action(ComponentPattern::constant(action)),
        ))
    }

    /// One retained rule, derivative cache, and progress cache checked against full replay.
    struct Fixture<'arena> {
        store: CanonicalStore<'arena, GitEvent<Actor, Path>>,
        derivatives: SymbolicDerivativeCache<'arena, GitEvent<Actor, Path>>,
        progress: ProgressCache<'arena, GitEvent<Actor, Path>>,
        rule: RuntimeRule<'arena, GitEvent<Actor, Path>>,
    }

    impl<'arena> Fixture<'arena> {
        /// Compiles a Require rule with a Stage-only `(actor, Stage, resource)` head.
        fn new(arena: &'arena Bump, tail: RegexExpr<GitEvent<Actor, Path>>) -> Self {
            let mut store = CanonicalStore::new(arena);
            let head = Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Action::Stage),
                ComponentPattern::variable("resource"),
            );
            let rule = compile_rule(&mut store, &Rule::new(RuleMode::Require, head, tail)).unwrap();
            let mut derivatives = SymbolicDerivativeCache::new();
            SymbolicMatcher::new(&mut store, &mut derivatives).precompile(rule.tail);
            Self {
                store,
                derivatives,
                progress: ProgressCache::new(),
                rule,
            }
        }

        /// Evaluates through the progress cache and asserts equality with uncached replay.
        fn accepts(
            &mut self,
            history: &History<GitEvent<Actor, Path>>,
            candidate: &GitEvent<Actor, Path>,
        ) -> bool {
            let substitution = self
                .rule
                .head
                .match_candidate(candidate)
                .expect("candidate matches the Stage head");
            let cached = self.progress.accepts(
                &mut self.store,
                &mut self.derivatives,
                self.rule.tail,
                history,
                &substitution,
            );
            let direct = accepts_direct(
                &mut self.store,
                self.rule.tail,
                history.iter(),
                &substitution,
            );
            assert_eq!(cached, direct, "{history:?} with candidate {candidate:?}");
            cached
        }
    }

    /// `a · All · b` over actions.
    fn a_all_b() -> RegexExpr<GitEvent<Actor, Path>> {
        RegexExpr::concat([action_regex(A), RegexExpr::all(), action_regex(B)])
    }

    #[test]
    fn appended_suffixes_advance_the_exact_residual() {
        let arena = Bump::new();
        let mut fixture = Fixture::new(&arena, a_all_b());
        let candidate = stage(ALICE, SRC);
        let mut history = History::new();

        let expected = [false, false, true, true, false, true];
        let appended = [A, B, B, X, B];
        for (prefix, expected) in expected.into_iter().enumerate() {
            if prefix > 0 {
                history.push(event(BOB, appended[prefix - 1], DOCS));
            }
            assert_eq!(history.len(), prefix);
            assert_eq!(fixture.accepts(&history, &candidate), expected);
            assert_eq!(fixture.accepts(&history, &candidate), expected);
        }
    }

    #[test]
    fn equal_length_replacement_invalidates_progress() {
        let arena = Bump::new();
        let mut fixture = Fixture::new(&arena, a_all_b());
        let candidate = stage(ALICE, SRC);
        let mut history = History::from_events([event(ALICE, A, SRC), event(ALICE, B, SRC)]);
        assert!(fixture.accepts(&history, &candidate));

        history.truncate(1);
        history.push(event(ALICE, X, SRC));
        assert!(!fixture.accepts(&history, &candidate));

        let checkpoint = history.checkpoint();
        history.push(event(ALICE, B, SRC));
        assert!(fixture.accepts(&history, &candidate));
        history.rollback(checkpoint);
        assert!(!fixture.accepts(&history, &candidate));
    }

    #[test]
    fn cloned_owners_at_equal_revision_keep_separate_cursors() {
        let arena = Bump::new();
        let mut fixture = Fixture::new(&arena, a_all_b());
        let candidate = stage(ALICE, SRC);
        let empty = History::new();
        let mut first = empty.clone();
        let mut second = empty.clone();
        first.push(event(ALICE, A, SRC));
        second.push(event(ALICE, A, SRC));
        assert!(!fixture.accepts(&first, &candidate));
        assert!(!fixture.accepts(&second, &candidate));

        first.push(event(ALICE, B, SRC));
        second.push(event(ALICE, X, SRC));
        assert!(fixture.accepts(&first, &candidate));
        assert!(!fixture.accepts(&second, &candidate));
        assert!(fixture.accepts(&first, &candidate));
    }

    #[test]
    fn evicted_bindings_recompute_the_same_verdict() {
        let arena = Bump::new();
        let edited_by_actor = RegexExpr::test(TestExpr::and([
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("actor")),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(B)),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Resource(ComponentPattern::variable("resource")),
            ),
        ]));
        let tail = RegexExpr::concat([RegexExpr::all(), edited_by_actor, RegexExpr::all()]);
        let mut fixture = Fixture::new(&arena, tail);
        let history = History::from_events([
            event(ALICE, A, SRC),
            event(ALICE, B, SRC),
            event(BOB, A, SRC),
        ]);

        let first = stage(ALICE, SRC);
        assert!(fixture.accepts(&history, &first));
        let first_key = (
            history.id(),
            fixture.rule.head.match_candidate(&first).unwrap(),
        );
        let others = (1..=PROGRESS_CACHE_CAPACITY).map(|index| Actor(1_000 + index as u32));
        for actor in others {
            assert!(!fixture.accepts(&history, &stage(actor, SRC)));
        }
        assert_eq!(fixture.progress.cursors.len(), PROGRESS_CACHE_CAPACITY);
        assert!(!fixture.progress.cursors.contains(&first_key));

        assert!(fixture.accepts(&history, &first));
        assert!(fixture.progress.cursors.contains(&first_key));
        assert!(!fixture.accepts(&history, &stage(ALICE, DOCS)));
    }
}
