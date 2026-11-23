// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Revision-bound retained cursors and failure-atomic numeric batch evaluation.
//! Graph construction and evaluation never report `WrongHistoryOwner`; typed facades check ownership.

#[cfg(verus_keep_ghost)]
use crate::compiled_rule::verify::numeric_result;
use crate::progress::CompiledPair;
#[cfg(any(test, feature = "test-util"))]
pub use crate::progress::WorkCounters;
#[cfg(verus_keep_ghost)]
use crate::progress::verify as progress;
#[cfg(verus_keep_ghost)]
use crate::verify::history_algebra;
#[cfg(verus_keep_ghost)]
use crate::verify::typed_decision as decision;
use alloc::sync::Arc;
#[cfg(any(test, feature = "test-util"))]
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use history_store::cache::HISTORY_CACHE_CAPACITY;
#[cfg(verus_keep_ghost)]
use history_store::cache::verify::{cursor_key_eq, longer_cached_suffix};
use history_store::cache::{CursorCache, HistoryCursor};
use history_store::history::StoredHistory;
#[cfg(verus_keep_ghost)]
use history_store::history::verify as raw;
use history_store::store::{Event, HistoryStore};
use junco_core::errors::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::kernel::Bindings;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::kernel::{KernelResult, RegexId};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;
}

#[cfg(verus_keep_ghost)]
verus! {
pub mod verify {
    use super::*;
    broadcast use junco_core::kernel::verify::group_kernel_views;
    /// Read-only public predicates keep graph IDs and writable runtime state private.
    pub open(crate) spec fn runtime_wf(runtime: RuleRuntime) -> bool {
        cursor_cache_wf(runtime.pair, runtime.cursors@, runtime.snapshots@)
    }

    pub open(crate) spec fn constructor_result(
        result: Result<RuleRuntime, HistoryError>, store: Arc<HistoryStore>,
        template: junco_core::flat::FlatPair<u64>,
    ) -> bool {
        result != Err(HistoryError::WrongHistoryOwner)
            && (junco_core::flat::verify::structural_wf(template) ==> language::no_invariant_failure(result))
            && (junco_core::flat::verify::structural_wf(template)
                ==> !(result matches Err(HistoryError::InvalidPolicy { .. })))
            && (junco_core::flat::verify::structural_wf(template)
                ==> (result matches Err(error) ==> resource_error(error)))
            && (result matches Ok(runtime) ==> runtime_wf(runtime)
            && runtime.store == store
            && runtime.cursors@ == Seq::<HistoryCursor>::empty()
            && runtime.snapshots@ == HistorySnapshots::empty()
            && crate::compile::verify::regex_correct(
                runtime.pair.store.graph(), template, template.root as nat, runtime.pair.root))
    }

    /// The retained root language, without exposing graph nodes or cache state.
    pub closed spec fn runtime_accepts(
        runtime: RuleRuntime, bindings: language::EventView, events: Seq<language::EventView>,
    ) -> bool {
        model::regex_lang(runtime.pair.store.graph(), bindings, runtime.pair.root@, events)
    }

    pub open(crate) spec fn resume_requires(
        runtime: RuleRuntime, bindings: Bindings, stored: StoredHistory, target_len: usize,
    ) -> bool {
        runtime_wf(runtime)
            && snapshot_compatible(runtime.snapshots@, stored.id(), stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && language::event_wf(bindings@, bindings@.len()) && target_len <= history_store::history::verify::stored_events(&stored).len()
    }

    pub(crate) open spec fn resume_count(
        cursors: Seq<HistoryCursor>, history: usize, revision: u64, bindings: Bindings, target: usize, root: RegexId,
    ) -> nat {
        let key = HistoryCursor { history, revision, bindings, target_len: target,
            consumed: 0, residual: root };
        if exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], key) {
            let i = choose|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], key);
            if cursors[i].revision == revision && cursors[i].target_len == target {
                cursors[i].consumed as nat
            } else { 0 }
        } else { 0 }
    }

    pub open(crate) spec fn advance_start(before: RuleRuntime, start: BatchCursor,
        stored: StoredHistory, bindings: Bindings, target: usize) -> nat {
        if start.consumed > 0 && start.target_len != target {
            resume_count(before.cursors@, stored.id(), stored.revision(), bindings, target, before.pair.root)
        } else { start.consumed as nat }
    }

    pub(super) proof fn lemma_root_suffix(pair: CompiledPair, events: Seq<language::EventView>,
        bindings: language::EventView, target: nat)
        requires progress::pair_wf(pair), target <= events.len(),
        ensures progress::residual_after_suffix(pair, events, bindings, target, 0, pair.root),
    {
        assert(events.subrange(target as int, target as int) =~= Seq::<language::EventView>::empty());
        assert forall|w: Seq<language::EventView>| model::regex_lang(pair.store.graph(), bindings, pair.root@, w)
            == model::regex_lang(pair.store.graph(), bindings, pair.root@, w + Seq::empty()) by {
            assert(w + Seq::<language::EventView>::empty() =~= w);
        }
    }

    pub open(crate) spec fn resume_ensures(
        before: RuleRuntime, after: RuleRuntime, result: BatchCursor,
        bindings: Bindings, stored: StoredHistory, target_len: usize,
    ) -> bool {
        after.store == before.store && after.pair == before.pair && after.cursors@ == before.cursors@
            && after.snapshots@ == before.snapshots@.insert((stored.id(), stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && runtime_wf(after) && result.consumed <= target_len
            && result.target_len == target_len
            && result.consumed == resume_count(before.cursors@, stored.id(), stored.revision(), bindings, target_len, before.pair.root)
            && progress::residual_after_suffix(after.pair, history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)),
                bindings@, target_len as nat, result.consumed as nat, result.residual)
            && batch_matches_snapshot(after.pair, result, stored.id(), stored.revision(), bindings, after.snapshots@)
    }

    pub open(crate) spec fn advance_requires(
        runtime: RuleRuntime, cursor: BatchCursor, bindings: Bindings, stored: StoredHistory,
    ) -> bool {
        runtime_wf(runtime)
            && snapshot_compatible(runtime.snapshots@, stored.id(), stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && batch_matches_snapshot(runtime.pair, cursor, stored.id(), stored.revision(), bindings, runtime.snapshots@)
    }

    pub open(crate) spec fn advance_ensures(
        before: RuleRuntime, after: RuleRuntime, start: BatchCursor, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory,
        target_len: usize, batch_size: usize, result: Result<Option<bool>, HistoryError>,
    ) -> bool {
        result != Err(HistoryError::WrongHistoryOwner)
            && (batch_size > 0 && start.consumed <= target_len
                && target_len <= stored@.events.len() ==> language::no_invariant_failure(result))
            && (batch_size > 0 && start.consumed <= target_len
                && target_len <= stored@.events.len()
                ==> (result matches Err(error) ==> resource_error(error)))
            && runtime_wf(after) && after.store == before.store && progress::pair_frame(before.pair, after.pair)
            && after.snapshots@ == before.snapshots@.insert((stored.id(), stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)))
            && batch_matches_snapshot(after.pair, cursor, stored.id(), stored.revision(), bindings, after.snapshots@)
            && progress::residual_after_suffix(after.pair, stored@.events, bindings@,
                cursor.target_len as nat, cursor.consumed as nat, cursor.residual)
            && (result is Err ==> cursor == start && after.cursors@ == before.cursors@)
            && (result is Ok ==> cursor.target_len == target_len
                && cursor.consumed == language::selected_end(
                    advance_start(before, start, stored, bindings, target_len), target_len as nat, batch_size as nat))
            && (result matches Ok(None) ==> cursor.consumed < target_len)
            && (result matches Ok(Some(answer)) ==> cursor.consumed == target_len
                && answer == model::regex_lang(before.pair.store.graph(), bindings@, before.pair.root@,
                    history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)).take(target_len as int)))
    }

    /// Logical graph IDs and the retained numeric store survive every transaction.
    pub open(crate) spec fn runtime_frame(before: RuleRuntime, after: RuleRuntime) -> bool {
        after.store == before.store && progress::pair_frame(before.pair, after.pair)
    }

    /// Retained graph growth does not change the root language of an earlier runtime.
    pub proof fn lemma_runtime_frame_accepts(
        before: RuleRuntime, after: RuleRuntime,
        bindings: language::EventView, events: Seq<language::EventView>,
    )
        requires runtime_wf(before), runtime_frame(before, after),
        ensures runtime_accepts(before, bindings, events) == runtime_accepts(after, bindings, events),
    {
        hide(language::numeric_lang);
        hide(model::lift_regex);
        reveal(runtime_wf);
        reveal(runtime_frame);
        reveal(runtime_accepts);
        model::lemma_graph_wf_elim(before.pair.store.graph());
        model::lemma_lift_regex_stable(before.pair.store.graph(), after.pair.store.graph(), before.pair.root@);
    }

    /// A failed transaction preserves every previously retained cursor.
    pub open(crate) spec fn cursor_cache_unchanged(before: RuleRuntime, after: RuleRuntime) -> bool {
        after.cursors@ == before.cursors@
    }

    pub proof fn lemma_constructor_runtime_wf(runtime: RuleRuntime, store: Arc<HistoryStore>,
        template: junco_core::flat::FlatPair<u64>)
        requires constructor_result(Ok(runtime), store, template),
        ensures runtime_wf(runtime), runtime.spec_store() == store,
            runtime.spec_snapshots() == HistorySnapshots::empty(),
    {
        reveal(constructor_result);
    }

    /// A newly constructed runtime has not observed any history revision yet.
    pub proof fn lemma_constructor_snapshot_compatible(
        runtime: RuleRuntime, store: Arc<HistoryStore>, template: FlatPair<u64>, stored: StoredHistory,
    )
        requires constructor_result(Ok(runtime), store, template),
        ensures snapshot_compatible(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
    {
        lemma_constructor_runtime_wf(runtime, store, template);
        lemma_snapshot_compatible_intro(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events);
    }

    /// Introduce readiness from public observations, not from readiness itself.
    pub proof fn lemma_resume_requires(
        runtime: RuleRuntime, bindings: Bindings, stored: StoredHistory, target_len: usize,
    )
        requires runtime_wf(runtime),
            snapshot_compatible(runtime.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
            language::event_wf(bindings@, bindings@.len()), target_len <= stored@.events.len(),
        ensures resume_requires(runtime, bindings, stored, target_len),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(resume_requires);
    }

    pub proof fn lemma_resume_can_advance(
        before: RuleRuntime, after: RuleRuntime, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory, target_len: usize,
    )
        requires resume_ensures(before, after, cursor, bindings, stored, target_len),
        ensures advance_requires(after, cursor, bindings, stored), runtime_wf(after),
            runtime_frame(before, after), cursor_cache_unchanged(before, after),
            after.spec_store() == before.spec_store(), cursor_consumed(cursor) <= target_len,
            cursor_target(cursor) == target_len,
            after.spec_snapshots() == before.spec_snapshots().insert(
                (stored.id(), stored.revision()), stored@.events),
            snapshot_compatible(after.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(resume_ensures);
        reveal(advance_requires);
        reveal(snapshot_compatible);
        reveal(runtime_frame);
        reveal(cursor_cache_unchanged);
        reveal(cursor_consumed);
    }

    pub proof fn lemma_advance_result_facts(
        before: RuleRuntime, after: RuleRuntime, start: BatchCursor, cursor: BatchCursor,
        bindings: Bindings, stored: StoredHistory,
        target_len: usize, batch_size: usize, result: Result<Option<bool>, HistoryError>,
    )
        requires advance_ensures(before, after, start, cursor, bindings, stored,
            target_len, batch_size, result),
        ensures runtime_wf(after), runtime_frame(before, after),
            result != Err(HistoryError::WrongHistoryOwner),
            batch_size > 0 && cursor_consumed(start) <= target_len && target_len <= stored@.events.len()
                ==> language::no_invariant_failure(result),
            batch_size > 0 && cursor_consumed(start) <= target_len && target_len <= stored@.events.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            after.spec_store() == before.spec_store(),
            after.spec_snapshots() == before.spec_snapshots().insert(
                (stored.id(), stored.revision()), stored@.events),
            snapshot_compatible(after.spec_snapshots(), stored.id(), stored.revision(), stored@.events),
            advance_requires(after, cursor, bindings, stored),
            result is Err ==> cursor_consumed(cursor) == cursor_consumed(start)
                && cursor_cache_unchanged(before, after),
            result is Ok ==> cursor_target(cursor) == target_len && cursor_consumed(cursor) ==
                language::selected_end(advance_start(before, start, stored, bindings, target_len),
                    target_len as nat, batch_size as nat),
            result matches Ok(None) ==> cursor_consumed(cursor) < target_len,
            result matches Ok(Some(answer)) ==> cursor_consumed(cursor) == target_len
                && answer == runtime_accepts(before, bindings@, stored@.events.take(target_len as int)),
    {
        history_store::history::lemma_stored_history_view(stored);
        reveal(advance_ensures);
        reveal(runtime_frame);
        reveal(cursor_cache_unchanged);
        reveal(cursor_consumed);
        reveal(advance_requires);
        reveal(snapshot_compatible);
        reveal(runtime_accepts);
    }

    pub open(crate) spec fn root_cursor_matches(runtime: RuleRuntime, cursor: BatchCursor) -> bool {
        cursor.consumed == 0 && cursor.target_len == 0 && cursor.residual == runtime.pair.root
    }

    pub open(crate) spec fn cursor_target(cursor: BatchCursor) -> usize {
        cursor.target_len
    }

    pub open(crate) spec fn cursor_consumed(cursor: BatchCursor) -> nat {
        cursor.consumed as nat
    }

    /// Numeric event snapshots keyed by immutable history identity and revision.
    pub type HistorySnapshots = Map<(usize, u64), Seq<language::EventView>>;

    /// Reobserving a revision may extend, but cannot replace, its retained prefix.
    pub closed spec fn snapshot_compatible(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    ) -> bool {
        !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events)
    }

    pub proof fn lemma_snapshot_compatible_intro(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events),
        ensures snapshot_compatible(snapshots, history, revision, events),
    {
        reveal(snapshot_compatible);
    }

    pub proof fn lemma_snapshot_compatible_elim(
        snapshots: HistorySnapshots, history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires snapshot_compatible(snapshots, history, revision, events),
        ensures !snapshots.contains_key((history, revision))
            || snapshots[(history, revision)].is_prefix_of(events),
    {
        reveal(snapshot_compatible);
    }

    /// Actual lifecycle receipts justify reuse even when other writers intervene.
    pub proof fn lemma_snapshot_compatible_lifecycle(
        snapshots: HistorySnapshots, stored: StoredHistory,
        tracked snapshot: &raw::Snapshot, tracked lifecycle: &raw::Lifecycle,
    )
        requires lifecycle.wf(), lifecycle.state() == stored@, snapshot.id() == lifecycle.id(),
            snapshots.contains_key((stored.id(), stored.revision())) ==>
                snapshot.value().revision == stored@.revision
                    && snapshot.value().events == snapshots[(stored.id(), stored.revision())],
        ensures snapshot_compatible(snapshots, stored.id(), stored.revision(), stored@.events),
    {
        history_store::history::lemma_stored_history_view(stored);
        if snapshots.contains_key((stored.id(), stored.revision())) {
            lifecycle.validate(snapshot);
        }
        lemma_snapshot_compatible_intro(snapshots, stored.id(), stored.revision(), stored@.events);
    }

    pub(crate) open spec fn cursor_matches_snapshot(
        pair: CompiledPair, cursor: HistoryCursor, snapshots: HistorySnapshots,
    ) -> bool {
        language::event_wf(cursor.bindings@, cursor.bindings@.len())
            && snapshots.contains_key((cursor.history, cursor.revision))
            && progress::residual_after_suffix(pair, snapshots[(cursor.history, cursor.revision)],
                cursor.bindings@, cursor.target_len as nat, cursor.consumed as nat, cursor.residual)
    }

    pub(crate) open spec fn batch_matches_snapshot(
        pair: CompiledPair, cursor: BatchCursor, history: usize, revision: u64,
        bindings: Bindings, snapshots: HistorySnapshots,
    ) -> bool {
        language::event_wf(bindings@, bindings@.len())
            && ((cursor.consumed == 0 && cursor.target_len == 0 && cursor.residual == pair.root)
                || (snapshots.contains_key((history, revision))
                    && progress::residual_after_suffix(pair, snapshots[(history, revision)],
                        bindings@, cursor.target_len as nat, cursor.consumed as nat, cursor.residual)))
    }

    pub(crate) open spec fn cursor_cache_wf(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    ) -> bool {
        crate::progress::verify::pair_wf(pair)
            && cursors.len() <= HISTORY_CACHE_CAPACITY
            && (forall|i: int| 0 <= i < cursors.len() ==> cursor_matches_snapshot(pair, cursors[i], snapshots))
            && (forall|i: int, j: int| 0 <= i < j < cursors.len()
                ==> !cursor_key_eq(cursors[i], cursors[j]))
    }


    pub(super) proof fn lemma_cursor_remove(
        pair: crate::progress::CompiledPair,
        cursors: Seq<HistoryCursor>, index: int, cursor: HistoryCursor, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), 0 <= index < cursors.len(),
            cursor_key_eq(cursors[index], cursor),
        ensures cursor_cache_wf(pair, cursors.remove(index), snapshots),
            cursors.remove(index).len() < HISTORY_CACHE_CAPACITY,
            forall|i: int| 0 <= i < cursors.remove(index).len()
                ==> !cursor_key_eq(cursors.remove(index)[i], cursor)
                    && cursors.contains(cursors.remove(index)[i]),
    {
        cursors.remove_ensures(index);
        let kept = cursors.remove(index);
        assert forall|i: int| 0 <= i < kept.len() implies cursor_matches_snapshot(pair, kept[i], snapshots)
            && !cursor_key_eq(kept[i], cursor) && cursors.contains(kept[i]) by {
            let original = if i < index { i } else { i + 1 };
            assert(0 <= original < cursors.len());
            assert(kept[i] == cursors[original]);
            assert(original != index);
            assert(cursor_matches_snapshot(pair, cursors[original], snapshots));
            if original < index {
                assert(!cursor_key_eq(cursors[original], cursors[index]));
            } else {
                assert(!cursor_key_eq(cursors[index], cursors[original]));
            }
            assert(!cursor_key_eq(cursors[original], cursor));
            assert(cursors.contains(cursors[original]));
        }
        assert forall|i: int, j: int| 0 <= i < j < kept.len()
            implies !cursor_key_eq(kept[i], kept[j]) by {
            let left = if i < index { i } else { i + 1 };
            let right = if j < index { j } else { j + 1 };
            assert(0 <= left < right < cursors.len());
            assert(left < right);
            assert(kept[i] == cursors[left]);
            assert(kept[j] == cursors[right]);
        }
    }

    pub(super) proof fn lemma_cursor_drop_last(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), cursors.len() > 0,
        ensures cursor_cache_wf(pair, cursors.drop_last(), snapshots),
            forall|i: int| 0 <= i < cursors.drop_last().len()
                ==> cursors.drop_last()[i] == cursors[i] && cursors.contains(cursors.drop_last()[i]),
    {
        assert forall|i: int| 0 <= i < cursors.drop_last().len()
            implies cursors.drop_last()[i] == cursors[i] && cursors.contains(cursors.drop_last()[i]) by {}
        assert forall|i: int, j: int| 0 <= i < j < cursors.drop_last().len()
            implies !cursor_key_eq(cursors.drop_last()[i], cursors.drop_last()[j]) by {
            assert(cursors.drop_last()[i] == cursors[i]);
            assert(cursors.drop_last()[j] == cursors[j]);
        }
    }

    pub(super) proof fn lemma_cursor_prepend(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, cursor: HistoryCursor, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(pair, cursors, snapshots), cursors.len() < HISTORY_CACHE_CAPACITY,
            cursor_matches_snapshot(pair, cursor, snapshots),
            forall|i: int| 0 <= i < cursors.len() ==> !cursor_key_eq(cursors[i], cursor),
        ensures cursor_cache_wf(pair, seq![cursor] + cursors, snapshots),
    {
        let after = seq![cursor] + cursors;
        assert forall|i: int| 0 <= i < after.len() implies cursor_matches_snapshot(pair, after[i], snapshots) by {
            if i == 0 { assert(after[i] == cursor); }
            else { assert(after[i] == cursors[i - 1]); }
        }
        assert forall|i: int, j: int| 0 <= i < j < after.len()
            implies !cursor_key_eq(after[i], after[j]) by {
            assert(after[j] == cursors[j - 1]);
            if i == 0 { assert(after[i] == cursor); }
            else { assert(after[i] == cursors[i - 1]); }
        }
    }

    pub(crate) proof fn lemma_cursor_cache_frame(
        before: CompiledPair, after: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
    )
        requires cursor_cache_wf(before, cursors, snapshots), progress::pair_wf(after),
            progress::pair_frame(before, after),
        ensures cursor_cache_wf(after, cursors, snapshots),
    {
        assert forall|i: int| 0 <= i < cursors.len()
            implies cursor_matches_snapshot(after, cursors[i], snapshots) by {
            let cursor = cursors[i];
            progress::lemma_residual_after_suffix_frame(before, after,
                snapshots[(cursor.history, cursor.revision)], cursor.bindings@,
                cursor.target_len as nat, cursor.consumed as nat, cursor.residual);
        }
    }

    pub(crate) proof fn lemma_cursor_cache_observe(
        pair: CompiledPair, cursors: Seq<HistoryCursor>, snapshots: HistorySnapshots,
        history: usize, revision: u64, events: Seq<language::EventView>,
    )
        requires cursor_cache_wf(pair, cursors, snapshots),
            snapshot_compatible(snapshots, history, revision, events),
        ensures cursor_cache_wf(pair, cursors, snapshots.insert((history, revision), events)),
    {
        let updated = snapshots.insert((history, revision), events);
        assert forall|i: int| 0 <= i < cursors.len()
            implies cursor_matches_snapshot(pair, cursors[i], updated) by {
            let cursor = cursors[i];
            if (cursor.history, cursor.revision) == (history, revision) {
                progress::lemma_residual_after_suffix_history_extends(pair,
                    snapshots[(history, revision)], events, cursor.bindings@,
                    cursor.target_len as nat, cursor.consumed as nat, cursor.residual);
            }
        }
    }
}
}

#[verus_verify]
pub struct RuleRuntime {
    pub(crate) pair: crate::progress::CompiledPair,
    pub(crate) cursors: CursorCache,
    pub(crate) store: Arc<HistoryStore>,
    #[cfg(verus_keep_ghost)]
    pub(crate) snapshots: Ghost<verify::HistorySnapshots>,
}

impl core::fmt::Debug for RuleRuntime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RuleRuntime")
            .field("pair", &self.pair)
            .field("cursors", &self.cursors)
            .finish()
    }
}

#[verus_verify]
impl RuleRuntime {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub open(crate) spec fn spec_store(&self) -> Arc<HistoryStore> { self.store }

        /// Read-only observations used to establish compatibility before evaluation.
        pub open(crate) spec fn spec_snapshots(&self) -> verify::HistorySnapshots { self.snapshots@ }
    }

    /// The numeric store whose records name this runtime's cursor keys.
    #[verus_spec(result => ensures *result == self.spec_store())]
    pub fn store(&self) -> &Arc<HistoryStore> {
        &self.store
    }

    /// Start a replacement graph generation without exposing or fabricating graph IDs.
    #[verus_spec(result => ensures root_cursor_matches(*self, result))]
    pub fn root_cursor(&self) -> BatchCursor {
        proof! { reveal(root_cursor_matches); }
        BatchCursor {
            consumed: 0,
            target_len: 0,
            prior_slot: None,
            residual: self.pair.root,
        }
    }

    #[verus_spec(result => ensures constructor_result(result, *store, *template),
        result != Err(HistoryError::WrongHistoryOwner),
        junco_core::flat::verify::structural_wf(*template) ==> language::no_invariant_failure(result)
            && !(result matches Err(HistoryError::InvalidPolicy { .. }))
            && (result matches Err(error) ==> resource_error(error))) ]
    pub fn new<L: Limits>(
        store: &Arc<HistoryStore>,
        template: &junco_core::flat::FlatPair<u64>,
        precompile: bool,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, HistoryError> {
        proof! { reveal(constructor_result); reveal(runtime_wf); }
        #[cfg_attr(not(feature = "cache"), allow(unused_mut))]
        let mut pair =
            CompiledPair::compile(template, junco_core::limits::MAX_GRAPH_BYTES, limits, world)?;
        #[cfg(feature = "cache")]
        if precompile {
            proof_decl! { let ghost compiled = pair; }
            if let Err(error) = pair.precompile(limits, world) {
                if !matches!(
                    error,
                    HistoryError::GraphBudget { .. } | HistoryError::GraphIndex
                ) {
                    return Err(error);
                }
                drop(pair);
                pair = CompiledPair::compile(
                    template,
                    junco_core::limits::MAX_GRAPH_BYTES,
                    limits,
                    world,
                )?;
            }
            proof! {
                if progress::pair_frame(compiled, pair) {
                    model::lemma_graph_wf_elim(compiled.store.graph());
                    model::lemma_lift_regex_stable(compiled.store.graph(), pair.store.graph(), compiled.root@);
                }
            }
        }
        #[cfg(not(feature = "cache"))]
        let _ = precompile;
        let cursors = CursorCache::new(limits, world)?;
        // The expression macro also supplies the ghost field during Verus's erased Rust check.
        let runtime = Self {
            pair,
            cursors,
            store: Arc::clone(store),
            #[cfg(verus_keep_ghost)]
            snapshots: verus_exec_expr! { Ghost(Map::empty()) },
        };
        Ok(runtime)
    }

    /// Bind the candidate and commit one complete-prefix answer/publication transaction.
    #[verus_verify]
    #[verus_spec(result =>
        requires decision::runtime_represents(*template, *old(self)),
            junco_core::flat::verify::structural_wf(*template),
            snapshot_compatible(old(self).snapshots@, stored.id(), stored.revision(),
                history_store::store::verify::events_view(raw::stored_events(&stored))),
        ensures decision::runtime_represents(*template, *final(self)),
            runtime_wf(*final(self)),
            progress::pair_frame(old(self).pair, final(self).pair),
            final(self).spec_store() == old(self).spec_store(),
            result != Err(HistoryError::WrongHistoryOwner),
            language::no_invariant_failure(result),
            result matches Err(error) ==> resource_error(error),
            result is Err ==> final(self).cursors@ == old(self).cursors@,
            final(self).snapshots@ == old(self).snapshots@
                || final(self).snapshots@ == old(self).snapshots@.insert((stored.id(), stored.revision()),
                    history_store::store::verify::events_view(raw::stored_events(&stored))),
            result != Ok(None) ==> final(self).snapshots@ == old(self).snapshots@.insert(
                (stored.id(), stored.revision()),
                history_store::store::verify::events_view(raw::stored_events(&stored))),
            numeric_result(*template, *request, *stored, result),
            result matches Ok(Some(answer)) ==> exists|bindings: Bindings|
                crate::compile::verify::bindings_match(*template, *request, bindings)
                    && language::event_wf(bindings@, bindings@.len())
                    && answer == model::regex_lang(old(self).pair.store.graph(), bindings@,
                        old(self).pair.root@,
                        history_store::store::verify::events_view(raw::stored_events(&stored))),
    )]
    pub(crate) fn accepts<L: Limits>(
        &mut self,
        template: &FlatPair<u64>,
        request: &Event,
        stored: &StoredHistory,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let bindings = match Self::bindings(template, request) {
            Some(bindings) => bindings,
            None => return Ok(None),
        };
        proof! {
            crate::compile::verify::lemma_bindings_match(*template, *request, bindings);
            history_store::history::lemma_stored_history_view(*stored);
            reveal(runtime_wf);
            reveal(resume_requires);
            reveal(resume_ensures);
            reveal(advance_requires);
            reveal(advance_ensures);
        }
        proof_decl! { let ghost initial_snapshots = self.snapshots@; }
        let target = stored.len();
        let mut cursor = self.resume_cursor(&bindings, stored, target);
        proof! {
            lemma_resume_can_advance(entry, *self, cursor, bindings, *stored, target);
            assert(self.snapshots@ == initial_snapshots.insert((stored.id(), stored.revision()),
                history_store::store::verify::events_view(raw::stored_events(&stored))));
        }
        proof_decl! { let ghost start = cursor; }
        let result = self.advance_cursor(
            &mut cursor,
            &bindings,
            stored,
            target,
            usize::MAX,
            limits,
            world,
        );
        proof! {
            let key = (stored.id(), stored.revision());
            let events = history_store::store::verify::events_view(raw::stored_events(&stored));
            assert(self.snapshots@ == initial_snapshots.insert(key, events).insert(key, events));
            assert(initial_snapshots.insert(key, events).insert(key, events) =~= initial_snapshots.insert(key, events));
            language::lemma_selected_end(start.consumed as nat, target as nat, usize::MAX as nat);
            assert(history_store::store::verify::events_view(raw::stored_events(&stored)).take(target as int)
                =~= history_store::store::verify::events_view(raw::stored_events(&stored)));
            decision::lemma_runtime_frame(*template, entry, *self);
        }
        match result {
            Err(error) => Err(error),
            Ok(Some(answer)) => {
                proof! {
                    assert(exists|witness: Bindings|
                        crate::compile::verify::bindings_match(*template, *request, witness)
                            && language::event_wf(witness@, witness@.len())
                            && answer == crate::compile::verify::source_regex(*template,
                                template.root as nat, witness@,
                                history_store::store::verify::events_view(raw::stored_events(&stored)))) by {
                        assert(crate::compile::verify::bindings_match(*template, *request, bindings));
                    }
                    assert(exists|witness: Bindings|
                        crate::compile::verify::bindings_match(*template, *request, witness)
                            && language::event_wf(witness@, witness@.len())
                            && answer == model::regex_lang(entry.pair.store.graph(), witness@,
                                entry.pair.root@,
                                history_store::store::verify::events_view(raw::stored_events(&stored)))) by {
                        assert(crate::compile::verify::bindings_match(*template, *request, bindings));
                    }
                }
                Ok(Some(answer))
            }
            Ok(None) => {
                proof! { assert(false); }
                Err(HistoryError::invariant(
                    "complete history batch returned no answer",
                ))
            }
        }
    }

    /// Public so hosts can drive bounded batches (Regorus HistoryStep).
    #[verus_spec(result =>
        requires resume_requires(*old(self), *bindings, *stored, target_len),
        ensures resume_ensures(*old(self), *final(self), result, *bindings, *stored, target_len),
    )]
    pub fn resume_cursor(
        &mut self,
        bindings: &Bindings,
        stored: &StoredHistory,
        target_len: usize,
    ) -> BatchCursor {
        proof! { reveal(resume_requires); reveal(resume_ensures); reveal(runtime_wf); }
        let history = stored.id();
        proof! {
            lemma_cursor_cache_observe(self.pair, self.cursors@, self.snapshots@,
                history, stored.revision(), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)));
            *self.snapshots = self.snapshots@.insert((history, stored.revision()), history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored)));
        }
        let key = HistoryCursor { history, revision: stored.revision(), bindings: *bindings,
            target_len, consumed: 0, residual: self.pair.root };
        let mut batch = BatchCursor { target_len, ..self.root_cursor() };
        proof! {
            lemma_root_suffix(self.pair, history_store::store::verify::events_view(raw::stored_events(stored)),
                bindings@, target_len as nat);
        }
        if let Some(index) = key.position(self.cursors.entries()) {
            let cursor = &self.cursors.entries()[index];
            proof! {
                let cursors = self.cursors@;
                assert(exists|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], key)) by {
                    assert(cursor_key_eq(cursors[index as int], key));
                }
                let i = choose|i: int| 0 <= i < cursors.len() && cursor_key_eq(cursors[i], key);
                if i < index { assert(!cursor_key_eq(cursors[i], cursors[index as int])); }
                if i > index { assert(!cursor_key_eq(cursors[index as int], cursors[i])); }
                assert(i == index);
                assert(cursor_matches_snapshot(self.pair, *cursor, self.snapshots@));
            }
            if cursor.revision == key.revision {
                if cursor.target_len == target_len {
                    batch.consumed = cursor.consumed;
                    batch.residual = cursor.residual;
                } else if cursor.consumed == cursor.target_len && cursor.consumed > 0
                    && cursor.consumed < target_len {
                    batch.prior_slot = Some(index);
                }
            }
        }
        batch
    }

    /// Public so hosts can drive bounded batches (Regorus HistoryStep).
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep the locked history transaction inputs explicit."
    )]
    #[expect(clippy::collapsible_if, reason = "Pinned Verus does not support let chains.")]
    #[verus_spec(result =>
        requires advance_requires(*old(self), *old(cursor), *bindings, *stored),
        ensures advance_ensures(*old(self), *final(self), *old(cursor), *final(cursor),
            *bindings, *stored, target_len, batch_size, result),
            result != Err(HistoryError::WrongHistoryOwner),
    )]
    pub fn advance_cursor<L: Limits>(
        &mut self,
        cursor: &mut BatchCursor,
        bindings: &Bindings,
        stored: &StoredHistory,
        target_len: usize,
        batch_size: usize,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof! { reveal(advance_requires); reveal(advance_ensures); reveal(runtime_wf); }
        let history = stored.id();
        proof_decl! { let ghost entry = self.pair; let ghost entry_cursors = self.cursors@; let ghost start = *cursor; }
        proof! {
            let events = history_store::store::verify::events_view(history_store::history::verify::stored_events(&stored));
            lemma_snapshot_compatible_elim(self.snapshots@, history, stored.revision(), events);
            history_store::history::lemma_stored_history_view(*stored);
            if cursor.consumed == 0 && cursor.target_len == 0 && cursor.residual == self.pair.root {
                lemma_root_suffix(self.pair, events, bindings@, 0);
            } else {
                progress::lemma_residual_after_suffix_history_extends(self.pair,
                    self.snapshots@[(history, stored.revision())], events, bindings@,
                    cursor.target_len as nat, cursor.consumed as nat, cursor.residual);
            }
            lemma_cursor_cache_observe(self.pair, self.cursors@, self.snapshots@, history, stored.revision(), events);
            *self.snapshots = self.snapshots@.insert((history, stored.revision()), events);
        }
        if batch_size == 0 || cursor.consumed > target_len || target_len > stored.len() {
            return Err(HistoryError::invariant("invalid history batch bounds"));
        }
        let mut staged = if cursor.target_len == target_len {
            *cursor
        } else if cursor.consumed > 0 {
            proof_decl! { let ghost observed = self.snapshots@; }
            proof! {
                reveal(resume_requires);
                lemma_snapshot_compatible_intro(observed, history, stored.revision(), stored@.events);
            }
            let fresh = self.resume_cursor(bindings, stored, target_len);
            proof! {
                reveal(resume_ensures);
                assert(observed.insert((history, stored.revision()), stored@.events) =~= observed);
            }
            fresh
        } else {
            proof! { lemma_root_suffix(self.pair, stored@.events, bindings@, target_len as nat); }
            BatchCursor { target_len, ..self.root_cursor() }
        };
        let hi = target_len - staged.consumed;
        let mut prior = None;
        if hi > 0 && hi <= batch_size {
            if let Some(index) = staged.prior_slot {
                if let Some(old) = self.cursors.entries().get(index) {
                    if old.history == history && old.revision == stored.revision()
                        && old.bindings == *bindings && old.target_len == old.consumed
                        && old.consumed > 0 && old.consumed < target_len && old.consumed <= hi {
                        proof! { assert(cursor_matches_snapshot(self.pair, *old, self.snapshots@)); }
                        prior = Some((old.consumed, old.residual));
                    }
                }
            }
        }
        let result = staged.advance(
            &mut self.pair,
            stored.as_slice(),
            bindings,
            target_len,
            batch_size,
            prior,
            limits,
            world,
        );
        proof! {
            lemma_cursor_cache_frame(entry, self.pair, entry_cursors, self.snapshots@);
            if result is Err {
                progress::lemma_residual_after_suffix_frame(entry, self.pair, stored@.events,
                    bindings@, start.target_len as nat, start.consumed as nat, start.residual);
            }
        }
        match result {
            Err(error) => Err(error),
            Ok(answer) => {
                let published = HistoryCursor {
                    history,
                    bindings: *bindings,
                    revision: stored.revision(),
                    target_len,
                    consumed: staged.consumed,
                    residual: staged.residual,
                };
                proof! { assert(cursor_matches_snapshot(self.pair, published, self.snapshots@)); }
                self.publish(published);
                *cursor = staged;
                Ok(answer)
            }
        }
    }

    /// Called only after all fallible batch work, while its history is read-locked.
    #[verus_verify]
    #[verus_spec(
        requires cursor_cache_wf(old(self).pair, old(self).cursors@, old(self).snapshots@),
            cursor_matches_snapshot(old(self).pair, cursor, old(self).snapshots@),
        ensures
        final(self).pair == old(self).pair, final(self).store == old(self).store,
        final(self).snapshots@ == old(self).snapshots@,
        cursor_cache_wf(final(self).pair, final(self).cursors@, final(self).snapshots@),
        longer_cached_suffix(old(self).cursors@, cursor) ==> final(self).cursors@ == old(self).cursors@,
        !longer_cached_suffix(old(self).cursors@, cursor) ==> final(self).cursors@.len() > 0
            && final(self).cursors@[0] == cursor,
        forall|i: int| 0 <= i < final(self).cursors@.len()
            ==> final(self).cursors@[i] == cursor || old(self).cursors@.contains(final(self).cursors@[i]),
    )]
    pub(crate) fn publish(&mut self, cursor: HistoryCursor) {
        proof_decl! { let ghost entry = self.cursors@; }
        self.cursors.publish(cursor);
        proof! {
            assert forall|i: int| 0 <= i < self.cursors@.len()
                implies cursor_matches_snapshot(self.pair, self.cursors@[i], self.snapshots@) by {
                if self.cursors@[i] != cursor {
                    assert(entry.contains(self.cursors@[i]));
                    let original = choose|j: int| 0 <= j < entry.len() && entry[j] == self.cursors@[i];
                    assert(cursor_matches_snapshot(self.pair, entry[original], self.snapshots@));
                }
            }
        }
    }
}

#[cfg(any(test, feature = "test-util"))]
impl RuleRuntime {
    /// Read the existing engine counters without exposing mutable graph state.
    pub fn work_counters(&self) -> &WorkCounters {
        &self.pair.work
    }

    pub fn reset_work_events(&mut self) {
        self.pair.reset_work_events();
    }

    pub fn work_events(&self) -> usize {
        self.pair.work_events()
    }

    /// Return keys and committed positions, never graph-local residual IDs.
    pub fn cursor_positions(&self) -> Vec<(usize, Bindings, u64, usize)> {
        self.cursors
            .entries()
            .iter()
            .map(|cursor| {
                (
                    cursor.history,
                    cursor.bindings,
                    cursor.revision,
                    cursor.consumed,
                )
            })
            .collect()
    }

    /// Exchange only byte pressure so replacement tests can restore an old generation.
    pub fn replace_graph_byte_pressure(&mut self, bytes: usize) -> usize {
        self.pair.store.replace_graph_byte_pressure(bytes)
    }

    pub fn set_answer_checkpoint_failure(&mut self, fail: bool) {
        self.pair.set_answer_checkpoint_failure(fail);
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub struct BatchCursor {
    pub(crate) consumed: usize,
    pub(crate) target_len: usize,
    pub(crate) prior_slot: Option<usize>,
    pub(crate) residual: RegexId,
}

impl BatchCursor {
    /// Return the number of events committed backwards from the pinned endpoint.
    #[verus_verify]
    #[verus_spec(result => ensures result == cursor_consumed(*self))]
    pub const fn consumed(&self) -> usize {
        proof! { reveal(cursor_consumed); }
        self.consumed
    }

    /// The same executable transaction is used under the runtime/history locks.
    /// No cursor changes until fold, final answer, and publication checks all succeed.
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep explicit transaction inputs aligned with its verified contract."
    )]
    #[verus_verify]
    #[verus_spec(result =>
        requires
            crate::progress::verify::pair_wf(*old(pair)),
            batch_size > 0 && old(self).consumed <= target_len && target_len <= events@.len() ==>
                old(self).target_len == target_len && crate::progress::verify::residual_after_suffix(
                    *old(pair), history_store::store::verify::events_view(events@), bindings@,
                    target_len as nat, old(self).consumed as nat, old(self).residual),
            prior matches Some((p, cached)) ==> 0 < p < target_len
                && p + old(self).consumed <= target_len
                && target_len - old(self).consumed <= batch_size
                && crate::progress::verify::residual_after_suffix(*old(pair),
                    history_store::store::verify::events_view(events@), bindings@, p as nat, p as nat, cached),
        ensures
            crate::progress::verify::pair_wf(*final(pair)),
            crate::progress::verify::pair_frame(*old(pair), *final(pair)),
            result != Err(HistoryError::WrongHistoryOwner),
            batch_size > 0 && old(self).consumed <= target_len && target_len <= events@.len()
                ==> language::no_invariant_failure(result),
            batch_size > 0 && old(self).consumed <= target_len && target_len <= events@.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result is Err ==> *final(self) == *old(self),
            final(self).target_len == old(self).target_len && final(self).prior_slot == old(self).prior_slot,
            result is Ok ==> old(self).consumed <= final(self).consumed
                && final(self).consumed <= target_len
                && final(self).consumed == junco_core::verify::history_specs::selected_end(old(self).consumed as nat, target_len as nat, batch_size as nat),
            result matches Ok(Some(_)) ==> final(self).consumed == target_len,
            result matches Ok(None) ==> final(self).consumed < target_len,
            result is Ok ==> crate::progress::verify::residual_folds(
                *final(pair), bindings@, old(self).residual,
                history_store::store::verify::events_view(events@).subrange(target_len - final(self).consumed, target_len - old(self).consumed),
                final(self).residual),
            result matches Ok(Some(answer)) ==> answer == junco_core::kernel::verify::regex_lang(
                (*final(pair)).store.graph(), bindings@,
                old(self).residual@, history_store::store::verify::events_view(events@).take(target_len - old(self).consumed)),
            result is Ok ==> crate::progress::verify::residual_after_suffix(
                *final(pair), history_store::store::verify::events_view(events@), bindings@,
                target_len as nat, final(self).consumed as nat, final(self).residual),
            result matches Ok(Some(answer)) ==> answer == junco_core::kernel::verify::regex_lang(
                (*old(pair)).store.graph(), bindings@,
                old(pair).root@, history_store::store::verify::events_view(events@).take(target_len as int)),
    )]
    pub(crate) fn advance<L: Limits>(
        &mut self,
        pair: &mut CompiledPair,
        events: &[Event],
        bindings: &Bindings,
        target_len: usize,
        batch_size: usize,
        prior: Option<(usize, RegexId)>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> KernelResult<Option<bool>> {
        proof_decl! { let ghost entry = *pair; let ghost entry_cursor = *self; }
        if batch_size == 0 || self.consumed > target_len || target_len > events.len() {
            return Err(HistoryError::invariant("invalid history batch bounds"));
        }
        let hi = target_len - self.consumed;
        let count = if batch_size < hi {
            batch_size
        } else {
            hi
        };
        let end = self.consumed + count;
        let lo = target_len - end;
        proof! {
            language::lemma_selected_end(self.consumed as nat, target_len as nat, batch_size as nat);
            assert(end == language::selected_end(self.consumed as nat, target_len as nat, batch_size as nat));
        }
        let split = match prior {
            Some((p, _)) => p,
            None => lo,
        };
        let recent = events
            .get(split..hi)
            .ok_or(HistoryError::invariant("invalid history batch slice"))?;
        proof_decl! { let ghost history = history_store::store::verify::events_view(events@); }
        proof! {
            assert(history_store::store::verify::events_view(recent@) =~= history.subrange(split as int, hi as int));
        }
        let middle = pair.fold(self.residual, recent, bindings, limits, world)?;
        let residual = if let Some((p, cached)) = prior {
            proof_decl! { let ghost after_recent = *pair; }
            let out = if middle == pair.root {
                proof! {
                    crate::progress::verify::lemma_residual_after_suffix_frame(entry, *pair, history, bindings@, p as nat, p as nat, cached);
                }
                cached
            } else {
                let older = events
                    .get(..p)
                    .ok_or(HistoryError::invariant("invalid history batch slice"))?;
                proof! {
                    assert(history_store::store::verify::events_view(older@) =~= history.subrange(0, p as int));
                }
                pair.fold(middle, older, bindings, limits, world)?
            };
            proof! {
                if middle != after_recent.root {
                    crate::progress::verify::lemma_fold_frame(after_recent, *pair, bindings@,
                        self.residual, history.subrange(p as int, hi as int), middle);
                }
                assert forall|w: Seq<language::EventView>| model::regex_lang(pair.store.graph(), bindings@, out@, w)
                    == model::regex_lang(pair.store.graph(), bindings@, self.residual@, w + history.subrange(lo as int, hi as int)) by {
                    let earlier = w + history.subrange(0, p as int);
                    assert(model::regex_lang(pair.store.graph(), bindings@, out@, w)
                        == model::regex_lang(pair.store.graph(), bindings@, middle@, earlier));
                    assert(model::regex_lang(pair.store.graph(), bindings@, middle@, earlier)
                        == model::regex_lang(pair.store.graph(), bindings@, self.residual@,
                            earlier + history.subrange(p as int, hi as int)));
                    assert(earlier + history.subrange(p as int, hi as int) =~= w + history.subrange(lo as int, hi as int));
                }
            }
            out
        } else {
            middle
        };
        let answer = if end == target_len {
            let answer = pair.answer(residual, limits, world)?;
            proof! {
                language::lemma_nullable_iff_nil(model::gsem(bindings@), model::lift_regex((*pair).store.graph(), residual@));
                assert(Seq::<language::EventView>::empty() + history.subrange(lo as int, hi as int) =~= history.take(hi as int));
                assert(model::regex_lang((*pair).store.graph(), bindings@, residual@, Seq::empty())
                    == model::regex_lang((*pair).store.graph(), bindings@, entry_cursor.residual@, history.take(hi as int)));
            }
            Some(answer)
        } else {
            None
        };
        limits.publication_checkpoint()?;
        proof! {
            model::lemma_graph_wf_elim(entry.store.graph());
            model::lemma_lift_regex_stable(entry.store.graph(), (*pair).store.graph(), entry.root@);
            history_algebra::lemma_batch_extends_pinned_suffix(
                entry.store.graph(), (*pair).store.graph(), bindings@,
                entry.root@, entry_cursor.residual@, residual@, history_store::store::verify::events_view(events@),
                target_len as nat, entry_cursor.consumed as nat, end as nat,
            );
            if end == target_len {
                assert(history.subrange(0, target_len as int) =~= history.take(target_len as int));
            }
        }
        // Commit the cursor last so every fallible operation leaves it unchanged.
        self.consumed = end;
        self.residual = residual;
        Ok(answer)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::indexing_slicing)]

    use super::*;
    use alloc::vec;
    use history_syntax::syntax::Component;
    use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
    use junco_core::limits::Unmetered;

    fn runtime(regex: FlatRegex) -> RuleRuntime {
        let store = HistoryStore::new(3);
        let runtime = RuleRuntime::new(
            &store,
            &FlatPair {
                head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
                tests: Vec::new(),
                regexes: vec![regex],
                root: 0,
            },
            false,
            &mut Unmetered,
            &mut ObservationWorld,
        )
        .unwrap();
        assert!(Arc::ptr_eq(runtime.store(), &store));
        runtime
    }

    fn event(store: &HistoryStore, action: &[u8]) -> Event {
        let principal = store
            .intern(
                Component(0),
                b"alice",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let action = store
            .intern(Component(1), action, &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let resource = store
            .intern(Component(2), b"doc", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store.event(&[principal, action, resource]).unwrap()
    }

    #[test]
    fn compiled_pair_uses_send_dependencies() {
        fn assert_send<T: Send>() {}
        assert_send::<CompiledPair>();
        assert_send::<RuleRuntime>();
    }

    #[test]
    fn batch_cursor_ends_and_retained_suffix_are_exact() {
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[event(&store, b"edit"); 7],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let mut runtime = runtime(FlatRegex::All);
        let bindings = Bindings::new(&[0; 3]);
        let mut cursor = runtime.root_cursor();
        for expected in [3, 6, 7] {
            let answer = runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    7,
                    3,
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            assert_eq!(answer, if expected == 7 { Some(true) } else { None });
            assert_eq!(cursor.consumed(), expected);
            assert_eq!(runtime.cursors.entries()[0].consumed, expected);
        }
        let latest = runtime.cursors.entries()[0];
        runtime.publish(HistoryCursor {
            consumed: 1,
            residual: runtime.pair.root,
            ..latest
        });
        assert_eq!(runtime.cursors.entries()[0].consumed, 7);
        assert_eq!(runtime.cursors.entries()[0].residual, latest.residual);
        let warm = runtime.resume_cursor(&bindings, &stored, 7);
        assert_eq!(warm.consumed(), 7);
    }

    #[test]
    fn failed_batch_and_final_answer_never_publish() {
        let mut empty = runtime(FlatRegex::Epsilon);
        let mut cursor = empty.root_cursor();
        let before = cursor;
        let error = cursor
            .advance(
                &mut empty.pair,
                &[],
                &Bindings::new(&[0; 3]),
                1,
                3,
                None,
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap_err();
        assert!(matches!(error, HistoryError::Invariant { .. }));
        assert_eq!(cursor.target_len, before.target_len);
        assert_eq!(cursor.consumed, before.consumed);
        assert_eq!(cursor.residual, before.residual);
        assert!(empty.cursors.entries().is_empty());

        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[event(&store, b"edit"); 2],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let bindings = Bindings::new(&[0; 3]);
        let mut runtime = runtime(FlatRegex::All);
        let mut cursor = runtime.root_cursor();
        assert_eq!(
            runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    2,
                    1,
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            None
        );
        let entry = cursor;
        let retained = runtime.cursors.entries()[0];
        runtime.set_answer_checkpoint_failure(true);
        assert!(matches!(
            runtime.advance_cursor(
                &mut cursor,
                &bindings,
                &stored,
                2,
                1,
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(cursor.target_len, entry.target_len);
        assert_eq!(cursor.consumed, entry.consumed);
        assert_eq!(cursor.residual, entry.residual);
        assert_eq!(runtime.cursors.entries()[0].target_len, retained.target_len);
        assert_eq!(runtime.cursors.entries()[0].consumed, retained.consumed);
        assert_eq!(runtime.cursors.entries()[0].residual, retained.residual);
        runtime.set_answer_checkpoint_failure(false);
        assert_eq!(
            runtime
                .advance_cursor(
                    &mut cursor,
                    &bindings,
                    &stored,
                    2,
                    1,
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            Some(true)
        );
        assert_eq!(runtime.cursors.entries()[0].consumed, 2);
    }

    #[test]
    fn publication_failure_preserves_cursor_and_retained_suffix() {
        struct FailPublication;
        impl Limits for FailPublication {
            fn checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn enforce_memory(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn publication_checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Err(junco_core::limits::LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
            }
        }
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[event(&store, b"edit"); 2],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let mut runtime = runtime(FlatRegex::All);
        let mut cursor = runtime.root_cursor();
        let entry = cursor;
        assert!(matches!(
            runtime.advance_cursor(
                &mut cursor,
                &Bindings::new(&[0; 3]),
                &stored,
                0,
                1,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(cursor.target_len, entry.target_len);
        assert_eq!(cursor.consumed, entry.consumed);
        assert_eq!(cursor.residual, entry.residual);
        assert!(runtime.cursors.entries().is_empty());

        assert_eq!(batch(&mut runtime, &mut cursor, &stored, 1, 1), Some(true));
        let before = cursor;
        let retained = runtime.cursors.entries()[0];
        assert!(matches!(
            runtime.advance_cursor(
                &mut cursor,
                &Bindings::new(&[0; 3]),
                &stored,
                2,
                2,
                &mut FailPublication,
                &mut ObservationWorld,
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(cursor.target_len, before.target_len);
        assert_eq!(cursor.consumed, before.consumed);
        assert_eq!(cursor.residual, before.residual);
        let after = runtime.cursors.entries()[0];
        assert_eq!(after.target_len, retained.target_len);
        assert_eq!(after.consumed, retained.consumed);
        assert_eq!(after.residual, retained.residual);
    }

    #[test]
    fn retained_cursor_lru_is_bounded_and_keeps_recent_histories() {
        let store = HistoryStore::new(3);
        let mut runtime = runtime(FlatRegex::All);
        let mut keys = Vec::new();
        for _ in 0..17 {
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            let record = store.history_record(&history).unwrap();
            let stored = record.read();
            assert_eq!(stored.id(), history.index());
            keys.push(history.index());
            let mut cursor = runtime.root_cursor();
            assert_eq!(
                runtime
                    .advance_cursor(
                        &mut cursor,
                        &Bindings::new(&[0; 3]),
                        &stored,
                        0,
                        3,
                        &mut Unmetered,
                        &mut ObservationWorld
                    )
                    .unwrap(),
                Some(true)
            );
        }
        assert_eq!(runtime.cursors.entries().len(), 16);
        assert_eq!(runtime.cursors.entries()[0].history, keys[16]);
        assert_eq!(runtime.cursors.entries()[15].history, keys[1]);
        assert!(
            runtime
                .cursors
                .entries()
                .iter()
                .all(|cursor| cursor.bindings == Bindings::new(&[0; 3]))
        );
    }

    #[test]
    fn equal_shape_records_never_share_residuals() {
        let store = HistoryStore::new(3);
        let read = event(&store, b"read");
        let edit = event(&store, b"edit");
        let mut runtime = action_runtime(&store, read, edit, FlatRegex::Star(0));
        let mut histories = Vec::new();
        for (event, expected) in [(read, true), (edit, false)] {
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            store
                .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            histories.push((history, expected));
        }
        assert_ne!(histories[0].0.index(), histories[1].0.index());
        let bindings = Bindings::new(&[0; 3]);
        // Cold then warm, in both orders: same length, revision and bindings, distinct keys.
        for order in [[0, 1], [1, 0], [0, 1], [1, 0]] {
            for index in order {
                let (history, expected) = &histories[index];
                let record = store.history_record(history).unwrap();
                let stored = record.read();
                let mut cursor = runtime.resume_cursor(&bindings, &stored, 1);
                let answer = runtime
                    .advance_cursor(
                        &mut cursor,
                        &bindings,
                        &stored,
                        1,
                        1,
                        &mut Unmetered,
                        &mut ObservationWorld,
                    )
                    .unwrap();
                assert_eq!(answer, Some(*expected));
            }
        }
        assert_eq!(runtime.cursors.entries().len(), 2);
    }

    fn action_runtime(
        store: &Arc<HistoryStore>,
        read: Event,
        edit: Event,
        root: FlatRegex,
    ) -> RuleRuntime {
        RuleRuntime::new(
            store,
            &FlatPair {
                head: vec![FlatHead::Any; 3],
                tests: [read, edit]
                    .map(|e| FlatTest::Atom {
                        field: Component(1),
                        term: FlatTerm::Constant(e.component(1)),
                        positive: true,
                    })
                    .to_vec(),
                regexes: vec![FlatRegex::Test(0), FlatRegex::Test(1), root],
                root: 2,
            },
            false,
            &mut Unmetered,
            &mut ObservationWorld,
        )
        .unwrap()
    }

    fn batch(
        runtime: &mut RuleRuntime,
        cursor: &mut BatchCursor,
        stored: &StoredHistory,
        target: usize,
        size: usize,
    ) -> Option<bool> {
        runtime
            .advance_cursor(
                cursor,
                &Bindings::new(&[0; 3]),
                stored,
                target,
                size,
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap()
    }

    #[test]
    fn chronological_batches_pin_the_requested_endpoint() {
        let store = HistoryStore::new(3);
        let read = event(&store, b"read");
        let edit = event(&store, b"edit");
        let mut runtime = action_runtime(&store, read, edit, FlatRegex::Concat(vec![0, 1]));
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(
                &history,
                &[read, edit, event(&store, b"remove")],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let stored = record.read();
        let mut cursor = runtime.root_cursor();
        assert_eq!(batch(&mut runtime, &mut cursor, &stored, 2, 1), None);
        assert_eq!(cursor.consumed(), 1);
        let mut resumed = runtime.resume_cursor(&Bindings::new(&[0; 3]), &stored, 2);
        assert_eq!(resumed.consumed(), 1);
        assert_eq!(batch(&mut runtime, &mut resumed, &stored, 2, 1), Some(true));
        assert_eq!(resumed.consumed(), 2);
        assert_eq!(batch(&mut runtime, &mut resumed, &stored, 3, 1), None);
        assert_eq!(resumed.consumed(), 1);
        assert_eq!(
            batch(&mut runtime, &mut resumed, &stored, 3, 2),
            Some(false)
        );
    }

    #[test]
    fn append_does_not_reuse_a_nonmatching_start_state() {
        let store = HistoryStore::new(3);
        let read = event(&store, b"read");
        let edit = event(&store, b"edit");
        let mut runtime = action_runtime(&store, read, edit, FlatRegex::Concat(vec![0, 1]));
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(&history, &[read], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let mut cursor = runtime.root_cursor();
        assert_eq!(
            batch(&mut runtime, &mut cursor, &record.read(), 1, 1),
            Some(false)
        );
        store
            .append(&history, &[edit], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let stored = record.read();
        let mut cursor = runtime.resume_cursor(&Bindings::new(&[0; 3]), &stored, 2);
        assert_eq!(batch(&mut runtime, &mut cursor, &stored, 2, 2), Some(true));
    }

    #[test]
    fn reused_slot_cannot_substitute_another_history() {
        let store = HistoryStore::new(3);
        let read = event(&store, b"read");
        let edit = event(&store, b"edit");
        let mut runtime = action_runtime(&store, read, edit, FlatRegex::Star(0));
        let x = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let y = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(&x, &[read], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(&y, &[edit], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let rx = store.history_record(&x).unwrap();
        let ry = store.history_record(&y).unwrap();
        let mut cursor = runtime.root_cursor();
        assert_eq!(
            batch(&mut runtime, &mut cursor, &rx.read(), 1, 1),
            Some(true)
        );
        store
            .append(&x, &[read], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let stored = rx.read();
        let mut resumed = runtime.resume_cursor(&Bindings::new(&[0; 3]), &stored, 2);
        let mut other = runtime.root_cursor();
        assert_eq!(
            batch(&mut runtime, &mut other, &ry.read(), 1, 1),
            Some(false)
        );
        assert_eq!(batch(&mut runtime, &mut resumed, &stored, 2, 2), Some(true));
    }
}
