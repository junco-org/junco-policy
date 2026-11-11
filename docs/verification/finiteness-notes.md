# FiniteMech HANDOFF (copy: /tmp/verus-work2/FiniteMech/repo = /home/zak/work/verus-work2/FiniteMech/repo)

## SESSION 3 (FiniteMech3) — read first
Policy: no full-crate runs; focus every changed module + dependents (HELPERS.md).
DONE (focus 0 errors unless noted in report):
- finite_deriv.rs fixed + registered; dbound/results_bound OPAQUE (reveal in lemmas). New native_bound + lemma_native_future
  (Star clause uses seq![root]; exec proof asserts `vstd::array::spec_array_as_slice(&[this])@ =~= seq![this]`).
- symbolic.rs: derivative_cache_wf entry += fder::dbound; derivative_correct_bounds; derivative_extends carries dbound;
  derivative_step (spinoff+rlimit 40, frame call before head match, per-kind native_bound asserts); child_step requires/ensures
  results_bound; derive invariant/ensures; branch + trait derivative ensures dbound.
  interpret: NEW verify/finite_interp.rs (abstract value-set machine iapply/irun, opaque ipre/istep/iinv, step lemmas per branch);
  interpret_branch/interpret_step ensures `ipre(old,..) ==> istep(final,..)`; interpret invariant + ensures
  `Ok(id) ==> (nf_sum(old,this) ==> tval(final,this,lift(final,id)))`.
- progress.rs: successor_entries_wf += fint::entry_val (opaque); frame lemma; successor ensures entry_val(final, key.transition@, id@).
- refinement/finiteness.rs: theorem_impl_instantiation, lemma_impl_step_abstracts, lemma_impl_step_same, lemma_impl_successor_abstracts.
- normalize.rs: RegexId::star ensures nf; NEW verify/finite_compile.rs; compile.rs (approved) ensures regex_nf(lift root), loop invariants compiled_nf.

Final focus counts (session 3, all 0 errors; default features unless noted): verify::finite_deriv 19, verify::finite_interp 40,
verify::finite_compile 15, verify::refinement::finiteness 19, verify::refinement::search 2, verify::history_examples 14,
symbolic 29, progress 22 (cache features: 26), normalize 87, compile 11, runtime 10.
Remaining: cases_follow(m_impl, cases_of) for the analyzer's search (implementation-link layer) — use
derivative ensures (dbound) + CompiledPair::successor ensures (entry_val) + finiteness::lemma_impl_successor_abstracts;
fold's guard path: lemma_impl_step_same. No ghost per-step chain added to `fold` itself.

## SESSION 2 (FiniteMech2) — read this first; supersedes "Next steps" 1-3 below
DONE + verified (focus runs 0 errors: verify::finite_steps 49, verify::finite_branch 61, verify::finite_trans 29,
verify::finite_collect 17; normalize module: see last run note at bottom of this section):
- finite_trans.rs: `cls_step` Union now `rconst(v) || kids(..)` (constants are in every union class; needed so
  av_union(children) <= av_of(union)); lemma_steps_mono / lemma_tcls_nf / finite_collect::lemma_union_node guarded.
- NEW verify/finite_steps.rs: xnf_task/xnf_tasks/xnf_values, vavs, push_av, run_bound, ite_bound, app_bound
  (with cat_front), OPAQUE xpre/xeffect/xrun/xcfg/xstep (reveal in lemmas; exec context only sees opaque atoms —
  open versions blew rlimit), stability lemmas, generic lemma_effect/_value, node class lemmas
  (lemma_if/union/inter/not/append/const_cls), lemma_const_transitions, lemma_nf_weaken/children, N4':
  lemma_cat_inline / cat_nest / cat_eps / cat_shift / cat_list. Avoid `seq![..]` literals inside triggers
  (use lemma_xnf1/2/3, lemma_rnf_seq2, lemma_tasks_valid1, lemma_any_x_pair).
- NEW verify/finite_branch.rs: one lemma per branch of clean_step/not_step/append_step/pair_step/
  pair_conditionals/fold_step/step (ensures xeffect), lemma_next (frame, ensures xstep), lemma_run_start/step/end,
  entry points lemma_ite_start/lemma_ite_future, lemma_app_future.
- normalize.rs (proof-only): imports fsteps/fbr/ftr/flink/fmach; `collect` trait ensures: moved the
  `all_nf ==> collect_out` conjunct BEFORE the language forall (it was swallowed by the forall — bug from session 1);
  `local_if` ensures `id==a || id==b || transitions[id]==If(test,a,b)`; `if_then_else` ensures
  `nf_sum(then)&&nf_sum(else) ==> ite_bound(final,id,then,else)`; `intersect` ensures
  `all_nf(children) ==> run_bound(final, Fold(children,0), id)`; `not` ensures `nf_sum(this) ==> run_bound(final, Not(this), id)`;
  `append` ensures `nf_sum(this)&&ids_nf(suffix) ==> app_bound(final,id,this,lifts(final,suffix))`;
  clean_step/not_step/append_step/pair_step/pair_conditionals/fold_step/step ensures
  `xpre(old..) ==> xeffect(final..)`; next ensures `xcfg(old..) ==> xstep(final..)`; run invariant `xrun` (+ graph_wf(entry),
  transition_action_valid(entry, shape)) and ensures `xnf_task(old, self@) ==> run_bound(final, self@, id@)`.
  pair_step: added spinoff_prover + rlimit(30); step: rlimit(30).
WIP (NOT registered in verify/mod.rs, file kept): verify/finite_deriv.rs — dbound/fbound/results_bound, lemma_const_lp,
  lemma_dbound_const/test/star/not, lemma_factor_set, lemma_factor_concat(2), lemma_inter_closed, lemma_derive_future.
  Last focus run: 15 verified, 3 errors: lemma_factor_concat (asserts at the `ys =~= es.skip(i+1)` / ids_nf proof, ~l.356-357),
  lemma_factor_concat2 (l.414 cs[i] bound: needs regex_kind_wf_at unfolding of Concat children bounded by root),
  lemma_derive_future (call at ~l.484 to finite_branch::lemma_meet_le_cl: requirement trigger form `(xs[i].x)(w)`).
NEXT (in order): fix finite_deriv (3 lemmas), register it; then symbolic.rs (plan): derivative_cache_wf entry
  `Some(out) => derivative_correct(..) && fder::dbound(g, i, out@)`; derivative_extends: dbound via lemma_dbound_stable
  (reveal derivative_correct for root/out bounds); derivative_step: after the head match, ghost match on
  growth_graph.regexes[this].kind and call lemma_dbound_const/test/star/not (d = cache@[inner]->Some_0); update the two
  cache foralls (resize + slot write) to include dbound; child_step requires/ensures results_bound (lemma_factor_set /
  lemma_factor_concat2 + lemma_results_stable/push); derive scan invariant results_bound, ensures dbound via
  lemma_derive_future called before the tail call; branch + trait derivative ensures dbound.
  Then interpret: abstract run with AV stacks (iapply mirrors symbolic::verify::interp_action: !finish -> push
  AV{x: tval(t)}, finish set -> set_av via nset, Not -> r_not, Append -> ccat), concrete stack = singletons of lifted
  values; invariant nf_sum of task ids + regex_nf of values; ensures `nf_sum(this) ==> tval(final, this, lift(result))`.
  Then successor_entries_wf += `nf_sum(g, key.transition@) ==> tval(g, key.transition@, lift(g, entries[key]@))`, and the
  export lemma: dclass(before,t,lift q) && tval(after,t,lift v) ==> step_abstracts(m_impl(), before, q, after, v)
  (lemma_succ_from_class + stability). instantiation_ok for compiled tails needs nf ensures on RegexId::star/from_test/
  TestId::connective (not/concat/set have link lemmas).

## Done (all verified)
- finite_states.rs: Model.nset relational `spec_fn(bool, Set<S>, S) -> bool`; `nset_shape(inter,xs,u)`;
  `set_states_within/has_set_bound` replaces "set state determined by operands"; nset_closed relational.
  theorem_finite_reachable still proved; toy model adapted.
- refinement/finiteness.rs: theorem_lift_injective, theorem_reachable_states_finite, theorem_items_from_states,
  theorem_model_finitely_many_items (any m with contract + `cases_follow(m, cases_of)` + cases_from_atoms),
  theorem_impl_finitely_many_items (m = m_impl, requires regex_nf(start.state), cases_follow(m_impl, cases_of)).
- finite_impl.rs: m_impl (regex_nf states, r_not, r_cat, relational nset = pre().nset_shape, r_combo,
  gfp lit/prod via `consistent`, g_succ), theorem_impl_contract; lemma_lit_fold / lemma_prod_fold (gfp fold).
- finite_link.rs: lemma_not_link, lemma_concat_link, lemma_set_link (exec constructor postconditions -> m_impl constructors on lifted nf inputs).
- finite_trans.rs: transition class tcls / sum class ycls / values tval as least fixpoints (`lfp`, unfold via lemma_tcls/lemma_ycls/lemma_tval),
  normal form nf_lit/nf_prod/nf_sum, soundness lemma_sum_sound, lemma_succ_from_class (dclass(g,t,p) + tval(g,t,v) => m_impl.succ(p,v)),
  stability lemma_trans_stable.
- finite_machine.rs: abstract values AV {x: class, y: sum class}, ops av_if/av_union/av_meet/av_neg/av_app,
  aapply (mirrors guarded_apply over ActionShape), arun, aref order, monotonicity, lemma_frame, stability
  (lemma_av_stable, lemma_arun_stable), members tpiece/piece_of (+ lemma_tpiece_child/class).
- finite_collect.rs: collect_members (work lists of TransitionMode::collect), elem_ok/elem_flat/collect_out,
  lemma_member_elem, lemma_leaf_elem, lemma_union_node/inter_node, lemma_node_future, lemma_const_out.
- normalize.rs (proof-only): `use crate::verify::finite_collect as fcol;` (cfg ghost);
  TransitionMode::collect ensures+invariant collect_members (when flat/constants start empty);
  TransitionNormalize::constant ensures `transitions[id] == Const(regex@)` (was `is Const`);
  TransitionNormalize::collect ensures `all_nf(old g, ids(children)) ==> collect_out(final g, ids(children), intersect, id@)`.

## Design of the remaining invariant (machine typing)
Single class per transition suffices (literal class == product class for non-sum nodes; Intersect/Not classes are &-closures,
which absorb merged leaves and Clean's rebuilds). No singleton-idempotence of RegexId::set needed.
Per step: `xeffect(g, task, pending, prior, tasks, values)` :=
  pending.is_prefix_of(tasks) && aref(aapply(g, task, avs(g, ids(prior))), arun(g, tasks[pending.len()..], avs(g, ids(values))))
  && xnf_tasks(g, tasks) && xnf_values(g, values)
where xnf_task: Clean/Not ids nf_sum; Append(id,r): nf_sum(id) && regex_nf(lift r); Pair: both nf_sum; Fold terms nf_sum; AppendResult r nf.
run loop invariant: aref(arun(g, [shape], []), arun(g, tasks, avs(values))) + xnf; at end av_le(av_of(g,out), aapply(shape,[])[0]).
Use lemma_frame (next) and lemma_arun_stable (graph growth).

## Next steps
1. local_if: add ensures `id == a || id == b || transitions[id] == If(test@, a@, b@)`; lemma av_le(av_of(out), av_if(av_of a, av_of b)), nf.
2. Add xeffect requires/ensures to clean_step, not_step, append_step, pair_step, pair_conditionals, fold_step, step,
   clean_children, ChildAction::schedule (needs lemma: arun over transition_child_actions(g,id,shape) = pushes in source order);
   next (frame), run (invariant). Per-branch lemmas belong in a new verify file (keep exec proof blocks to calls).
   N4' needed for Append merges: r_cat([w]+ys) == r_cat([w, r_cat(ys)]) for nf (prove from pre().flat; lemma_cat_assoc needs atoms).
3. Entry points: intersect/not/append/if_then_else ensures (class bounds) from run.
4. derivative: strengthen symbolic::verify::derivative_cache_wf with `regex_nf(lift o) ==> dclass(g, out, lift o)`;
   per kind: union (collect union bound + lemma_lit_fold/prod_fold), intersect (meet), not (neg), star/list (app, list_lit with r_cat),
   test/const (ycls consts). Stability under extension via lemma_trans_stable.
5. interpret: ensures tval(g, t, lift(result)) (needs nf leaves: use RegexId::set/not/concat link lemmas).
6. CompiledPair::successor: carry `tval(transition, lift result)` in successor cache entries; then step_abstracts via lemma_succ_from_class.

## Pitfalls
- Never put triggers on recursive calls inside recursive spec bodies (fuel mismatch); use lfp form or index triggers `#![trigger cs[i]]`.
- `#[trigger]` inside closure-call arguments is ignored; use `#![trigger vs[i]]`.
- lfp relations: triggers on `tcls(a,x,v)` don't fire on `(tc(a))(x,v)` terms; assert `tcls(a,x,v) == tcls(b,x,v)` explicitly.
- The edit tool's line anchors shift after earlier hunks in the same call when ranges were read before an insert; re-read before multi-hunk edits.
