# Encoding helper — progress notes (paused on coordinator request)

File: repo/crates/history-semantics/src/verify/refinement/encoding.rs (only file changed).

## State
- None of the three theorems has verified yet. Everything after `// ===== proofs =====` is draft: the
  previous helper's partial proofs plus my fixes.
- Focus run 1 (`verify::refinement::encoding`) stopped at compile errors, 3 of them, all the same
  kind: `assert forall|c| f(c) matches Some(v) implies ... v ...`: the binding `v`/`k` is not in
  scope after `implies`. Fixed (not re-run) by rewriting both spots (lemma_front_end_denies ~l.336,
  lemma_numeric_genericity ~l.600) to `n_head_field(..., c) is Some implies ... ->Some_0`.
- Verification (SMT) has never been reached, so expect proof failures on the next run.

## Draft contents
- lemma_source_test_local / lemma_source_regex_local / theorem_source_regex_local: induction on
  index. structural_wf gives test_wf (variable atoms reference Bind head components) and
  regex_wf (children < index).
- lemma_front_end_denies<E> / theorem_front_end_denies<E>: composes
  enc::lemma_dsl_later_maps_preservation (DSL head/lang == portable head/lang on the numeric
  template), enc::lemma_topology_wf (structural_wf of the template), numeric::lemma_flat_regex
  with theta := head_bindings(head_view(template), theta), then lemma_source_regex_local
  (bound -> whole theta), then `represents`. The head: portable::head_matches over head codes ==
  n_head_matches. There is no missing side condition that I can see: event_wf(theta) follows from
  the u64 request via event_representation, and maps_wf is a hypothesis.
- lemma_test_rename / lemma_lang_rename / lemma_numeric_genericity / theorem_numeric_genericity:
  structural induction. Concat/Star use enc::lemma_partition_lift with forward/reverse relations
  n_renamed / n_renamed_rev. Constants come from the new n_renaming_ok clause, variables from
  injectivity.

## Next steps
1. Run focus on verify::refinement::encoding and fix the SMT failures, one function at a time
   (`focus.sh verify::refinement::encoding lemma_...`).
2. Likely pitfalls:
   - Recursive spec fns (source_regex, lang, regex_mentions, test_mentions) may need
     `reveal_with_fuel(..., 1)`. compile.rs's lemma_flat_regex does that for portable::lang and
     source_regex.
   - Triggers on recursive calls inside quantifiers do not fire; unfold the parent node first.
   - In lemma_front_end_denies, check that template.head@.len()==3 and n_head_field ==
     head_code(head@[field_index c]) go through. Also check the shape of portable::head_matches;
     it lives in junco-core `flat` verify (path not yet located: crates/junco-core/src/flat/verify.rs
     does not exist; grep for `fn head_matches` under crates/junco-core/src/flat*).
   - In lemma_lang_rename Concat/Star, the `choose` on parts must match the shape of lang's
     definition in history_specs (check that the existential has the same order of conjuncts and
     the same bound).
3. Then run focus on the modules importing encoding items (grep `refinement::encoding` /
   `super::encoding`).
