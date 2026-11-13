#![cfg(feature = "runtime")]

//! T: public executable clients. All semantic clauses range over E and Seq<E>.
//! Capacity is a condition on a RETURNED witness, never a precondition for Holds.
#[cfg(verus_keep_ghost)]
mod proofs {
    use history_analysis::spec::analyzer::{QueryResult, rule_ids, rules_of};
    use history_analysis::{Domains, Inclusion, PolicyAnalyzer, RuleId};
    use history_syntax::{Event, Head, RegexExpr, Rule};
    use junco_core::spec::hypotheses::analyzer_hypotheses;
    use junco_core::spec::{questions as q, semantics as s};
    use junco_core::{CompileError, HistoryError};
    use vstd::prelude::*;
    use vstd::std_specs::cmp::PartialEqSpec;

    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
    /// Instantiate R3's profile minimum at each real instance.
    proof fn lemma_instance_profile_minimum<E: Event>(
        domains: q::Domains<E::Component>, cex: q::Counterexample<E::Component>,
        fails: spec_fn(E, Seq<E>) -> bool,
    )
        requires q::every_instance::<E>(domains, cex, |candidate: E, _history: Seq<E>|
            q::shortest_in_case::<E>(domains, cex.known, candidate, cex.history.len(), fails)),
        ensures forall|candidate: E, history: Seq<E>| q::instance(domains, cex, candidate, history)
            ==> forall|other: E, shorter: Seq<E>| q::in_domains(domains, other, shorter)
                && shorter.len() < history.len() && q::same_profile::<E>(cex.known, candidate, other)
                ==> !fails(other, shorter),
    {
        assert forall|candidate: E, history: Seq<E>| q::instance(domains, cex, candidate, history)
            implies forall|other: E, shorter: Seq<E>| q::in_domains(domains, other, shorter)
                && shorter.len() < history.len() && q::same_profile::<E>(cex.known, candidate, other)
                ==> !fails(other, shorter) by {
            assert(q::shortest_in_case::<E>(domains, cex.known, candidate, cex.history.len(), fails));
        }
    }


    /// A1/A2/A5/A6. Every instance is explicit; only existence/refutation and the
    /// reverse decision implication depend on this counterexample's fresh capacity.
    fn theorem_covered<E: Event>(analyzer: &PolicyAnalyzer<E>, rule: RuleId, by: &[RuleId])
        -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer.wf(), analyzer_hypotheses::<E>(),
        ensures match result {
            Err(error) => !(error is Invariant),
            Ok(value) => match value@ {
                QueryResult::Holds => forall|candidate: E, history: Seq<E>|
                    q::in_domains(analyzer@.domains, candidate, history)
                    && s::rule_violated(analyzer@.rules[rule@ as int], candidate, history)
                    ==> s::policy_denies(rules_of(analyzer@, rule_ids(by@)), candidate, history),
                QueryResult::Counterexample(cex) =>
                    q::counterexample_wf::<E>(analyzer@.domains, cex)
                    && q::known_within(cex, q::knowable_constants(analyzer@.domains, analyzer@.rules))
                    && (forall|candidate: E, history: Seq<E>|
                        q::instance(analyzer@.domains, cex, candidate, history) ==>
                            q::in_domains(analyzer@.domains, candidate, history)
                            && s::rule_violated(analyzer@.rules[rule@ as int], candidate, history)
                            && !s::policy_denies(rules_of(analyzer@, rule_ids(by@)), candidate, history)
                            && (forall|other: E, shorter: Seq<E>|
                                q::in_domains(analyzer@.domains, other, shorter) && shorter.len() < history.len()
                                && q::same_profile::<E>(cex.known, candidate, other)
                                ==> !(s::rule_violated(analyzer@.rules[rule@ as int], other, shorter)
                                    && !s::policy_denies(rules_of(analyzer@, rule_ids(by@)), other, shorter))))
                    && (q::counterexample_capacity::<E>(analyzer@.domains, cex) ==>
                        (exists|candidate: E, history: Seq<E>| q::instance(analyzer@.domains, cex, candidate, history))
                        && !q::covers(analyzer@.domains, rules_of(analyzer@, rule_ids(by@)), analyzer@.rules[rule@ as int])),
                QueryResult::Exhausted => true, // UNIT: deliberately no claim.
                QueryResult::Error(_) => false, // Not a native Ok verdict.
            },
        },
        // Honest conditional iff, not false finite-carrier unconditional completeness.
        result matches Ok(value) ==> ((value@ matches QueryResult::Counterexample(cex) ==>
            q::counterexample_capacity::<E>(analyzer@.domains, cex))
            && !(value@ is Exhausted) ==>
            ((value@ is Holds) == q::covers(analyzer@.domains, rules_of(analyzer@, rule_ids(by@)), analyzer@.rules[rule@ as int]))),
    {
        let result = analyzer.covered(rule, by);
        proof {
            if let Ok(value) = &result {
                rule.lemma_belongs_to(analyzer);
                if let QueryResult::Counterexample(cex) = value@ {
                    lemma_instance_profile_minimum::<E>(analyzer@.domains, cex,
                        |candidate: E, history: Seq<E>| s::rule_violated(analyzer@.rules[rule@ as int], candidate, history)
                            && !s::policy_denies(rules_of(analyzer@, rule_ids(by@)), candidate, history));
                }
                value.lemma_view();
            }
        }
        result
    }

    /// A3/A5/A6. Filtering removes EVERY occurrence of the target id, retaining the
    /// arbitrary order and duplicates of all other ids. An absent target still asks coverage.
    fn theorem_redundant<E: Event>(analyzer: &PolicyAnalyzer<E>, rule: RuleId, policy: &[RuleId])
        -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer.wf(), analyzer_hypotheses::<E>(),
        ensures match result {
            Err(error) => !(error is Invariant),
            Ok(value) => match value@ {
                QueryResult::Holds =>
                    q::covers(analyzer@.domains,
                        rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), analyzer@.rules[rule@ as int])
                    && (forall|candidate: E, history: Seq<E>| q::in_domains(analyzer@.domains, candidate, history)
                        ==> (s::policy_denies(rules_of(analyzer@, rule_ids(policy@)), candidate, history)
                            == s::policy_denies(rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), candidate, history))),
                QueryResult::Counterexample(cex) =>
                    q::counterexample_wf::<E>(analyzer@.domains, cex)
                    && q::known_within(cex, q::knowable_constants(analyzer@.domains, analyzer@.rules))
                    && (forall|candidate: E, history: Seq<E>| q::instance(analyzer@.domains, cex, candidate, history)
                        ==> s::rule_violated(analyzer@.rules[rule@ as int], candidate, history)
                            && !s::policy_denies(rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), candidate, history)
                            && (rule_ids(policy@).contains(rule@) ==>
                                s::policy_denies(rules_of(analyzer@, rule_ids(policy@)), candidate, history))
                            && (forall|other: E, shorter: Seq<E>|
                                q::in_domains(analyzer@.domains, other, shorter) && shorter.len() < history.len()
                                && q::same_profile::<E>(cex.known, candidate, other)
                                ==> !(s::rule_violated(analyzer@.rules[rule@ as int], other, shorter)
                                    && !s::policy_denies(rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), other, shorter))))
                    && (q::counterexample_capacity::<E>(analyzer@.domains, cex) ==>
                        q::has_instance::<E>(analyzer@.domains, cex)
                        && !q::covers(analyzer@.domains,
                            rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), analyzer@.rules[rule@ as int])
                        && (rule_ids(policy@).contains(rule@) ==> !q::redundant_in(analyzer@.domains,
                            rules_of(analyzer@, rule_ids(policy@)), rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@))))),
                QueryResult::Exhausted => true,
                QueryResult::Error(_) => false,
            },
        },
        result matches Ok(value) ==> ((value@ matches QueryResult::Counterexample(cex) ==>
            q::counterexample_capacity::<E>(analyzer@.domains, cex))
            && !(value@ is Exhausted) ==>
            ((value@ is Holds) == q::covers(analyzer@.domains,
                rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), analyzer@.rules[rule@ as int]))),
        result matches Ok(value) ==> (rule_ids(policy@).contains(rule@)
            && (value@ matches QueryResult::Counterexample(cex) ==> q::counterexample_capacity::<E>(analyzer@.domains, cex))
            && !(value@ is Exhausted) ==> ((value@ is Holds) == q::redundant_in(analyzer@.domains,
                rules_of(analyzer@, rule_ids(policy@)), rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@))))),
    {
        let result = analyzer.redundant(rule, policy);
        proof {
            if let Ok(value) = &result {
                value.lemma_view();
                rule.lemma_belongs_to(analyzer);
                assert(history_analysis::spec::analyzer::covered_spec(analyzer@, rule@,
                    q::without_rule(rule_ids(policy@), rule@), value@));
                if let QueryResult::Counterexample(cex) = value@ {
                    lemma_instance_profile_minimum::<E>(analyzer@.domains, cex,
                        |candidate: E, history: Seq<E>| s::rule_violated(analyzer@.rules[rule@ as int], candidate, history)
                            && !s::policy_denies(rules_of(analyzer@, q::without_rule(rule_ids(policy@), rule@)), candidate, history));
                }
            }
        }
        result
    }

    /// A3/A5/A6: ONE selected Q rule j serves both correctness and minimality for
    /// EVERY instance; the existential must not be split into different rule choices.
    fn theorem_at_least_as_strict<E: Event>(analyzer: &PolicyAnalyzer<E>, p: &[RuleId], other: &[RuleId])
        -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer.wf(), analyzer_hypotheses::<E>(),
        ensures match result {
            Err(error) => !(error is Invariant),
            Ok(value) => match value@ {
                QueryResult::Holds => forall|candidate: E, history: Seq<E>|
                    q::in_domains(analyzer@.domains, candidate, history)
                    && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), candidate, history)
                    ==> !s::policy_denies(rules_of(analyzer@, rule_ids(other@)), candidate, history),
                QueryResult::Counterexample(cex) =>
                    q::counterexample_wf::<E>(analyzer@.domains, cex)
                    && q::known_within(cex, q::knowable_constants(analyzer@.domains, analyzer@.rules))
                    && (exists|j: int| 0 <= j < other@.len() && rule_ids(other@)[j] < analyzer@.rules.len()
                        && (forall|candidate: E, history: Seq<E>| q::instance(analyzer@.domains, cex, candidate, history)
                            ==> s::rule_violated(analyzer@.rules[rule_ids(other@)[j] as int], candidate, history)
                                && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), candidate, history)
                                && (forall|other_candidate: E, shorter: Seq<E>|
                                    q::in_domains(analyzer@.domains, other_candidate, shorter) && shorter.len() < history.len()
                                    && q::same_profile::<E>(cex.known, candidate, other_candidate)
                                    ==> !(s::rule_violated(analyzer@.rules[rule_ids(other@)[j] as int], other_candidate, shorter)
                                        && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), other_candidate, shorter)))))
                    && (q::counterexample_capacity::<E>(analyzer@.domains, cex) ==>
                        q::has_instance::<E>(analyzer@.domains, cex)
                        && !q::refines(analyzer@.domains, rules_of(analyzer@, rule_ids(p@)), rules_of(analyzer@, rule_ids(other@)))),
                QueryResult::Exhausted => true,
                QueryResult::Error(_) => false,
            },
        },
        result matches Ok(value) ==> ((value@ matches QueryResult::Counterexample(cex) ==>
            q::counterexample_capacity::<E>(analyzer@.domains, cex))
            && !(value@ is Exhausted) ==> ((value@ is Holds) == q::refines(analyzer@.domains,
                rules_of(analyzer@, rule_ids(p@)), rules_of(analyzer@, rule_ids(other@))))),
    {
        let result = analyzer.at_least_as_strict(p, other);
        proof {
            if let Ok(value) = &result {
                value.lemma_view();
                if let QueryResult::Counterexample(cex) = value@ {
                    let ids = rule_ids(other@);
                    let j = choose|j: int| 0 <= j < ids.len() && ids[j] < analyzer@.rules.len()
                        && q::every_instance::<E>(analyzer@.domains, cex, |candidate: E, history: Seq<E>|
                            s::rule_violated(analyzer@.rules[ids[j] as int], candidate, history)
                                && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), candidate, history))
                        && q::every_instance::<E>(analyzer@.domains, cex, |candidate: E, _history: Seq<E>|
                            q::shortest_in_case::<E>(analyzer@.domains, cex.known, candidate, cex.history.len(),
                                |other_candidate: E, history: Seq<E>|
                                    s::rule_violated(analyzer@.rules[ids[j] as int], other_candidate, history)
                                        && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), other_candidate, history)));
                    lemma_instance_profile_minimum::<E>(analyzer@.domains, cex,
                        |candidate: E, history: Seq<E>| s::rule_violated(analyzer@.rules[ids[j] as int], candidate, history)
                            && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), candidate, history));
                    assert(exists|index: int| 0 <= index < other@.len() && rule_ids(other@)[index] < analyzer@.rules.len()
                        && (forall|candidate: E, history: Seq<E>| q::instance(analyzer@.domains, cex, candidate, history)
                            ==> s::rule_violated(analyzer@.rules[rule_ids(other@)[index] as int], candidate, history)
                                && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), candidate, history)
                                && (forall|other_candidate: E, shorter: Seq<E>|
                                    q::in_domains(analyzer@.domains, other_candidate, shorter) && shorter.len() < history.len()
                                    && q::same_profile::<E>(cex.known, candidate, other_candidate)
                                    ==> !(s::rule_violated(analyzer@.rules[rule_ids(other@)[index] as int], other_candidate, shorter)
                                        && !s::policy_denies(rules_of(analyzer@, rule_ids(p@)), other_candidate, shorter))))) by {
                        assert(0 <= j < other@.len());
                    }
                }
            }
        }
        result
    }

    /// A4/A5: borrowed scoped tails, all real instances, global minimum history length,
    /// exact semantic frame, and capacity-qualified existence/negation.
    fn theorem_tail_included<E: Event>(analyzer: &mut PolicyAnalyzer<E>, head: &Head<E>, left: &RegexExpr<E>, right: &RegexExpr<E>)
        -> (result: Result<Inclusion<E>, CompileError>)
        requires old(analyzer).wf(), analyzer_hypotheses::<E>(),
        ensures final(analyzer).wf(), final(analyzer)@.domains == old(analyzer)@.domains,
            final(analyzer)@.rules == old(analyzer)@.rules,
            match result {
                Err(error) => !(error matches CompileError::Runtime(HistoryError::Invariant { .. })),
                Ok(value) => s::head_tails_wf::<E>(head@, left@, right@) && match value@ {
                    QueryResult::Holds => forall|candidate: E, history: Seq<E>|
                        q::in_domains(old(analyzer)@.domains, candidate, history)
                        && s::head_matches(head@, candidate) && s::lang(left@, head@, candidate, history)
                        ==> s::lang(right@, head@, candidate, history),
                    QueryResult::Counterexample(cex) => q::counterexample_wf::<E>(old(analyzer)@.domains, cex)
                        && q::known_within(cex, q::tail_knowable_constants::<E>(old(analyzer)@.domains, head@, left@, right@))
                        && (forall|candidate: E, history: Seq<E>| q::instance(old(analyzer)@.domains, cex, candidate, history)
                            ==> s::head_matches(head@, candidate) && s::lang(left@, head@, candidate, history)
                                && !s::lang(right@, head@, candidate, history))
                        && (forall|candidate: E, history: Seq<E>| q::in_domains(old(analyzer)@.domains, candidate, history)
                            && history.len() < cex.history.len() && s::head_matches(head@, candidate)
                            && s::lang(left@, head@, candidate, history) ==> s::lang(right@, head@, candidate, history))
                        && (q::counterexample_capacity::<E>(old(analyzer)@.domains, cex) ==>
                            q::has_instance::<E>(old(analyzer)@.domains, cex)
                            && !q::tails_included::<E>(old(analyzer)@.domains, head@, left@, right@)),
                    QueryResult::Exhausted => true,
                    QueryResult::Error(_) => false,
                },
            },
            result matches Ok(value) ==> ((value@ matches QueryResult::Counterexample(cex) ==>
                q::counterexample_capacity::<E>(old(analyzer)@.domains, cex))
                && !(value@ is Exhausted) ==> ((value@ is Holds) == q::tails_included::<E>(
                    old(analyzer)@.domains, head@, left@, right@))),
    {
        let result = analyzer.tail_included(head, left, right);
        proof { if let Ok(value) = &result { value.lemma_view(); } }
        result
    }

    /// Construction and two actual registrations use no private capacity or owner APIs.
    /// Allocation/structural errors remain honest branches, not assumptions of success.
    fn theorem_public_construction<E: Event>(first: &Rule<E>, second: &Rule<E>)
        -> Result<(), CompileError>
        requires analyzer_hypotheses::<E>(),
    {
        let domains = Domains::<E>::infinite();
        let mut analyzer = PolicyAnalyzer::new(domains);
        let first_id = analyzer.add_rule(first)?;
        let second_id = analyzer.add_rule(second)?;
        let mut policy = Vec::new();
        policy.push(second_id);
        policy.push(first_id);
        policy.push(first_id); // Real duplicate id, deliberately non-registration order.
        let _ = theorem_covered(&analyzer, first_id, &policy);
        let _ = theorem_redundant(&analyzer, first_id, &policy);
        let _ = theorem_at_least_as_strict(&analyzer, &policy, &policy);
        let _ = theorem_tail_included(&mut analyzer, &first.head, &first.tail, &second.tail);
        Ok(())
    }

    /// Declared-domain analyzer → monitor bridge, using THREE actual public calls.
    /// P permits ⇒ Q permits (equivalently Q denies ⇒ P denies), only inside D.
    /// No guarantee is asserted for a candidate/history outside the declared domains.
    fn theorem_declared_domain_monitor_bridge<E: Event>(
        analyzer: &PolicyAnalyzer<E>, p: &[RuleId], other: &[RuleId],
        p_monitor: &mut history_semantics::validator::Validator<E>,
        q_monitor: &mut history_semantics::validator::Validator<E>, candidate: &E,
    ) -> (result: (Result<Inclusion<E>, HistoryError>, Result<bool, HistoryError>, Result<bool, HistoryError>))
        requires analyzer.wf(), analyzer_hypotheses::<E>(),
            old(p_monitor).wf(), old(q_monitor).wf(),
            old(p_monitor)@.rules == rules_of(analyzer@, rule_ids(p@)),
            old(q_monitor)@.rules == rules_of(analyzer@, rule_ids(other@)),
            old(p_monitor)@.history == old(q_monitor)@.history,
            q::in_domains(analyzer@.domains, *candidate, old(p_monitor)@.history),
        ensures
            result.0 matches Ok(value) ==> (value@ is Holds && result.1 == Ok(true)
                && result.2 is Ok ==> result.2 == Ok(true)),
            final(p_monitor)@.history == old(p_monitor)@.history,
            final(q_monitor)@.history == old(q_monitor)@.history,
    {
        let analysis = theorem_at_least_as_strict(analyzer, p, other);
        let p_permits = p_monitor.permits(candidate);
        let q_permits = q_monitor.permits(candidate);
        (analysis, p_permits, q_permits)
    }

    /// A declared coordinate cannot consume fresh names, even in a long symbolic history.
    proof fn lemma_declared_coordinate_zero<E: Event>(
        domains: q::Domains<E::Component>, cex: q::Counterexample<E::Component>, coordinate: int,
    )
        requires q::counterexample_wf::<E>(domains, cex),
            0 <= coordinate < history_syntax::spec::events::arity::<E>(),
            domains[coordinate] is Some,
        ensures q::fresh_count(cex, coordinate) == 0,
            q::fresh_capacity::<E>(domains, cex.known, coordinate, q::fresh_count(cex, coordinate)),
    {
        let word = seq![cex.candidate] + cex.history;
        assert forall|name: nat| !q::fresh_names(word, coordinate).contains(name) by {
            q::lemma_fresh_names_member(word, coordinate, name);
            if q::fresh_names(word, coordinate).contains(name) {
                let j = choose|j: int| 0 <= j < word.len() && 0 <= coordinate < word[j].len()
                    && word[j][coordinate] == q::SymbolicValue::Fresh(name);
                if j == 0 {
                    assert(q::symbolic_event_wf::<E>(domains, cex.candidate));
                } else {
                    assert(word[j] == cex.history[j - 1]);
                    assert(q::symbolic_event_wf::<E>(domains, cex.history[j - 1]));
                }
            }
        }
        assert(q::fresh_names(word, coordinate) =~= Set::empty());
        q::lemma_fresh_capacity_zero::<E>(domains, cex.known, coordinate);
    }

    /// S1 regression: bool is an undeclared finite enum, completely covered by its
    /// false/true heads. A returned symbolic refutation MUST fail capacity at bool,
    /// not at the other (declared) coordinate. Exhausted/errors still make no verdict.
    fn theorem_s1_undeclared_finite_enum()
        -> (result: Result<Inclusion<(bool, u8)>, CompileError>)
        requires analyzer_hypotheses::<(bool, u8)>(),
        ensures result matches Ok(value) ==> match value@ {
            QueryResult::Counterexample(cex) => !q::fresh_capacity::<(bool, u8)>(
                seq![None, Some(set![history_syntax::Component2::C1(0u8)])],
                cex.known, 0, q::fresh_count(cex, 0)),
            QueryResult::Holds | QueryResult::Exhausted => true,
            QueryResult::Error(_) => false,
        },
    {
        use history_syntax::{Component, Component2, ComponentPattern, RuleMode};
        let mut values = Vec::new();
        values.push(Component2::C1(0u8));
        let domains = Domains::<(bool, u8)>::infinite().with_domain(Component(1), values);
        let mut analyzer = PolicyAnalyzer::new(domains);
        let mut target_slots = Vec::new();
        target_slots.push(ComponentPattern::Variable(String::new()));
        target_slots.push(ComponentPattern::Constant(Component2::C1(0u8)));
        let target = Rule::new(RuleMode::Forbid, Head(target_slots), RegexExpr::All);
        let mut false_slots = Vec::new();
        false_slots.push(ComponentPattern::Constant(Component2::C0(false)));
        false_slots.push(ComponentPattern::Constant(Component2::C1(0u8)));
        let false_rule = Rule::new(RuleMode::Forbid, Head(false_slots), RegexExpr::All);
        let mut true_slots = Vec::new();
        true_slots.push(ComponentPattern::Constant(Component2::C0(true)));
        true_slots.push(ComponentPattern::Constant(Component2::C1(0u8)));
        let true_rule = Rule::new(RuleMode::Forbid, Head(true_slots), RegexExpr::All);
        let target_id = analyzer.add_rule(&target)?;
        let false_id = analyzer.add_rule(&false_rule)?;
        let true_id = analyzer.add_rule(&true_rule)?;
        let mut by = Vec::new();
        by.push(false_id);
        by.push(true_id);
        let result = analyzer.covered(target_id, &by)?;
        proof {
            result.lemma_view();
            let covering = rules_of(analyzer@, rule_ids(by@));
            assert(covering =~= seq![false_rule, true_rule]);
            assert forall|candidate: (bool, u8), history: Seq<(bool, u8)>|
                q::in_domains(analyzer@.domains, candidate, history)
                    && s::rule_violated(target, candidate, history)
                implies s::policy_denies(covering, candidate, history) by {
                assert(history_syntax::spec::events::event_view(candidate)
                    =~= seq![Component2::C0(candidate.0), Component2::C1(candidate.1)]);
                assert(s::head_matches(target.head@, candidate));
                assert(target.head@.len() == 2);
                assert(target.head@[1] == history_syntax::spec::events::PatternView::Constant(Component2::C1(0u8)));
                assert(history_syntax::spec::events::event_view(candidate)[1]
                    .eq_spec(&Component2::C1(0u8)));
                assert(candidate.1 == 0u8);
                if candidate.0 {
                    assert(s::rule_violated(covering[1], candidate, history));
                } else {
                    assert(s::rule_violated(covering[0], candidate, history));
                }
            }
            if let QueryResult::Counterexample(cex) = result@ {
                lemma_declared_coordinate_zero::<(bool, u8)>(analyzer@.domains, cex, 1);
                assert(q::covers(analyzer@.domains, covering, target));
                assert(!q::counterexample_capacity::<(bool, u8)>(analyzer@.domains, cex));
                assert(!q::fresh_capacity::<(bool, u8)>(analyzer@.domains, cex.known, 0, q::fresh_count(cex, 0)));
            }
        }
        Ok(result)
    }

    }
}

#[cfg(not(verus_keep_ghost))]
#[test]
fn public_queries_have_both_verdicts() {
    use history_analysis::{Domains, Inclusion, PolicyAnalyzer};
    use history_syntax::{Component3, ComponentPattern, Head, RegexExpr, Rule, RuleMode};

    let mut analyzer = PolicyAnalyzer::<(u8, u8, u8)>::new(Domains::infinite());
    let first = Rule::new(
        RuleMode::Forbid,
        Head(vec![
            ComponentPattern::Constant(Component3::C0(1)),
            ComponentPattern::Constant(Component3::C1(2)),
            ComponentPattern::Constant(Component3::C2(3)),
        ]),
        RegexExpr::All,
    );
    let second = Rule::new(
        RuleMode::Require,
        Head(vec![
            ComponentPattern::Constant(Component3::C0(9)),
            ComponentPattern::Constant(Component3::C1(2)),
            ComponentPattern::Constant(Component3::C2(3)),
        ]),
        RegexExpr::Empty,
    );
    let first_id = analyzer.add_rule(&first).expect("first registration");
    let second_id = analyzer.add_rule(&second).expect("second registration");
    assert!(matches!(
        analyzer.covered(first_id, &[first_id]).expect("coverage"),
        Inclusion::Holds
    ));
    assert!(matches!(
        analyzer.covered(first_id, &[]).expect("refutation"),
        Inclusion::Counterexample(_)
    ));
    assert!(matches!(
        analyzer
            .redundant(first_id, &[second_id, first_id, first_id])
            .expect("duplicate removal"),
        Inclusion::Counterexample(_)
    ));
    assert!(matches!(
        analyzer
            .at_least_as_strict(&[first_id, second_id], &[second_id])
            .expect("strictness"),
        Inclusion::Holds
    ));
    assert!(matches!(
        analyzer
            .tail_included(&first.head, &RegexExpr::Empty, &RegexExpr::All)
            .expect("tail inclusion"),
        Inclusion::Holds
    ));
}
