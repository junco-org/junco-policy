//! Layer 0: policy semantics over typed component values (paper "Heads, tails, and
//! policy decisions", `sec:rules`, Definitions Rule violation `def:violates` and Policy violation
//! `def:policy-violates`; policy refinement, `sec:policy`; coverage, redundancy, vacuity, appendix
//! `app:policy-reduction`).
//!
//! The valuation `θ` of the paper is the candidate itself; histories are oldest first and never
//! contain the candidate. Tail and test semantics are the existing `junco_core::verify::dsl`
//! semantics, whose component equality is `PartialEqSpec::eq_spec`. A policy is a finite sequence
//! of rules; its order is irrelevant to every predicate below.
use alloc::boxed::Box;
use history_syntax::Comparison;
use history_syntax::syntax::RuleMode;
use history_syntax::verify::dsl::{HeadView, PatternView, RegexView, RuleView, TestView};
use junco_core::verify::dsl as tdsl;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// The status of one rule for a candidate and a history. `Violated` is the paper's rule violation
/// (Definition Rule violation, `def:violates`); `NotFired` is a head that does not unify.
pub enum Status { NotFired, Satisfied, Violated }

/// `mode = require` and the history is outside the tail, or `mode = forbid` and it is inside.
pub open spec fn violated_by(mode: RuleMode, inside: bool) -> bool {
    match mode { RuleMode::Require => !inside, RuleMode::Forbid => inside }
}

pub open spec fn rule_status<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> Status {
    if !tdsl::head_matches(rule.head, candidate) {
        Status::NotFired
    } else if violated_by(rule.mode, tdsl::lang(rule.tail, rule.head, candidate, history)) {
        Status::Violated
    } else {
        Status::Satisfied
    }
}

pub open spec fn rule_denies<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> bool {
    rule_status(rule, candidate, history) is Violated
}

/// A policy denies iff some rule is violated (`sec:rules`).
pub open spec fn policy_denies<C: PartialEq>(
    policy: Seq<RuleView<C>>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> bool {
    exists|i: int| 0 <= i < policy.len() && #[trigger] rule_denies(policy[i], candidate, history)
}

pub open spec fn policy_permits<C: PartialEq>(
    policy: Seq<RuleView<C>>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> bool {
    !policy_denies(policy, candidate, history)
}

// ----- component domains -----

/// The values a component ranges over: all values of its type (`None`), or a declared finite set.
/// The paper assumes every domain infinite ("Product events and component tests", `sec:events`); declared finite domains are an
/// implementation feature (`Domains::with_domain`) outside the paper's theorems.
pub type DomainsView<C> = Seq<Option<Set<C>>>;

pub open spec fn in_domain<T: PartialEq>(domain: Option<Set<T>>, value: T) -> bool {
    match domain {
        None => true,
        Some(values) => exists|w: T| values.contains(w) && value.eq_spec(&w),
    }
}

pub open spec fn event_in<C: PartialEq>(domains: DomainsView<C>, event: Seq<C>) -> bool {
    1 <= domains.len() <= history_syntax::MAX_ARITY && event.len() == domains.len()
        && forall|i: int| 0 <= i < domains.len() ==> in_domain(#[trigger] domains[i], event[i])
}

pub open spec fn history_in<C: PartialEq>(
    domains: DomainsView<C>, history: Seq<Seq<C>>,
) -> bool {
    forall|i: int| 0 <= i < history.len() ==> #[trigger] event_in(domains, history[i])
}

/// Every domain is `None`: candidates and history events range over whole types.
pub open spec fn all_unrestricted<C>(domains: DomainsView<C>) -> bool {
    1 <= domains.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < domains.len() ==> #[trigger] domains[i] is None
}

/// `v` equals no member of `values`.
pub open spec fn misses<T: PartialEq>(values: Set<T>, v: T) -> bool {
    forall|w: T| values.contains(w) ==> !v.eq_spec(&w)
}

pub open spec fn has_missing<T: PartialEq>(values: Set<T>) -> bool {
    exists|v: T| #[trigger] misses(values, v)
}

/// A type with infinitely many `eq_spec`-distinct values: every finite set misses one.
pub open spec fn infinite_type<T: PartialEq>() -> bool {
    forall|values: Set<T>| #[trigger] has_missing(values)
}

/// The paper's hypothesis (`sec:events`; assumed by Lemmas `lem:succ` and `lem:uniform` and
/// Theorem Inclusion search correctness `thm:search`).
pub open spec fn infinite_domains<C: PartialEq>(
    domains: DomainsView<C>,
) -> bool {
    all_unrestricted(domains) && infinite_type::<C>()
}

// ----- well-formed rules -----

/// Head variables have distinct names and every tail variable is the head variable of its own
/// component (`sec:rules`, "a tail whose variables occur in h"; component-locality, `sec:events`).
pub open spec fn rule_wf<C>(rule: RuleView<C>) -> bool {
    1 <= rule.head.len() <= history_syntax::MAX_ARITY && tdsl::head_scoped(rule.head) && tdsl::regex_scoped(rule.tail, rule.head)
}

pub open spec fn head_tails_wf<C>(head: HeadView<C>, left: RegexView<C>, right: RegexView<C>) -> bool {
    1 <= head.len() <= history_syntax::MAX_ARITY && tdsl::head_scoped(head) && tdsl::regex_scoped(left, head) && tdsl::regex_scoped(right, head)
}

// ----- policy questions (`sec:policy`, Definition Policy refinement `def:policy-refinement`, appendix `app:policy-reduction`) -----

/// `P ⊑ Q` over `domains`: every pair permitted by `P` is permitted by `Q`.
pub open spec fn refines<C: PartialEq>(
    domains: DomainsView<C>, p: Seq<RuleView<C>>, q: Seq<RuleView<C>>,
) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(domains, candidate) && history_in(domains, history) && policy_permits(p, candidate, history)
            ==> #[trigger] policy_permits(q, candidate, history)
}

/// `P` covers `rule`: every pair the rule denies is denied by some rule of `P`.
pub open spec fn covers<C: PartialEq>(
    domains: DomainsView<C>, p: Seq<RuleView<C>>, rule: RuleView<C>,
) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(domains, candidate) && history_in(domains, history) && #[trigger] rule_denies(rule, candidate, history)
            ==> policy_denies(p, candidate, history)
}

pub open spec fn never_denies<C: PartialEq>(
    domains: DomainsView<C>, rule: RuleView<C>,
) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(domains, candidate) && history_in(domains, history) ==> !#[trigger] rule_denies(rule, candidate, history)
}

/// The rule denies every candidate it matches, whatever the history.
pub open spec fn always_denies<C: PartialEq>(
    domains: DomainsView<C>, rule: RuleView<C>,
) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(domains, candidate) && history_in(domains, history) && tdsl::head_matches(rule.head, candidate)
            ==> #[trigger] rule_denies(rule, candidate, history)
}

/// For every candidate matching `head`, `L(left) ⊆ L(right)`; both tails read `head`'s variables.
pub open spec fn tails_included<C: PartialEq>(
    domains: DomainsView<C>, head: HeadView<C>, left: RegexView<C>, right: RegexView<C>,
) -> bool {
    forall|candidate: Seq<C>, history: Seq<Seq<C>>|
        event_in(domains, candidate) && history_in(domains, history) && tdsl::head_matches(head, candidate)
            && #[trigger] tdsl::lang(left, head, candidate, history) ==> tdsl::lang(right, head, candidate, history)
}

// ----- theorem statements -----

/// `P ⊑ Q` iff `P` covers every rule of `Q` (appendix `app:policy-reduction`).
pub open spec fn stmt_refines_iff_covers<C: PartialEq>() -> bool {
    forall|domains: DomainsView<C>, p: Seq<RuleView<C>>, q: Seq<RuleView<C>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
}

/// Removing a covered rule changes no decision (appendix `app:policy-reduction`): with `others` the policy
/// without the rule, the two policies deny the same pairs iff `others` covers the rule.
pub open spec fn stmt_redundant_iff_covered<C: PartialEq>() -> bool {
    forall|domains: DomainsView<C>, others: Seq<RuleView<C>>, rule: RuleView<C>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: Seq<C>, history: Seq<Seq<C>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
}

/// Genericity: semantics depends only on which values are equal and on equality with the
/// rules' constants. Hence a property proved for every pair over an infinite domain holds for
/// every pair over any type: map the finitely many values of a pair injectively into the infinite
/// domain, fixing the constants. Stated for one rule; policies follow pointwise.
pub open spec fn renaming_preserves<C: PartialEq>(f: spec_fn(C) -> C, fixed: Set<C>, values: ISet<C>) -> bool {
    &&& forall|x: C, y: C| values.contains(x) && values.contains(y) ==> (#[trigger] f(x).eq_spec(&#[trigger] f(y)) == x.eq_spec(&y))
    &&& forall|x: C, k: C| values.contains(x) && fixed.contains(k) ==> (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k))
}

pub open spec fn rename_event<C>(f: Seq<spec_fn(C) -> C>, e: Seq<C>) -> Seq<C> {
    Seq::new(e.len(), |i: int| f[i](e[i]))
}

pub open spec fn rename_history<C>(f: Seq<spec_fn(C) -> C>, h: Seq<Seq<C>>) -> Seq<Seq<C>> {
    h.map(|i: int, e: Seq<C>| rename_event(f, e))
}

/// The values used at one coordinate of a candidate and its history.
pub open spec fn pair_values<C>(candidate: Seq<C>, history: Seq<Seq<C>>, coordinate: int) -> ISet<C> {
    ISet::new(|x: C| (0 <= coordinate < candidate.len() && x == candidate[coordinate])
        || exists|i: int| 0 <= i < history.len() && 0 <= coordinate < history[i].len()
            && #[trigger] history[i][coordinate] == x)
}

pub open spec fn stmt_genericity<C: PartialEq>() -> bool {
    forall|rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>, f: Seq<spec_fn(C) -> C>|
        rule_wf(rule) && candidate.len() == rule.head.len()
            && (forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len())
            && renamings_preserve(f, rule_constants(rule),
                Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i)))
            ==> (rule_status(rule, candidate, history)
                == #[trigger] rule_status(rule, rename_event(f, candidate), rename_history(f, history)))
}

pub open spec fn pattern_constant<C>(pattern: PatternView<C>) -> Set<C> {
    match pattern { PatternView::Constant(c) => Set::empty().insert(c), PatternView::Variable(_) => Set::empty() }
}

/// A finite union, built from finite sets rather than an unrestricted comprehension.
pub open spec fn constants_union<C>(sets: Seq<Set<C>>) -> Set<C>
    decreases sets.len(),
{
    if sets.len() == 0 { Set::empty() }
    else { constants_union(sets.drop_last()).union(sets.last()) }
}

pub proof fn lemma_constants_union<C>(sets: Seq<Set<C>>, i: int)
    requires 0 <= i < sets.len(),
    ensures sets[i].subset_of(constants_union(sets)),
    decreases sets.len(),
{
    if i < sets.len() - 1 {
        lemma_constants_union(sets.drop_last(), i);
        assert(sets[i] == sets.drop_last()[i]);
    } else {
        assert(sets[i] == sets.last());
    }
}

pub open spec fn test_constant_at<C>(test: TestView<C>, coordinate: int) -> Set<C>
    decreases test,
{
    match test {
        TestView::True | TestView::False => Set::empty(),
        TestView::Atom { pattern, .. } =>
            if coordinate == pattern.component { pattern_constant(pattern.pattern) } else { Set::empty() },
        TestView::And(cs) | TestView::Or(cs) => test_constant_forest(cs, coordinate),
    }
}

pub open spec fn test_constant_forest<C>(tests: Seq<TestView<C>>, coordinate: int) -> Set<C>
    decreases tests,
{
    if tests.len() == 0 { Set::empty() }
    else { test_constant_forest(tests.drop_last(), coordinate).union(test_constant_at(tests.last(), coordinate)) }
}

pub open spec fn test_constants<C>(test: TestView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| test_constant_at(test, j))
}

pub open spec fn regex_constant_at<C>(regex: RegexView<C>, coordinate: int) -> Set<C>
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => Set::empty(),
        RegexView::Test(test) => test_constant_at(test, coordinate),
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => regex_constant_forest(cs, coordinate),
        RegexView::Star(child) | RegexView::Not(child) => regex_constant_at(*child, coordinate),
    }
}

pub open spec fn regex_constant_forest<C>(regexes: Seq<RegexView<C>>, coordinate: int) -> Set<C>
    decreases regexes,
{
    if regexes.len() == 0 { Set::empty() }
    else { regex_constant_forest(regexes.drop_last(), coordinate).union(regex_constant_at(regexes.last(), coordinate)) }
}

pub open spec fn regex_constants<C>(regex: RegexView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| regex_constant_at(regex, j))
}

proof fn lemma_test_constant_forest_index<C>(tests: Seq<TestView<C>>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures test_constant_forest(tests, j) == constants_union(Seq::new(tests.len(), |i: int|
        if 0 <= i < tests.len() { test_constants(tests[i], arity)[j] } else { Set::empty() })),
    decreases tests.len(),
{
    if tests.len() > 0 {
        let prior = tests.drop_last();
        lemma_test_constant_forest_index(prior, arity, j);
        let values = Seq::new(tests.len(), |i: int|
            if 0 <= i < tests.len() { test_constants(tests[i], arity)[j] } else { Set::empty() });
        let prefix = Seq::new(prior.len(), |i: int|
            if 0 <= i < prior.len() { test_constants(prior[i], arity)[j] } else { Set::empty() });
        assert(values.drop_last() =~= prefix);
        assert(values.last() == test_constant_at(tests.last(), j));
    }
}

proof fn lemma_regex_constant_forest_index<C>(regexes: Seq<RegexView<C>>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures regex_constant_forest(regexes, j) == constants_union(Seq::new(regexes.len(), |i: int|
        if 0 <= i < regexes.len() { regex_constants(regexes[i], arity)[j] } else { Set::empty() })),
    decreases regexes.len(),
{
    if regexes.len() > 0 {
        let prior = regexes.drop_last();
        lemma_regex_constant_forest_index(prior, arity, j);
        let values = Seq::new(regexes.len(), |i: int|
            if 0 <= i < regexes.len() { regex_constants(regexes[i], arity)[j] } else { Set::empty() });
        let prefix = Seq::new(prior.len(), |i: int|
            if 0 <= i < prior.len() { regex_constants(prior[i], arity)[j] } else { Set::empty() });
        assert(values.drop_last() =~= prefix);
        assert(values.last() == regex_constant_at(regexes.last(), j));
    }
}

/// One coordinate of a test's constants, with recursive calls left at their own fuel level.
pub proof fn lemma_test_constants_index<C>(test: TestView<C>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures test_constants(test, arity)[j] == match test {
        TestView::True | TestView::False => Set::empty(),
        TestView::Atom { pattern, .. } =>
            if j == pattern.component { pattern_constant(pattern.pattern) } else { Set::empty() },
        TestView::And(cs) | TestView::Or(cs) => constants_union(Seq::new(cs.len(), |i: int|
            if 0 <= i < cs.len() { test_constants(cs[i], arity)[j] } else { Set::empty() })),
    },
{
    reveal_with_fuel(test_constant_at, 2);
    match test {
        TestView::And(cs) | TestView::Or(cs) => lemma_test_constant_forest_index(cs, arity, j),
        _ => {},
    }
}

/// The analogous indexed unfolding for regex constants.
pub proof fn lemma_regex_constants_index<C>(regex: RegexView<C>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures regex_constants(regex, arity)[j] == match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => Set::empty(),
        RegexView::Test(test) => test_constants(test, arity)[j],
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) =>
            constants_union(Seq::new(cs.len(), |i: int|
                if 0 <= i < cs.len() { regex_constants(cs[i], arity)[j] } else { Set::empty() })),
        RegexView::Star(child) | RegexView::Not(child) => regex_constants(*child, arity)[j],
    },
{
    reveal_with_fuel(regex_constant_at, 2);
    match regex {
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) =>
            lemma_regex_constant_forest_index(cs, arity, j),
        _ => {},
    }
}

pub open spec fn head_constants<C>(head: HeadView<C>) -> Seq<Set<C>> {
    head.map(|i: int, pattern: PatternView<C>| pattern_constant(pattern))
}

/// Exact finite constants of the head and tail, separately at every coordinate.
pub open spec fn rule_constants<C>(rule: RuleView<C>) -> Seq<Set<C>> {
    Seq::new(rule.head.len(), |i: int|
        regex_constants(rule.tail, rule.head.len())[i].union(head_constants(rule.head)[i]))
}


// ----- proofs -----

/// Appending a rule to a policy adds exactly that rule's denials.
pub proof fn lemma_policy_denies_push<C: PartialEq>(
    policy: Seq<RuleView<C>>, rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
)
    ensures
        policy_denies(policy.push(rule), candidate, history)
            == (policy_denies(policy, candidate, history) || rule_denies(rule, candidate, history)),
{
    let q = policy.push(rule);
    if policy_denies(policy, candidate, history) {
        let i = choose|i: int| 0 <= i < policy.len() && #[trigger] rule_denies(policy[i], candidate, history);
        assert(q[i] == policy[i]);
        assert(rule_denies(q[i], candidate, history));
    }
    if rule_denies(rule, candidate, history) {
        let n = policy.len() as int;
        assert(q[n] == rule);
        assert(rule_denies(q[n], candidate, history));
    }
    if policy_denies(q, candidate, history) {
        let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_denies(q[i], candidate, history);
        if i < policy.len() {
            assert(q[i] == policy[i]);
            assert(rule_denies(policy[i], candidate, history));
        }
    }
}

pub proof fn theorem_refines_iff_covers<C: PartialEq>()
    ensures stmt_refines_iff_covers::<C>(),
{
    assert forall|domains: DomainsView<C>, p: Seq<RuleView<C>>, q: Seq<RuleView<C>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
    by {
        if refines(domains, p, q) {
            assert forall|i: int| 0 <= i < q.len() implies covers(domains, p, #[trigger] q[i]) by {
                assert forall|candidate: Seq<C>, history: Seq<Seq<C>>|
                    event_in(domains, candidate) && history_in(domains, history)
                        && #[trigger] rule_denies(q[i], candidate, history)
                    implies policy_denies(p, candidate, history) by {
                    assert(policy_denies(q, candidate, history));
                    assert(!policy_permits(q, candidate, history));
                }
            }
        }
        if forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i]) {
            assert forall|candidate: Seq<C>, history: Seq<Seq<C>>|
                event_in(domains, candidate) && history_in(domains, history) && policy_permits(p, candidate, history)
                implies #[trigger] policy_permits(q, candidate, history) by {
                if policy_denies(q, candidate, history) {
                    let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_denies(q[i], candidate, history);
                    assert(covers(domains, p, q[i]));
                }
            }
        }
    }
}

pub proof fn theorem_redundant_iff_covered<C: PartialEq>()
    ensures stmt_redundant_iff_covered::<C>(),
{
    assert forall|domains: DomainsView<C>, others: Seq<RuleView<C>>, rule: RuleView<C>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: Seq<C>, history: Seq<Seq<C>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
    by {
        if covers(domains, others, rule) {
            assert forall|candidate: Seq<C>, history: Seq<Seq<C>>|
                event_in(domains, candidate) && history_in(domains, history)
                implies (#[trigger] policy_denies(others.push(rule), candidate, history)
                    == policy_denies(others, candidate, history)) by {
                lemma_policy_denies_push(others, rule, candidate, history);
            }
        }
        if forall|candidate: Seq<C>, history: Seq<Seq<C>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
        {
            assert forall|candidate: Seq<C>, history: Seq<Seq<C>>|
                event_in(domains, candidate) && history_in(domains, history) && #[trigger] rule_denies(rule, candidate, history)
                implies policy_denies(others, candidate, history) by {
                lemma_policy_denies_push(others, rule, candidate, history);
                assert(policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history));
            }
        }
    }
}

// ----- genericity -----

/// Every component lies in its corresponding value set, at exactly that arity.
pub open spec fn values_in<C>(e: Seq<C>, values: Seq<ISet<C>>) -> bool {
    e.len() == values.len() && forall|i: int| 0 <= i < e.len() ==> #[trigger] values[i].contains(e[i])
}

pub open spec fn word_values_in<C>(w: Seq<Seq<C>>, values: Seq<ISet<C>>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] values_in(w[i], values)
}

pub open spec fn renamings_preserve<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, fixed: Seq<Set<C>>, values: Seq<ISet<C>>,
) -> bool {
    f.len() == fixed.len() && values.len() == fixed.len()
        && forall|i: int| 0 <= i < f.len() ==> renaming_preserves(#[trigger] f[i], fixed[i], values[i])
}

pub open spec fn rename_parts<C>(f: Seq<spec_fn(C) -> C>, parts: Seq<Seq<Seq<C>>>) -> Seq<Seq<Seq<C>>> {
    parts.map(|i: int, part: Seq<Seq<C>>| rename_history(f, part))
}

pub proof fn lemma_renaming_mono<T: PartialEq>(f: spec_fn(T) -> T, small: Set<T>, big: Set<T>, values: ISet<T>)
    requires
        renaming_preserves(f, big, values),
        forall|x: T| #[trigger] small.contains(x) ==> big.contains(x),
    ensures renaming_preserves(f, small, values),
{
    assert forall|x: T, k: T| values.contains(x) && small.contains(k)
        implies (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k)) by {
        assert(big.contains(k));
    }
}

pub proof fn lemma_renamings_mono<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, small: Seq<Set<C>>, big: Seq<Set<C>>, values: Seq<ISet<C>>,
)
    requires renamings_preserve(f, big, values), small.len() == big.len(),
        forall|i: int| 0 <= i < small.len() ==> #[trigger] small[i].subset_of(big[i]),
    ensures renamings_preserve(f, small, values),
{
    assert forall|i: int| 0 <= i < f.len() implies renaming_preserves(#[trigger] f[i], small[i], values[i]) by {
        assert(small[i].subset_of(big[i]));
        assert forall|x: C| #[trigger] small[i].contains(x) implies big[i].contains(x) by {}
        lemma_renaming_mono(f[i], small[i], big[i], values[i]);
    }
}

pub proof fn lemma_head_pattern_rename<T: PartialEq>(pattern: PatternView<T>, f: spec_fn(T) -> T, fixed: Set<T>, values: ISet<T>, x: T)
    requires
        renaming_preserves(f, fixed, values),
        values.contains(x),
        forall|k: T| #[trigger] pattern_constant(pattern).contains(k) ==> fixed.contains(k),
    ensures tdsl::head_pattern_matches(pattern, f(x)) == tdsl::head_pattern_matches(pattern, x),
{
    if let PatternView::Constant(k) = pattern {
        assert(pattern_constant(pattern).contains(k));
        assert(f(x).eq_spec(&k) == x.eq_spec(&k));
    }
}

pub proof fn lemma_comparison_rename<T: PartialEq>(
    comparison: Comparison, pattern: PatternView<T>, head: PatternView<T>, f: spec_fn(T) -> T,
    fixed: Set<T>, values: ISet<T>, c: T, e: T,
)
    requires
        renaming_preserves(f, fixed, values),
        values.contains(c),
        values.contains(e),
        forall|k: T| #[trigger] pattern_constant(pattern).contains(k) ==> fixed.contains(k),
    ensures
        tdsl::comparison_sem(comparison, f(e), tdsl::resolve_pattern(pattern, head, f(c)))
            == tdsl::comparison_sem(comparison, e, tdsl::resolve_pattern(pattern, head, c)),
{
    match pattern {
        PatternView::Constant(k) => {
            assert(pattern_constant(pattern).contains(k));
            assert(f(e).eq_spec(&k) == e.eq_spec(&k));
        },
        PatternView::Variable(_) => {
            assert(f(e).eq_spec(&f(c)) == e.eq_spec(&c));
        },
    }
}

pub proof fn lemma_test_rename<C: PartialEq>(
    test: TestView<C>, head: HeadView<C>, candidate: Seq<C>, event: Seq<C>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires renamings_preserve(f, test_constants(test, head.len()), values),
        values_in(candidate, values), values_in(event, values),
    ensures tdsl::test_sem(test, head, rename_event(f, candidate), rename_event(f, event))
        == tdsl::test_sem(test, head, candidate, event),
    decreases test,
{
    let rc = rename_event(f, candidate);
    let re = rename_event(f, event);
    match test {
        TestView::True | TestView::False => {},
        TestView::Atom { comparison, pattern } => {
            let j = pattern.component as int;
            if j < head.len() {
                lemma_test_constants_index(test, head.len(), j);
                assert(test_constants(test, head.len())[j] == pattern_constant(pattern.pattern));
                lemma_comparison_rename(comparison, pattern.pattern, head[j], f[j],
                    test_constants(test, head.len())[j], values[j], candidate[j], event[j]);
            }
        },
        TestView::And(cs) | TestView::Or(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                tdsl::test_sem(cs[i], head, rc, re) == tdsl::test_sem(cs[i], head, candidate, event) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] test_constants(cs[i], head.len())[j].subset_of(test_constants(test, head.len())[j]) by {
                    lemma_test_constants_index(test, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { test_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == test_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, test_constants(cs[i], head.len()), test_constants(test, head.len()), values);
                lemma_test_rename(cs[i], head, candidate, event, f, values);
            }
        },
    }
}

/// Renaming commutes with flattening.
pub proof fn lemma_flatten_rename<C>(
    f: Seq<spec_fn(C) -> C>, parts: Seq<Seq<Seq<C>>>,
)
    ensures rename_history(f, parts.flatten()) == rename_parts(f, parts).flatten(),
    decreases parts.len(),
{
    let rp = rename_parts(f, parts);
    if parts.len() == 0 {
        assert(rename_history(f, parts.flatten()) =~= rp.flatten());
    } else {
        lemma_flatten_rename(f, parts.drop_first());
        assert(rp.drop_first() =~= rename_parts(f, parts.drop_first()));
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(rename_history(f, a + b) =~= rename_history(f, a) + rename_history(f, b));
        assert(rp.first() == rename_history(f, a));
    }
}

/// A word whose renaming is split into parts splits into parts with those renamings.
pub proof fn lemma_unflatten_rename<C>(
    f: Seq<spec_fn(C) -> C>, rparts: Seq<Seq<Seq<C>>>,
    w: Seq<Seq<C>>,
) -> (parts: Seq<Seq<Seq<C>>>)
    requires rparts.flatten() == rename_history(f, w),
    ensures
        parts.len() == rparts.len(),
        parts.flatten() == w,
        forall|i: int| 0 <= i < parts.len() ==> rename_history(f, #[trigger] parts[i]) == rparts[i],
    decreases rparts.len(),
{
    if rparts.len() == 0 {
        assert(w =~= Seq::<Seq<C>>::empty());
        Seq::empty()
    } else {
        let first = rparts.first();
        let rest = rparts.drop_first();
        let k = first.len() as int;
        let rw = rename_history(f, w);
        assert(rw == first + rest.flatten());
        let w0 = w.subrange(0, k);
        let w1 = w.subrange(k, w.len() as int);
        assert(rename_history(f, w0) =~= first) by {
            assert forall|j: int| 0 <= j < k implies rename_history(f, w0)[j] == first[j] by {
                assert(rw[j] == (first + rest.flatten())[j]);
            }
        }
        assert(rename_history(f, w1) =~= rest.flatten()) by {
            assert forall|j: int| 0 <= j < w.len() - k implies rename_history(f, w1)[j] == rest.flatten()[j] by {
                assert(rw[k + j] == (first + rest.flatten())[k + j]);
            }
        }
        let tail = lemma_unflatten_rename(f, rest, w1);
        let parts = seq![w0] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.first() == w0);
        assert(parts.flatten() == w0 + tail.flatten());
        assert(w0 + w1 =~= w);
        assert forall|i: int| 0 <= i < parts.len() implies rename_history(f, #[trigger] parts[i]) == rparts[i] by {
            if i > 0 {
                assert(parts[i] == tail[i - 1]);
                assert(rparts[i] == rest[i - 1]);
            }
        }
        parts
    }
}

/// The parts of a word only contain the word's values.
pub proof fn lemma_flatten_values_in<C>(parts: Seq<Seq<Seq<C>>>, values: Seq<ISet<C>>)
    requires word_values_in(parts.flatten(), values),
    ensures forall|i: int| 0 <= i < parts.len() ==> word_values_in(#[trigger] parts[i], values),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(parts.flatten() == a + b);
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] values_in(a[j], values) by {
            assert((a + b)[j] == a[j]);
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] values_in(b[j], values) by {
            assert((a + b)[a.len() + j] == b[j]);
        }
        lemma_flatten_values_in(parts.drop_first(), values);
        assert forall|i: int| 0 <= i < parts.len() implies word_values_in(#[trigger] parts[i], values) by {
            if i > 0 {
                assert(parts[i] == parts.drop_first()[i - 1]);
            }
        }
    }
}

pub proof fn lemma_lang_rename<C: PartialEq>(
    regex: RegexView<C>, head: HeadView<C>, candidate: Seq<C>, w: Seq<Seq<C>>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires
        renamings_preserve(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        tdsl::lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 1nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => {},
        RegexView::Test(t) => {
            assert(regex_constants(regex, head.len()) =~= test_constants(t, head.len()));
            if w.len() == 1 {
                assert(values_in(w[0], values));
                lemma_test_rename(t, head, candidate, w[0], f, values);
            }
        },
        RegexView::Star(b) | RegexView::Not(b) => {
            lemma_lang_rename_star_not(regex, *b, head, candidate, w, f, values);
        },
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] renamings_preserve(f, regex_constants(cs[i], head.len()), values) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] regex_constants(cs[i], head.len())[j].subset_of(regex_constants(regex, head.len())[j]) by {
                    lemma_regex_constants_index(regex, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { regex_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == regex_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, regex_constants(cs[i], head.len()), regex_constants(regex, head.len()), values);
            }
            if regex is Concat {
                if tdsl::lang(regex, head, candidate, w) {
                    let parts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == cs.len() && w == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, candidate, parts[i]);
                    lemma_flatten_values_in(parts, values);
                    lemma_flatten_rename(f, parts);
                    let rp = rename_parts(f, parts);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, rc, rp[i]) by {
                        assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                    assert(rp.len() == cs.len() && rw == rp.flatten());
                }
                if tdsl::lang(regex, head, rc, rw) {
                    let rparts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == cs.len() && rw == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, rc, parts[i]);
                    let parts = lemma_unflatten_rename(f, rparts, w);
                    lemma_flatten_values_in(parts, values);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, candidate, parts[i]) by {
                        assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        assert(rename_history(f, parts[i]) == rparts[i]);
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                }
            } else {
                assert forall|i: int| 0 <= i < cs.len() implies
                    tdsl::lang(cs[i], head, rc, rw) == tdsl::lang(cs[i], head, candidate, w) by {
                    assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                    lemma_lang_rename(cs[i], head, candidate, w, f, values);
                }
            }
        },
    }
}

proof fn lemma_lang_rename_star_not<C: PartialEq>(
    regex: RegexView<C>, b: RegexView<C>, head: HeadView<C>, candidate: Seq<C>,
    w: Seq<Seq<C>>, f: Seq<spec_fn(C) -> C>,
    values: Seq<ISet<C>>,
)
    requires
        regex == RegexView::Star(Box::new(b)) || regex == RegexView::Not(Box::new(b)),
        renamings_preserve(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        tdsl::lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 0nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    assert(regex_constants(b, head.len()) =~= regex_constants(regex, head.len()));
    if regex is Not {
        lemma_lang_rename(b, head, candidate, w, f, values);
    } else {
        if tdsl::lang(regex, head, candidate, w) {
            let parts = choose|parts: Seq<Seq<Seq<C>>>| w == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, candidate, parts[i]);
            lemma_flatten_values_in(parts, values);
            lemma_flatten_rename(f, parts);
            let rp = rename_parts(f, parts);
            assert forall|i: int| 0 <= i < rp.len() implies tdsl::lang(b, head, rc, rp[i]) by {
                assert(word_values_in(parts[i], values));
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
            assert(rw == rp.flatten());
        }
        if tdsl::lang(regex, head, rc, rw) {
            let rparts = choose|parts: Seq<Seq<Seq<C>>>| rw == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, rc, parts[i]);
            let parts = lemma_unflatten_rename(f, rparts, w);
            lemma_flatten_values_in(parts, values);
            assert forall|i: int| 0 <= i < parts.len() implies tdsl::lang(b, head, candidate, parts[i]) by {
                assert(word_values_in(parts[i], values));
                assert(rename_history(f, parts[i]) == rparts[i]);
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
        }
    }
}

/// Status is invariant under renamings that preserve equality on the given values and with the
/// rule's constants.
pub proof fn lemma_status_rename<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires
        renamings_preserve(f, rule_constants(rule), values),
        values_in(candidate, values),
        word_values_in(history, values),
    ensures
        rule_status(rule, candidate, history)
            == rule_status(rule, rename_event(f, candidate), rename_history(f, history)),
{
    let k = rule_constants(rule);
    assert forall|i: int| 0 <= i < rule.head.len() implies
        tdsl::head_pattern_matches(rule.head[i], rename_event(f, candidate)[i])
            == tdsl::head_pattern_matches(rule.head[i], candidate[i]) by {
        lemma_head_pattern_rename(rule.head[i], f[i], k[i], values[i], candidate[i]);
    }
    assert(tdsl::head_matches(rule.head, candidate) == tdsl::head_matches(rule.head, rename_event(f, candidate)));
    assert forall|i: int| 0 <= i < rule.head.len() implies
        #[trigger] regex_constants(rule.tail, rule.head.len())[i].subset_of(k[i]) by {}
    lemma_renamings_mono(f, regex_constants(rule.tail, rule.head.len()), k, values);
    lemma_lang_rename(rule.tail, rule.head, candidate, history, f, values);
}

pub proof fn lemma_pair_values_contains<C>(candidate: Seq<C>, history: Seq<Seq<C>>, coordinate: int, i: int)
    requires 0 <= i < history.len(), 0 <= coordinate < history[i].len(),
    ensures pair_values(candidate, history, coordinate).contains(history[i][coordinate]),
{
    let x = history[i][coordinate];
    assert(exists|j: int| 0 <= j < history.len() && 0 <= coordinate < history[j].len()
        && #[trigger] history[j][coordinate] == x);
}

pub proof fn theorem_genericity<C: PartialEq>()
    ensures stmt_genericity::<C>(),
{
    assert forall|rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>, f: Seq<spec_fn(C) -> C>|
        rule_wf(rule) && candidate.len() == rule.head.len()
            && (forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len())
            && renamings_preserve(f, rule_constants(rule),
                Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i)))
        implies (rule_status(rule, candidate, history)
            == #[trigger] rule_status(rule, rename_event(f, candidate), rename_history(f, history))) by {
        let values = Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i));
        assert(values_in(candidate, values));
        assert forall|i: int| 0 <= i < history.len() implies #[trigger] values_in(history[i], values) by {
            assert forall|j: int| 0 <= j < candidate.len() implies #[trigger] values[j].contains(history[i][j]) by {
                lemma_pair_values_contains(candidate, history, j, i);
            }
        }
        lemma_status_rename(rule, candidate, history, f, values);
    }
}

} // verus!
