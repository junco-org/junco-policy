//! Layer 0: policy semantics over typed component values (paper §3.3, `bg.tex:101-126`;
//! refinement, `inclusion.tex:7-20`; coverage, redundancy, vacuity, `appendix.tex:437-455`).
//!
//! The valuation `θ` of the paper is the candidate itself; histories are oldest first and never
//! contain the candidate. Tail and test semantics are the existing `junco_core::verify::dsl`
//! semantics, whose component equality is `PartialEqSpec::eq_spec`. A policy is a finite sequence
//! of rules; its order is irrelevant to every predicate below.
use alloc::boxed::Box;
use history_syntax::Comparison;
use history_syntax::syntax::RuleMode;
use history_syntax::verify::dsl::{AtomView, HeadView, PatternView, RegexView, RuleView, TestView};
use junco_core::verify::dsl as tdsl;
use junco_core::verify::dsl::EventView as TEvent;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// The status of one rule for a candidate and a history (`bg.tex:113-121`).
pub enum Status { NotFired, Satisfied, Violated }

/// `mode = require` and the history is outside the tail, or `mode = forbid` and it is inside.
pub open spec fn violated_by(mode: RuleMode, inside: bool) -> bool {
    match mode { RuleMode::Require => !inside, RuleMode::Forbid => inside }
}

pub open spec fn rule_status<P: PartialEq, A: PartialEq, R: PartialEq>(
    rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
) -> Status {
    if !tdsl::head_matches(rule.head, candidate) {
        Status::NotFired
    } else if violated_by(rule.mode, tdsl::lang(rule.tail, rule.head, candidate, history)) {
        Status::Violated
    } else {
        Status::Satisfied
    }
}

pub open spec fn rule_denies<P: PartialEq, A: PartialEq, R: PartialEq>(
    rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
) -> bool {
    rule_status(rule, candidate, history) is Violated
}

/// A policy denies iff some rule is violated (`bg.tex:123-126`).
pub open spec fn policy_denies<P: PartialEq, A: PartialEq, R: PartialEq>(
    policy: Seq<RuleView<P, A, R>>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
) -> bool {
    exists|i: int| 0 <= i < policy.len() && #[trigger] rule_denies(policy[i], candidate, history)
}

pub open spec fn policy_permits<P: PartialEq, A: PartialEq, R: PartialEq>(
    policy: Seq<RuleView<P, A, R>>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
) -> bool {
    !policy_denies(policy, candidate, history)
}

// ----- component domains -----

/// The values a component ranges over: all values of its type (`None`), or a declared finite set.
/// The paper assumes every domain infinite (`bg.tex:14-18`); declared finite domains are an
/// implementation feature (`Domains::with_*`) outside the paper's theorems.
pub struct DomainsView<P, A, R> {
    pub principal: Option<Set<P>>,
    pub action: Option<Set<A>>,
    pub resource: Option<Set<R>>,
}

pub open spec fn in_domain<T: PartialEq>(domain: Option<Set<T>>, value: T) -> bool {
    match domain {
        None => true,
        Some(values) => exists|w: T| values.contains(w) && value.eq_spec(&w),
    }
}

pub open spec fn event_in<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, event: TEvent<P, A, R>,
) -> bool {
    in_domain(domains.principal, event.principal) && in_domain(domains.action, event.action)
        && in_domain(domains.resource, event.resource)
}

pub open spec fn history_in<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, history: Seq<TEvent<P, A, R>>,
) -> bool {
    forall|i: int| 0 <= i < history.len() ==> #[trigger] event_in(domains, history[i])
}

/// Every domain is `None`: candidates and history events range over whole types.
pub open spec fn all_unrestricted<P, A, R>(domains: DomainsView<P, A, R>) -> bool {
    domains.principal is None && domains.action is None && domains.resource is None
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

/// The paper's hypothesis (`bg.tex:14`, `inclusion.tex:198`, `inclusion.tex:258`).
pub open spec fn infinite_domains<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>,
) -> bool {
    all_unrestricted(domains) && infinite_type::<P>() && infinite_type::<A>() && infinite_type::<R>()
}

// ----- well-formed rules -----

/// Head variables have distinct names and every tail variable is the head variable of its own
/// component (`bg.tex:111`, "a tail whose variables occur in h"; component-locality, `bg.tex:28`).
pub open spec fn rule_wf<P, A, R>(rule: RuleView<P, A, R>) -> bool {
    tdsl::head_scoped(rule.head) && tdsl::regex_scoped(rule.tail, rule.head)
}

pub open spec fn head_tails_wf<P, A, R>(head: HeadView<P, A, R>, left: RegexView<P, A, R>, right: RegexView<P, A, R>) -> bool {
    tdsl::head_scoped(head) && tdsl::regex_scoped(left, head) && tdsl::regex_scoped(right, head)
}

// ----- policy questions (`inclusion.tex:7-20`, `appendix.tex:444-455`) -----

/// `P ⊑ Q` over `domains`: every pair permitted by `P` is permitted by `Q`.
pub open spec fn refines<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, p: Seq<RuleView<P, A, R>>, q: Seq<RuleView<P, A, R>>,
) -> bool {
    forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
        event_in(domains, candidate) && history_in(domains, history) && policy_permits(p, candidate, history)
            ==> #[trigger] policy_permits(q, candidate, history)
}

/// `P` covers `rule`: every pair the rule denies is denied by some rule of `P`.
pub open spec fn covers<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, p: Seq<RuleView<P, A, R>>, rule: RuleView<P, A, R>,
) -> bool {
    forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
        event_in(domains, candidate) && history_in(domains, history) && #[trigger] rule_denies(rule, candidate, history)
            ==> policy_denies(p, candidate, history)
}

pub open spec fn never_denies<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, rule: RuleView<P, A, R>,
) -> bool {
    forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
        event_in(domains, candidate) && history_in(domains, history) ==> !#[trigger] rule_denies(rule, candidate, history)
}

/// The rule denies every candidate it matches, whatever the history.
pub open spec fn always_denies<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, rule: RuleView<P, A, R>,
) -> bool {
    forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
        event_in(domains, candidate) && history_in(domains, history) && tdsl::head_matches(rule.head, candidate)
            ==> #[trigger] rule_denies(rule, candidate, history)
}

/// For every candidate matching `head`, `L(left) ⊆ L(right)`; both tails read `head`'s variables.
pub open spec fn tails_included<P: PartialEq, A: PartialEq, R: PartialEq>(
    domains: DomainsView<P, A, R>, head: HeadView<P, A, R>, left: RegexView<P, A, R>, right: RegexView<P, A, R>,
) -> bool {
    forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
        event_in(domains, candidate) && history_in(domains, history) && tdsl::head_matches(head, candidate)
            && #[trigger] tdsl::lang(left, head, candidate, history) ==> tdsl::lang(right, head, candidate, history)
}

// ----- statements (no proofs in this phase) -----

/// `P ⊑ Q` iff `P` covers every rule of `Q` (`appendix.tex:450`).
pub open spec fn stmt_refines_iff_covers<P: PartialEq, A: PartialEq, R: PartialEq>() -> bool {
    forall|domains: DomainsView<P, A, R>, p: Seq<RuleView<P, A, R>>, q: Seq<RuleView<P, A, R>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
}

/// Removing a covered rule changes no decision (`appendix.tex:452-453`): with `others` the policy
/// without the rule, the two policies deny the same pairs iff `others` covers the rule.
pub open spec fn stmt_redundant_iff_covered<P: PartialEq, A: PartialEq, R: PartialEq>() -> bool {
    forall|domains: DomainsView<P, A, R>, others: Seq<RuleView<P, A, R>>, rule: RuleView<P, A, R>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
}

/// Genericity: semantics depends only on which values are equal and on equality with the
/// rules' constants. Hence a property proved for every pair over an infinite domain holds for
/// every pair over any type: map the finitely many values of a pair injectively into the infinite
/// domain, fixing the constants. Stated for one rule; policies follow pointwise.
pub open spec fn renaming_preserves<T: PartialEq>(f: spec_fn(T) -> T, fixed: ISet<T>, values: ISet<T>) -> bool {
    &&& forall|x: T, y: T| values.contains(x) && values.contains(y) ==> (#[trigger] f(x).eq_spec(&#[trigger] f(y)) == x.eq_spec(&y))
    &&& forall|x: T, k: T| values.contains(x) && fixed.contains(k) ==> (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k))
}

pub open spec fn rename_event<P, A, R>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, e: TEvent<P, A, R>,
) -> TEvent<P, A, R> {
    TEvent { principal: fp(e.principal), action: fa(e.action), resource: fr(e.resource) }
}

pub open spec fn rename_history<P, A, R>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, h: Seq<TEvent<P, A, R>>,
) -> Seq<TEvent<P, A, R>> {
    h.map(|i: int, e: TEvent<P, A, R>| rename_event(fp, fa, fr, e))
}

/// Values of a pair at one component.
pub open spec fn pair_values<P, A, R, T>(candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
    get: spec_fn(TEvent<P, A, R>) -> T) -> ISet<T> {
    ISet::new(|x: T| x == get(candidate) || exists|i: int| 0 <= i < history.len() && #[trigger] get(history[i]) == x)
}

/// Statement form of genericity for one rule: a renaming that is injective on the pair's values
/// and fixes the rule's constants preserves the rule's status.
pub open spec fn stmt_genericity<P: PartialEq, A: PartialEq, R: PartialEq>() -> bool {
    forall|rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
        fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R|
        rule_wf(rule)
            && renaming_preserves(fp, rule_constants(rule).0, pair_values(candidate, history, |e: TEvent<P, A, R>| e.principal))
            && renaming_preserves(fa, rule_constants(rule).1, pair_values(candidate, history, |e: TEvent<P, A, R>| e.action))
            && renaming_preserves(fr, rule_constants(rule).2, pair_values(candidate, history, |e: TEvent<P, A, R>| e.resource))
            ==> (rule_status(rule, candidate, history)
                == #[trigger] rule_status(rule, rename_event(fp, fa, fr, candidate), rename_history(fp, fa, fr, history)))
}

pub open spec fn pattern_constant<T>(pattern: PatternView<T>) -> ISet<T> {
    match pattern { PatternView::Constant(c) => ISet::empty().insert(c), PatternView::Variable(_) => ISet::empty() }
}

pub open spec fn test_constants<P, A, R>(test: TestView<P, A, R>) -> (ISet<P>, ISet<A>, ISet<R>)
    decreases test,
{
    match test {
        TestView::True | TestView::False => (ISet::empty(), ISet::empty(), ISet::empty()),
        TestView::Atom { pattern, .. } => match pattern {
            AtomView::Principal(p) => (pattern_constant(p), ISet::empty(), ISet::empty()),
            AtomView::Action(p) => (ISet::empty(), pattern_constant(p), ISet::empty()),
            AtomView::Resource(p) => (ISet::empty(), ISet::empty(), pattern_constant(p)),
        },
        TestView::And(cs) | TestView::Or(cs) => (
            ISet::new(|x: P| exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && test_constants(cs[i]).0.contains(x)),
            ISet::new(|x: A| exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && test_constants(cs[i]).1.contains(x)),
            ISet::new(|x: R| exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && test_constants(cs[i]).2.contains(x)),
        ),
    }
}

pub open spec fn regex_constants<P, A, R>(regex: RegexView<P, A, R>) -> (ISet<P>, ISet<A>, ISet<R>)
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => (ISet::empty(), ISet::empty(), ISet::empty()),
        RegexView::Test(t) => test_constants(t),
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => (
            ISet::new(|x: P| exists|i: int| 0 <= i < cs.len() && #[trigger] regex_constants(cs[i]).0.contains(x)),
            ISet::new(|x: A| exists|i: int| 0 <= i < cs.len() && #[trigger] regex_constants(cs[i]).1.contains(x)),
            ISet::new(|x: R| exists|i: int| 0 <= i < cs.len() && #[trigger] regex_constants(cs[i]).2.contains(x)),
        ),
        RegexView::Star(c) | RegexView::Not(c) => regex_constants(*c),
    }
}

/// Constants of a rule's head and tail, per component (finite for every finite rule view).
pub open spec fn rule_constants<P, A, R>(rule: RuleView<P, A, R>) -> (ISet<P>, ISet<A>, ISet<R>) {
    let t = regex_constants(rule.tail);
    (t.0.union(pattern_constant(rule.head.principal)), t.1.union(pattern_constant(rule.head.action)),
        t.2.union(pattern_constant(rule.head.resource)))
}


// ----- proofs -----

/// Appending a rule to a policy adds exactly that rule's denials.
pub proof fn lemma_policy_denies_push<P: PartialEq, A: PartialEq, R: PartialEq>(
    policy: Seq<RuleView<P, A, R>>, rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
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

pub proof fn theorem_refines_iff_covers<P: PartialEq, A: PartialEq, R: PartialEq>()
    ensures stmt_refines_iff_covers::<P, A, R>(),
{
    assert forall|domains: DomainsView<P, A, R>, p: Seq<RuleView<P, A, R>>, q: Seq<RuleView<P, A, R>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
    by {
        if refines(domains, p, q) {
            assert forall|i: int| 0 <= i < q.len() implies covers(domains, p, #[trigger] q[i]) by {
                assert forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
                    event_in(domains, candidate) && history_in(domains, history)
                        && #[trigger] rule_denies(q[i], candidate, history)
                    implies policy_denies(p, candidate, history) by {
                    assert(policy_denies(q, candidate, history));
                    assert(!policy_permits(q, candidate, history));
                }
            }
        }
        if forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i]) {
            assert forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
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

pub proof fn theorem_redundant_iff_covered<P: PartialEq, A: PartialEq, R: PartialEq>()
    ensures stmt_redundant_iff_covered::<P, A, R>(),
{
    assert forall|domains: DomainsView<P, A, R>, others: Seq<RuleView<P, A, R>>, rule: RuleView<P, A, R>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
    by {
        if covers(domains, others, rule) {
            assert forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
                event_in(domains, candidate) && history_in(domains, history)
                implies (#[trigger] policy_denies(others.push(rule), candidate, history)
                    == policy_denies(others, candidate, history)) by {
                lemma_policy_denies_push(others, rule, candidate, history);
            }
        }
        if forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
            event_in(domains, candidate) && history_in(domains, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
        {
            assert forall|candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>|
                event_in(domains, candidate) && history_in(domains, history) && #[trigger] rule_denies(rule, candidate, history)
                implies policy_denies(others, candidate, history) by {
                lemma_policy_denies_push(others, rule, candidate, history);
                assert(policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history));
            }
        }
    }
}

// ----- genericity -----

/// Every component of `e` lies in the given value sets.
pub open spec fn values_in<P, A, R>(e: TEvent<P, A, R>, vp: ISet<P>, va: ISet<A>, vr: ISet<R>) -> bool {
    vp.contains(e.principal) && va.contains(e.action) && vr.contains(e.resource)
}

pub open spec fn word_values_in<P, A, R>(w: Seq<TEvent<P, A, R>>, vp: ISet<P>, va: ISet<A>, vr: ISet<R>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] values_in(w[i], vp, va, vr)
}

/// The three renamings preserve equality on the values, and with the constants.
pub open spec fn renamings_preserve<P: PartialEq, A: PartialEq, R: PartialEq>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, fixed: (ISet<P>, ISet<A>, ISet<R>),
    vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
) -> bool {
    renaming_preserves(fp, fixed.0, vp) && renaming_preserves(fa, fixed.1, va) && renaming_preserves(fr, fixed.2, vr)
}

/// Each part of a word renamed separately.
pub open spec fn rename_parts<P, A, R>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, parts: Seq<Seq<TEvent<P, A, R>>>,
) -> Seq<Seq<TEvent<P, A, R>>> {
    parts.map(|i: int, part: Seq<TEvent<P, A, R>>| rename_history(fp, fa, fr, part))
}

pub proof fn lemma_renaming_mono<T: PartialEq>(f: spec_fn(T) -> T, small: ISet<T>, big: ISet<T>, values: ISet<T>)
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

pub proof fn lemma_renamings_mono<P: PartialEq, A: PartialEq, R: PartialEq>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, small: (ISet<P>, ISet<A>, ISet<R>),
    big: (ISet<P>, ISet<A>, ISet<R>), vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
)
    requires
        renamings_preserve(fp, fa, fr, big, vp, va, vr),
        forall|x: P| #[trigger] small.0.contains(x) ==> big.0.contains(x),
        forall|x: A| #[trigger] small.1.contains(x) ==> big.1.contains(x),
        forall|x: R| #[trigger] small.2.contains(x) ==> big.2.contains(x),
    ensures renamings_preserve(fp, fa, fr, small, vp, va, vr),
{
    lemma_renaming_mono(fp, small.0, big.0, vp);
    lemma_renaming_mono(fa, small.1, big.1, va);
    lemma_renaming_mono(fr, small.2, big.2, vr);
}

pub proof fn lemma_head_pattern_rename<T: PartialEq>(pattern: PatternView<T>, f: spec_fn(T) -> T, fixed: ISet<T>, values: ISet<T>, x: T)
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
    fixed: ISet<T>, values: ISet<T>, c: T, e: T,
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

pub proof fn lemma_test_rename<P: PartialEq, A: PartialEq, R: PartialEq>(
    test: TestView<P, A, R>, head: HeadView<P, A, R>, candidate: TEvent<P, A, R>, event: TEvent<P, A, R>,
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
)
    requires
        renamings_preserve(fp, fa, fr, test_constants(test), vp, va, vr),
        values_in(candidate, vp, va, vr),
        values_in(event, vp, va, vr),
    ensures
        tdsl::test_sem(test, head, rename_event(fp, fa, fr, candidate), rename_event(fp, fa, fr, event))
            == tdsl::test_sem(test, head, candidate, event),
    decreases test,
{
    let rc = rename_event(fp, fa, fr, candidate);
    let re = rename_event(fp, fa, fr, event);
    match test {
        TestView::True | TestView::False => {},
        TestView::Atom { comparison, pattern } => match pattern {
            AtomView::Principal(p) => lemma_comparison_rename(comparison, p, head.principal, fp,
                test_constants(test).0, vp, candidate.principal, event.principal),
            AtomView::Action(p) => lemma_comparison_rename(comparison, p, head.action, fa,
                test_constants(test).1, va, candidate.action, event.action),
            AtomView::Resource(p) => lemma_comparison_rename(comparison, p, head.resource, fr,
                test_constants(test).2, vr, candidate.resource, event.resource),
        },
        TestView::And(cs) | TestView::Or(cs) => {
            assert forall|i: int| 0 <= i < cs.len()
                implies tdsl::test_sem(cs[i], head, rc, re) == tdsl::test_sem(cs[i], head, candidate, event) by {
                assert forall|x: P| #[trigger] test_constants(cs[i]).0.contains(x) implies test_constants(test).0.contains(x) by {}
                assert forall|x: A| #[trigger] test_constants(cs[i]).1.contains(x) implies test_constants(test).1.contains(x) by {}
                assert forall|x: R| #[trigger] test_constants(cs[i]).2.contains(x) implies test_constants(test).2.contains(x) by {}
                lemma_renamings_mono(fp, fa, fr, test_constants(cs[i]), test_constants(test), vp, va, vr);
                lemma_test_rename(cs[i], head, candidate, event, fp, fa, fr, vp, va, vr);
            }
        },
    }
}

/// Renaming commutes with flattening.
pub proof fn lemma_flatten_rename<P, A, R>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, parts: Seq<Seq<TEvent<P, A, R>>>,
)
    ensures rename_history(fp, fa, fr, parts.flatten()) == rename_parts(fp, fa, fr, parts).flatten(),
    decreases parts.len(),
{
    let rp = rename_parts(fp, fa, fr, parts);
    if parts.len() == 0 {
        assert(rename_history(fp, fa, fr, parts.flatten()) =~= rp.flatten());
    } else {
        lemma_flatten_rename(fp, fa, fr, parts.drop_first());
        assert(rp.drop_first() =~= rename_parts(fp, fa, fr, parts.drop_first()));
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(rename_history(fp, fa, fr, a + b) =~= rename_history(fp, fa, fr, a) + rename_history(fp, fa, fr, b));
        assert(rp.first() == rename_history(fp, fa, fr, a));
    }
}

/// A word whose renaming is split into parts splits into parts with those renamings.
pub proof fn lemma_unflatten_rename<P, A, R>(
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, rparts: Seq<Seq<TEvent<P, A, R>>>,
    w: Seq<TEvent<P, A, R>>,
) -> (parts: Seq<Seq<TEvent<P, A, R>>>)
    requires rparts.flatten() == rename_history(fp, fa, fr, w),
    ensures
        parts.len() == rparts.len(),
        parts.flatten() == w,
        forall|i: int| 0 <= i < parts.len() ==> rename_history(fp, fa, fr, #[trigger] parts[i]) == rparts[i],
    decreases rparts.len(),
{
    if rparts.len() == 0 {
        assert(w =~= Seq::<TEvent<P, A, R>>::empty());
        Seq::empty()
    } else {
        let first = rparts.first();
        let rest = rparts.drop_first();
        let k = first.len() as int;
        let rw = rename_history(fp, fa, fr, w);
        assert(rw == first + rest.flatten());
        let w0 = w.subrange(0, k);
        let w1 = w.subrange(k, w.len() as int);
        assert(rename_history(fp, fa, fr, w0) =~= first) by {
            assert forall|j: int| 0 <= j < k implies rename_history(fp, fa, fr, w0)[j] == first[j] by {
                assert(rw[j] == (first + rest.flatten())[j]);
            }
        }
        assert(rename_history(fp, fa, fr, w1) =~= rest.flatten()) by {
            assert forall|j: int| 0 <= j < w.len() - k implies rename_history(fp, fa, fr, w1)[j] == rest.flatten()[j] by {
                assert(rw[k + j] == (first + rest.flatten())[k + j]);
            }
        }
        let tail = lemma_unflatten_rename(fp, fa, fr, rest, w1);
        let parts = seq![w0] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.first() == w0);
        assert(parts.flatten() == w0 + tail.flatten());
        assert(w0 + w1 =~= w);
        assert forall|i: int| 0 <= i < parts.len() implies rename_history(fp, fa, fr, #[trigger] parts[i]) == rparts[i] by {
            if i > 0 {
                assert(parts[i] == tail[i - 1]);
                assert(rparts[i] == rest[i - 1]);
            }
        }
        parts
    }
}

/// The parts of a word only contain the word's values.
pub proof fn lemma_flatten_values_in<P, A, R>(parts: Seq<Seq<TEvent<P, A, R>>>, vp: ISet<P>, va: ISet<A>, vr: ISet<R>)
    requires word_values_in(parts.flatten(), vp, va, vr),
    ensures forall|i: int| 0 <= i < parts.len() ==> word_values_in(#[trigger] parts[i], vp, va, vr),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(parts.flatten() == a + b);
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] values_in(a[j], vp, va, vr) by {
            assert((a + b)[j] == a[j]);
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] values_in(b[j], vp, va, vr) by {
            assert((a + b)[a.len() + j] == b[j]);
        }
        lemma_flatten_values_in(parts.drop_first(), vp, va, vr);
        assert forall|i: int| 0 <= i < parts.len() implies word_values_in(#[trigger] parts[i], vp, va, vr) by {
            if i > 0 {
                assert(parts[i] == parts.drop_first()[i - 1]);
            }
        }
    }
}

pub proof fn lemma_lang_rename<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: TEvent<P, A, R>, w: Seq<TEvent<P, A, R>>,
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
)
    requires
        renamings_preserve(fp, fa, fr, regex_constants(regex), vp, va, vr),
        values_in(candidate, vp, va, vr),
        word_values_in(w, vp, va, vr),
    ensures
        tdsl::lang(regex, head, rename_event(fp, fa, fr, candidate), rename_history(fp, fa, fr, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 1nat,
{
    let rc = rename_event(fp, fa, fr, candidate);
    let rw = rename_history(fp, fa, fr, w);
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => {},
        RegexView::Test(t) => {
            if w.len() == 1 {
                assert(values_in(w[0], vp, va, vr));
                lemma_test_rename(t, head, candidate, w[0], fp, fa, fr, vp, va, vr);
            }
        },
        RegexView::Star(b) | RegexView::Not(b) => {
            lemma_lang_rename_star_not(regex, *b, head, candidate, w, fp, fa, fr, vp, va, vr);
        },
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] renamings_preserve(fp, fa, fr, regex_constants(cs[i]), vp, va, vr) by {
                // Unfolding `Not(cs[i])` creates the fuel-level term the `exists` in
                // `regex_constants(regex)` is triggered on.
                assert(regex_constants(RegexView::<P, A, R>::Not(Box::new(cs[i]))) == regex_constants(cs[i]));
                assert forall|x: P| #[trigger] regex_constants(cs[i]).0.contains(x) implies regex_constants(regex).0.contains(x) by {}
                assert forall|x: A| #[trigger] regex_constants(cs[i]).1.contains(x) implies regex_constants(regex).1.contains(x) by {}
                assert forall|x: R| #[trigger] regex_constants(cs[i]).2.contains(x) implies regex_constants(regex).2.contains(x) by {}
                lemma_renamings_mono(fp, fa, fr, regex_constants(cs[i]), regex_constants(regex), vp, va, vr);
            }
            if regex is Concat {
                if tdsl::lang(regex, head, candidate, w) {
                    let parts = choose|parts: Seq<Seq<TEvent<P, A, R>>>| parts.len() == cs.len() && w == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, candidate, parts[i]);
                    lemma_flatten_values_in(parts, vp, va, vr);
                    lemma_flatten_rename(fp, fa, fr, parts);
                    let rp = rename_parts(fp, fa, fr, parts);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, rc, rp[i]) by {
                        assert(renamings_preserve(fp, fa, fr, regex_constants(cs[i]), vp, va, vr));
                        assert(word_values_in(parts[i], vp, va, vr));
                        lemma_lang_rename(cs[i], head, candidate, parts[i], fp, fa, fr, vp, va, vr);
                    }
                    assert(rp.len() == cs.len() && rw == rp.flatten());
                }
                if tdsl::lang(regex, head, rc, rw) {
                    let rparts = choose|parts: Seq<Seq<TEvent<P, A, R>>>| parts.len() == cs.len() && rw == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, rc, parts[i]);
                    let parts = lemma_unflatten_rename(fp, fa, fr, rparts, w);
                    lemma_flatten_values_in(parts, vp, va, vr);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, candidate, parts[i]) by {
                        assert(renamings_preserve(fp, fa, fr, regex_constants(cs[i]), vp, va, vr));
                        assert(word_values_in(parts[i], vp, va, vr));
                        assert(rename_history(fp, fa, fr, parts[i]) == rparts[i]);
                        lemma_lang_rename(cs[i], head, candidate, parts[i], fp, fa, fr, vp, va, vr);
                    }
                }
            } else {
                assert forall|i: int| 0 <= i < cs.len() implies
                    tdsl::lang(cs[i], head, rc, rw) == tdsl::lang(cs[i], head, candidate, w) by {
                    assert(renamings_preserve(fp, fa, fr, regex_constants(cs[i]), vp, va, vr));
                    lemma_lang_rename(cs[i], head, candidate, w, fp, fa, fr, vp, va, vr);
                }
            }
        },
    }
}

proof fn lemma_lang_rename_star_not<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, b: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: TEvent<P, A, R>,
    w: Seq<TEvent<P, A, R>>, fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R,
    vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
)
    requires
        regex == RegexView::Star(Box::new(b)) || regex == RegexView::Not(Box::new(b)),
        renamings_preserve(fp, fa, fr, regex_constants(regex), vp, va, vr),
        values_in(candidate, vp, va, vr),
        word_values_in(w, vp, va, vr),
    ensures
        tdsl::lang(regex, head, rename_event(fp, fa, fr, candidate), rename_history(fp, fa, fr, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 0nat,
{
    let rc = rename_event(fp, fa, fr, candidate);
    let rw = rename_history(fp, fa, fr, w);
    assert(regex_constants(b) == regex_constants(regex));
    if regex is Not {
        lemma_lang_rename(b, head, candidate, w, fp, fa, fr, vp, va, vr);
    } else {
        if tdsl::lang(regex, head, candidate, w) {
            let parts = choose|parts: Seq<Seq<TEvent<P, A, R>>>| w == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, candidate, parts[i]);
            lemma_flatten_values_in(parts, vp, va, vr);
            lemma_flatten_rename(fp, fa, fr, parts);
            let rp = rename_parts(fp, fa, fr, parts);
            assert forall|i: int| 0 <= i < rp.len() implies tdsl::lang(b, head, rc, rp[i]) by {
                assert(word_values_in(parts[i], vp, va, vr));
                lemma_lang_rename(b, head, candidate, parts[i], fp, fa, fr, vp, va, vr);
            }
            assert(rw == rp.flatten());
        }
        if tdsl::lang(regex, head, rc, rw) {
            let rparts = choose|parts: Seq<Seq<TEvent<P, A, R>>>| rw == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, rc, parts[i]);
            let parts = lemma_unflatten_rename(fp, fa, fr, rparts, w);
            lemma_flatten_values_in(parts, vp, va, vr);
            assert forall|i: int| 0 <= i < parts.len() implies tdsl::lang(b, head, candidate, parts[i]) by {
                assert(word_values_in(parts[i], vp, va, vr));
                assert(rename_history(fp, fa, fr, parts[i]) == rparts[i]);
                lemma_lang_rename(b, head, candidate, parts[i], fp, fa, fr, vp, va, vr);
            }
        }
    }
}

/// Status is invariant under renamings that preserve equality on the given values and with the
/// rule's constants.
pub proof fn lemma_status_rename<P: PartialEq, A: PartialEq, R: PartialEq>(
    rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
    fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R, vp: ISet<P>, va: ISet<A>, vr: ISet<R>,
)
    requires
        renamings_preserve(fp, fa, fr, rule_constants(rule), vp, va, vr),
        values_in(candidate, vp, va, vr),
        word_values_in(history, vp, va, vr),
    ensures
        rule_status(rule, candidate, history)
            == rule_status(rule, rename_event(fp, fa, fr, candidate), rename_history(fp, fa, fr, history)),
{
    let k = rule_constants(rule);
    lemma_head_pattern_rename(rule.head.principal, fp, k.0, vp, candidate.principal);
    lemma_head_pattern_rename(rule.head.action, fa, k.1, va, candidate.action);
    lemma_head_pattern_rename(rule.head.resource, fr, k.2, vr, candidate.resource);
    lemma_renamings_mono(fp, fa, fr, regex_constants(rule.tail), k, vp, va, vr);
    lemma_lang_rename(rule.tail, rule.head, candidate, history, fp, fa, fr, vp, va, vr);
}

pub proof fn lemma_pair_values_contains<P, A, R, T>(
    candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>, get: spec_fn(TEvent<P, A, R>) -> T, i: int,
)
    requires 0 <= i < history.len(),
    ensures pair_values(candidate, history, get).contains(get(history[i])),
{
    let x = get(history[i]);
    assert(exists|j: int| 0 <= j < history.len() && #[trigger] get(history[j]) == x);
}

pub proof fn theorem_genericity<P: PartialEq, A: PartialEq, R: PartialEq>()
    ensures stmt_genericity::<P, A, R>(),
{
    assert forall|rule: RuleView<P, A, R>, candidate: TEvent<P, A, R>, history: Seq<TEvent<P, A, R>>,
        fp: spec_fn(P) -> P, fa: spec_fn(A) -> A, fr: spec_fn(R) -> R|
        rule_wf(rule)
            && renaming_preserves(fp, rule_constants(rule).0, pair_values(candidate, history, |e: TEvent<P, A, R>| e.principal))
            && renaming_preserves(fa, rule_constants(rule).1, pair_values(candidate, history, |e: TEvent<P, A, R>| e.action))
            && renaming_preserves(fr, rule_constants(rule).2, pair_values(candidate, history, |e: TEvent<P, A, R>| e.resource))
        implies (rule_status(rule, candidate, history)
            == #[trigger] rule_status(rule, rename_event(fp, fa, fr, candidate), rename_history(fp, fa, fr, history)))
    by {
        let vp = pair_values(candidate, history, |e: TEvent<P, A, R>| e.principal);
        let va = pair_values(candidate, history, |e: TEvent<P, A, R>| e.action);
        let vr = pair_values(candidate, history, |e: TEvent<P, A, R>| e.resource);
        assert(values_in(candidate, vp, va, vr));
        assert forall|i: int| 0 <= i < history.len() implies #[trigger] values_in(history[i], vp, va, vr) by {
            lemma_pair_values_contains(candidate, history, |e: TEvent<P, A, R>| e.principal, i);
            lemma_pair_values_contains(candidate, history, |e: TEvent<P, A, R>| e.action, i);
            lemma_pair_values_contains(candidate, history, |e: TEvent<P, A, R>| e.resource, i);
        }
        lemma_status_rename(rule, candidate, history, fp, fa, fr, vp, va, vr);
    }
}

} // verus!
