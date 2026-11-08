//! Ten agent policies over one event vocabulary, compared pairwise for strictness.
//!
//! Run with `cargo run --release -p history-analysis --example corpus`. For every ordered pair of
//! policies it asks whether the first is at least as strict as the second, and for every rule of
//! the second whether the first covers it; then whether each rule is redundant in its own policy
//! and in the union of all ten. Every counterexample is replayed through the runtime's trace
//! policy, which must deny it under the covered side and grant it under the covering side. Each
//! query is timed as the median of `CORPUS_RUNS` runs, 5 by default.

use std::sync::Arc;
use std::time::{Duration, Instant};

use history_analysis::{
    Components, Counterexample, Domains, Inclusion, PolicyAnalyzer, RuleId, Value,
};
use history_semantics::{PolicyDecision, TracePolicy, TraceRule};
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Act {
    Read,
    Edit,
    Delete,
    Release,
    Stage,
    Unstage,
    Commit,
    Checkout,
    Stash,
    Clean,
    Diff,
    Log,
    Send,
    Approve,
    Push,
    Merge,
    Freeze,
    Thaw,
}

const ACTS: [Act; 18] = [
    Act::Read,
    Act::Edit,
    Act::Delete,
    Act::Release,
    Act::Stage,
    Act::Unstage,
    Act::Commit,
    Act::Checkout,
    Act::Stash,
    Act::Clean,
    Act::Diff,
    Act::Log,
    Act::Send,
    Act::Approve,
    Act::Push,
    Act::Merge,
    Act::Freeze,
    Act::Thaw,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Ev {
    principal: &'static str,
    action: Act,
    resource: &'static str,
}

impl Event for Ev {
    type Principal = &'static str;
    type Action = Act;
    type Resource = &'static str;

    fn principal(self) -> &'static str {
        self.principal
    }

    fn action(self) -> Act {
        self.action
    }

    fn resource(self) -> &'static str {
        self.resource
    }
}

type Test = TestExpr<Ev>;
type Re = RegexExpr<Ev>;

// ---------------------------------------------------------------------------------------------
// Building blocks.

/// The event's principal is (`Eq`) or is not (`Neq`) the candidate's.
fn me(comparison: Comparison) -> Test {
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::variable("p")),
    )
}

/// The event's resource is (`Eq`) or is not (`Neq`) the candidate's.
fn here(comparison: Comparison) -> Test {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::variable("r")),
    )
}

fn res(comparison: Comparison, resource: &'static str) -> Test {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::constant(resource)),
    )
}

fn act(comparison: Comparison, action: Act) -> Test {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}

fn one_of(actions: &[Act]) -> Test {
    TestExpr::or(actions.iter().map(|&action| act(Comparison::Eq, action)))
}

fn none_of(actions: &[Act]) -> Test {
    TestExpr::and(actions.iter().map(|&action| act(Comparison::Neq, action)))
}

fn test(test: Test) -> Re {
    RegexExpr::test(test)
}

/// `Σ*·trigger·Σ*`: `trigger` happened.
fn ever(trigger: Test) -> Re {
    RegexExpr::concat([RegexExpr::all(), test(trigger), RegexExpr::all()])
}

/// `Σ*·trigger·keep*`: `trigger` happened and every later event satisfies `keep`.
fn since(trigger: Test, keep: Test) -> Re {
    RegexExpr::concat([RegexExpr::all(), test(trigger), RegexExpr::star(test(keep))])
}

/// A forbid rule whose head binds the principal `p`, fixes the action, and binds the resource `r`
/// or fixes it to a constant.
fn forbid(action: Act, resource: Option<&'static str>, tail: Re) -> Rule<Ev> {
    let resource = match resource {
        Some(constant) => ComponentPattern::constant(constant),
        None => ComponentPattern::variable("r"),
    };
    Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("p"),
            ComponentPattern::constant(action),
            resource,
        ),
        tail,
    )
}

fn not_approval(resource: &'static str) -> Test {
    TestExpr::or([
        act(Comparison::Neq, Act::Approve),
        res(Comparison::Neq, resource),
    ])
}

/// The candidate's principal performed `action` on `resource`.
fn my(action: Act, resource: &'static str) -> Test {
    TestExpr::and([
        me(Comparison::Eq),
        act(Comparison::Eq, action),
        res(Comparison::Eq, resource),
    ])
}

// ---------------------------------------------------------------------------------------------
// Policies.

/// Ownership locks (Section 2): an edit takes ownership, which blocks other principals' edits,
/// releases and deletions; a foreign edit since the principal last looked, or a foreign last
/// read, blocks its edits and deletions.
fn lock() -> Vec<Rule<Ev>> {
    let foreign = |action| {
        TestExpr::and([
            here(Comparison::Eq),
            act(Comparison::Eq, action),
            me(Comparison::Neq),
        ])
    };
    let stable = |changes: &[Act]| TestExpr::or([here(Comparison::Neq), none_of(changes)]);
    let owned = since(
        foreign(Act::Edit),
        stable(&[Act::Edit, Act::Release, Act::Delete]),
    );
    let read = since(foreign(Act::Read), stable(&[Act::Read, Act::Delete]));
    let stale = since(
        foreign(Act::Edit),
        TestExpr::and([
            stable(&[Act::Edit, Act::Delete]),
            TestExpr::or([
                here(Comparison::Neq),
                act(Comparison::Neq, Act::Read),
                me(Comparison::Neq),
            ]),
        ]),
    );
    vec![
        forbid(Act::Edit, None, owned.clone()),
        forbid(Act::Release, None, owned.clone()),
        forbid(Act::Delete, None, owned),
        forbid(Act::Edit, None, stale.clone()),
        forbid(Act::Delete, None, stale),
        forbid(Act::Edit, None, read.clone()),
        forbid(Act::Delete, None, read),
    ]
}

/// Git working-tree discipline: the 23-rule table of the earlier junco policy. The last
/// state-changing event on a resource puts it in one of four rows (clean, staged, unstaged by the
/// candidate's principal, unstaged by another), and the last read gives another principal a claim.
fn git() -> Vec<Rule<Ev>> {
    use Act::*;
    let changes = [Edit, Stage, Unstage, Commit, Checkout, Stash, Delete];
    let stable = TestExpr::or([here(Comparison::Neq), none_of(&changes)]);
    let on_r = |actions: &[Act]| TestExpr::and([here(Comparison::Eq), one_of(actions)]);
    let clean = RegexExpr::union([
        RegexExpr::star(test(stable.clone())),
        since(on_r(&[Commit, Checkout, Stash]), stable.clone()),
    ]);
    let staged = since(on_r(&[Stage, Delete]), stable.clone());
    let unstaged = |principal| {
        since(
            TestExpr::and([on_r(&[Edit, Unstage]), me(principal)]),
            stable.clone(),
        )
    };
    let mine = unstaged(Comparison::Eq);
    let other = unstaged(Comparison::Neq);
    let claimed = since(
        TestExpr::and([on_r(&[Read]), me(Comparison::Neq)]),
        TestExpr::or([here(Comparison::Neq), act(Comparison::Neq, Read)]),
    );
    let table: [(Act, &Re); 23] = [
        (Edit, &other),
        (Checkout, &other),
        (Stage, &clean),
        (Stage, &staged),
        (Stage, &other),
        (Stash, &clean),
        (Stash, &staged),
        (Stash, &other),
        (Unstage, &other),
        (Unstage, &clean),
        (Unstage, &mine),
        (Commit, &clean),
        (Commit, &mine),
        (Commit, &other),
        (Delete, &staged),
        (Delete, &mine),
        (Delete, &other),
        (Clean, &other),
        (Edit, &claimed),
        (Delete, &claimed),
        (Clean, &claimed),
        (Checkout, &claimed),
        (Stash, &claimed),
    ];
    table
        .into_iter()
        .map(|(action, tail)| forbid(action, None, tail.clone()))
        .collect()
}

/// Confidentiality: no sending to an external sink after reading the secret, until the secret is
/// declassified.
fn confidentiality() -> Vec<Rule<Ev>> {
    let tail = since(my(Act::Read, "secret"), not_approval("secret"));
    ["email", "http"]
        .into_iter()
        .map(|sink| forbid(Act::Send, Some(sink), tail.clone()))
        .collect()
}

/// Integrity: after reading untrusted content, no consequential action (sending anywhere,
/// deleting anything) until the content is endorsed.
fn integrity() -> Vec<Rule<Ev>> {
    let tail = since(my(Act::Read, "untrusted"), not_approval("untrusted"));
    [Act::Send, Act::Delete]
        .into_iter()
        .map(|action| forbid(action, None, tail.clone()))
        .collect()
}

/// Agents Rule of Two: no consequential action once the principal holds both untrusted input
/// (unendorsed) and private data.
fn rule_of_two() -> Vec<Rule<Ev>> {
    let tail = RegexExpr::intersect([
        since(my(Act::Read, "untrusted"), not_approval("untrusted")),
        ever(my(Act::Read, "secret")),
    ]);
    [Act::Send, Act::Delete]
        .into_iter()
        .map(|action| forbid(action, None, tail.clone()))
        .collect()
}

/// Chinese wall: a principal that read one client's data may not read a competitor's.
fn chinese_wall() -> Vec<Rule<Ev>> {
    const CLIENTS: [&str; 3] = ["bank-a", "bank-b", "bank-c"];
    CLIENTS
        .into_iter()
        .map(|client| {
            let competitor = TestExpr::or(
                CLIENTS
                    .into_iter()
                    .filter(|other| *other != client)
                    .map(|other| res(Comparison::Eq, other)),
            );
            let tail = ever(TestExpr::and([
                me(Comparison::Eq),
                act(Comparison::Eq, Act::Read),
                competitor,
            ]));
            forbid(Act::Read, Some(client), tail)
        })
        .collect()
}

/// Code freeze: no edits or deletions between a freeze and the next thaw.
fn code_freeze() -> Vec<Rule<Ev>> {
    let tail = since(
        act(Comparison::Eq, Act::Freeze),
        act(Comparison::Neq, Act::Thaw),
    );
    [Act::Edit, Act::Delete]
        .into_iter()
        .map(|action| forbid(action, None, tail.clone()))
        .collect()
}

/// Test integrity: after editing the source, a principal may not edit or delete the tests until
/// a reviewer approves the tests.
fn test_integrity() -> Vec<Rule<Ev>> {
    let tail = since(my(Act::Edit, "src"), not_approval("tests"));
    [Act::Edit, Act::Delete]
        .into_iter()
        .map(|action| forbid(action, Some("tests"), tail.clone()))
        .collect()
}

/// Separation of duty: the last pusher of a change may not approve it, and a change may not be
/// merged unless approved since its last push.
fn separation_of_duty() -> Vec<Rule<Ev>> {
    let pushed = TestExpr::and([here(Comparison::Eq), act(Comparison::Eq, Act::Push)]);
    let not_pushed = TestExpr::or([here(Comparison::Neq), act(Comparison::Neq, Act::Push)]);
    let self_review = since(
        TestExpr::and([pushed.clone(), me(Comparison::Eq)]),
        not_pushed.clone(),
    );
    let unreviewed = since(
        pushed,
        TestExpr::and([
            not_pushed,
            TestExpr::or([here(Comparison::Neq), act(Comparison::Neq, Act::Approve)]),
        ]),
    );
    vec![
        forbid(Act::Approve, None, self_review),
        forbid(Act::Merge, None, unreviewed),
    ]
}

/// Deletion budget: a principal may delete at most `limit` resources between approvals.
fn deletion_budget(limit: usize) -> Vec<Rule<Ev>> {
    let deletion = TestExpr::and([me(Comparison::Eq), act(Comparison::Eq, Act::Delete)]);
    let quiet = RegexExpr::star(test(not_approval("deletions")));
    let mut tail = vec![RegexExpr::all()];
    for _ in 0..limit {
        tail.push(test(deletion.clone()));
        tail.push(quiet.clone());
    }
    vec![forbid(Act::Delete, None, RegexExpr::concat(tail))]
}

// ---------------------------------------------------------------------------------------------
// Replay.

/// Names for fresh values: none equals a constant of the corpus.
const FRESH_PRINCIPALS: [&str; 8] = [
    "agent-0", "agent-1", "agent-2", "agent-3", "agent-4", "agent-5", "agent-6", "agent-7",
];
const FRESH_RESOURCES: [&str; 8] = [
    "file-0", "file-1", "file-2", "file-3", "file-4", "file-5", "file-6", "file-7",
];

/// Instantiates a counterexample's components; distinct fresh numbers get distinct new names.
fn concrete(components: &Components<Ev>) -> Ev {
    let name = |value: Value<&'static str>, pool: &[&'static str]| match value {
        Value::Constant(value) => value,
        Value::Fresh(number) => pool[number],
    };
    let Value::Constant(action) = components.action else {
        panic!("declared actions are never fresh");
    };
    Ev {
        principal: name(components.principal, &FRESH_PRINCIPALS),
        action,
        resource: name(components.resource, &FRESH_RESOURCES),
    }
}

/// Whether `rules` deny the counterexample's candidate after its history, by the runtime.
fn denied(rules: &[Rule<Ev>], counterexample: &Counterexample<Ev>) -> bool {
    let store = Arc::new(Store::new().unwrap());
    let rules = rules
        .iter()
        .map(|rule| TraceRule::new(rule.clone(), |_: &Ev| (String::new(), Vec::new())));
    let mut policy = TracePolicy::new(store.clone(), rules).unwrap();
    let history = History::from_events(store, counterexample.history.iter().map(concrete)).unwrap();
    policy
        .decide(&history, &concrete(&counterexample.candidate))
        .unwrap()
        != PolicyDecision::Grant
}

/// Checks that `denying` denies the counterexample and `granting` grants it.
fn replay(denying: &[Rule<Ev>], granting: &[Rule<Ev>], counterexample: &Counterexample<Ev>) {
    assert!(
        denied(denying, counterexample),
        "{counterexample:?} is not denied"
    );
    assert!(
        !denied(granting, counterexample),
        "{counterexample:?} is not granted"
    );
}

// ---------------------------------------------------------------------------------------------
// Measurement.

/// Runs per query, `CORPUS_RUNS` or 5.
fn runs() -> usize {
    std::env::var("CORPUS_RUNS").map_or(5, |runs| runs.parse().expect("CORPUS_RUNS is a count"))
}

/// Median wall time of `query` over [`runs`] runs, and its last result.
fn timed<T>(mut query: impl FnMut() -> T) -> (Duration, T) {
    let runs = runs();
    let mut times = Vec::with_capacity(runs);
    let mut result = None;
    for _ in 0..runs {
        let start = Instant::now();
        let value = query();
        times.push(start.elapsed());
        result = Some(value);
    }
    times.sort_unstable();
    (times[runs / 2], result.unwrap())
}

/// `principal action resource` with fresh values numbered.
fn show(components: &Components<Ev>) -> String {
    fn value(value: Value<&'static str>, kind: &str) -> String {
        match value {
            Value::Constant(value) => value.to_string(),
            Value::Fresh(number) => format!("{kind}{number}"),
        }
    }
    let action = match components.action {
        Value::Constant(action) => format!("{action:?}").to_lowercase(),
        Value::Fresh(_) => unreachable!("declared actions are never fresh"),
    };
    format!(
        "({}, {action}, {})",
        value(components.principal, "p"),
        value(components.resource, "r")
    )
}

struct Policy {
    name: &'static str,
    rules: Vec<Rule<Ev>>,
    ids: Vec<RuleId>,
}

#[derive(Default)]
struct Totals {
    holds: usize,
    refuted: usize,
    exhausted: usize,
    times: Vec<Duration>,
    expanded: usize,
    /// Events in the longest counterexample history.
    longest: usize,
}

impl Totals {
    fn add(&mut self, time: Duration, inclusion: &Inclusion<Ev>, expanded: usize) {
        match inclusion {
            Inclusion::Holds => self.holds += 1,
            Inclusion::Counterexample(counterexample) => {
                self.refuted += 1;
                self.longest = self.longest.max(counterexample.history.len());
            }
            Inclusion::Exhausted => self.exhausted += 1,
        }
        self.times.push(time);
        self.expanded += expanded;
    }

    fn print(&mut self, title: &str) {
        let ms = |time: Duration| time.as_secs_f64() * 1e3;
        self.times.sort_unstable();
        let total = self.times.iter().sum::<Duration>();
        println!(
            "| {title} | {} | {} | {} | {} | {:.3} | {:.3} | {:.3} | {} | {} |",
            self.times.len(),
            self.holds,
            self.refuted,
            self.exhausted,
            ms(self.times[self.times.len() / 2]),
            ms(*self.times.last().unwrap()),
            ms(total),
            self.expanded,
            self.longest,
        );
    }
}

fn main() {
    let mut analyzer = PolicyAnalyzer::new(Domains::infinite().with_actions(ACTS));
    let sources: [(&'static str, Vec<Rule<Ev>>); 10] = [
        ("lock", lock()),
        ("git", git()),
        ("confidentiality", confidentiality()),
        ("integrity", integrity()),
        ("rule-of-two", rule_of_two()),
        ("chinese-wall", chinese_wall()),
        ("code-freeze", code_freeze()),
        ("test-integrity", test_integrity()),
        ("separation-of-duty", separation_of_duty()),
        ("deletion-budget", deletion_budget(3)),
    ];
    let policies = sources
        .into_iter()
        .map(|(name, rules)| {
            let ids = rules
                .iter()
                .map(|rule| analyzer.add_rule(rule).expect("corpus rules compile"))
                .collect();
            Policy { name, rules, ids }
        })
        .collect::<Vec<_>>();
    let all_rules = policies
        .iter()
        .flat_map(|policy| policy.rules.clone())
        .collect::<Vec<_>>();
    let all_ids = policies
        .iter()
        .flat_map(|policy| policy.ids.clone())
        .collect::<Vec<_>>();

    println!("## Policies\n");
    println!("| policy | rules |\n|---|---:|");
    for policy in &policies {
        println!("| {} | {} |", policy.name, policy.rules.len());
    }
    println!("| total | {} |", all_rules.len());

    // Pairwise strictness: does `stricter` deny everything `than` denies?
    let mut strict = Totals::default();
    let mut covered = Totals::default();
    let mut holding = Vec::new();
    let mut covered_rules = Vec::new();
    for stricter in &policies {
        for than in &policies {
            if std::ptr::eq(stricter, than) {
                continue;
            }
            let (time, verdict) = timed(|| {
                analyzer
                    .at_least_as_strict(&stricter.ids, &than.ids)
                    .unwrap()
            });
            if let Inclusion::Counterexample(counterexample) = &verdict.inclusion {
                replay(&than.rules, &stricter.rules, counterexample);
                let history = counterexample.history.iter().map(show).collect::<Vec<_>>();
                println!(
                    "{} not ⊒ {}: {} after [{}]",
                    stricter.name,
                    than.name,
                    show(&counterexample.candidate),
                    history.join(", ")
                );
            } else if verdict.holds() {
                holding.push(format!("{} ⊒ {}", stricter.name, than.name));
            }
            strict.add(time, &verdict.inclusion, verdict.stats.expanded);
            for (index, rule) in than.ids.iter().enumerate() {
                let (time, verdict) = timed(|| analyzer.covered(*rule, &stricter.ids).unwrap());
                if let Inclusion::Counterexample(counterexample) = &verdict.inclusion {
                    replay(&than.rules[index..=index], &stricter.rules, counterexample);
                } else if verdict.holds() {
                    covered_rules.push(format!("{}[{index}] by {}", than.name, stricter.name));
                }
                covered.add(time, &verdict.inclusion, verdict.stats.expanded);
            }
        }
    }

    // Redundancy of each rule in its own policy and in the union of all ten.
    let mut own = Totals::default();
    let mut union = Totals::default();
    let mut redundant_own = Vec::new();
    let mut redundant_union = Vec::new();
    for policy in &policies {
        for (index, rule) in policy.ids.iter().enumerate() {
            let label = format!("{}[{index}]", policy.name);
            let (time, verdict) = timed(|| analyzer.redundant(*rule, &policy.ids).unwrap());
            if let Inclusion::Counterexample(counterexample) = &verdict.inclusion {
                let others = policy
                    .rules
                    .iter()
                    .enumerate()
                    .filter(|(other, _)| *other != index)
                    .map(|(_, rule)| rule.clone())
                    .collect::<Vec<_>>();
                replay(&policy.rules[index..=index], &others, counterexample);
            } else if verdict.holds() {
                redundant_own.push(label.clone());
            }
            own.add(time, &verdict.inclusion, verdict.stats.expanded);
            let (time, verdict) = timed(|| analyzer.redundant(*rule, &all_ids).unwrap());
            if let Inclusion::Counterexample(counterexample) = &verdict.inclusion {
                let position = all_ids.iter().position(|id| id == rule).unwrap();
                let others = all_rules
                    .iter()
                    .enumerate()
                    .filter(|(other, _)| *other != position)
                    .map(|(_, rule)| rule.clone())
                    .collect::<Vec<_>>();
                replay(&all_rules[position..=position], &others, counterexample);
            } else if verdict.holds() {
                redundant_union.push(label.clone());
            }
            if time > Duration::from_millis(10) {
                println!(
                    "slow: {label} redundant in the union: {time:?}, {:?}",
                    verdict.stats
                );
            }
            union.add(time, &verdict.inclusion, verdict.stats.expanded);
        }
    }

    println!(
        "\n## Queries (each timed as the median of {} runs)\n",
        runs()
    );
    println!(
        "| question | queries | holds | refuted | exhausted | median (ms) | max (ms) | total (ms) | expanded | longest counterexample |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
    strict.print("policy at least as strict as policy");
    covered.print("rule covered by policy");
    own.print("rule redundant in its policy");
    union.print("rule redundant in the union");

    println!("\nstrictness holds: {holding:?}");
    println!("rules covered by another policy: {covered_rules:?}");
    println!("redundant in own policy: {redundant_own:?}");
    println!("redundant in union: {redundant_union:?}");
}
