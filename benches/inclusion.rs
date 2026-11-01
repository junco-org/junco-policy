//! Inclusion-checking evaluation: policy questions on junco's git table and marsh's recommended
//! agent policy, scaling families, and random tails, under each search configuration.
//!
//! Run with `cargo bench --bench inclusion`. Pass a workload-name filter to run a subset, for
//! example `cargo bench --bench inclusion -- git`. Each row reports the median wall time over
//! repeated runs, each with a fresh analyzer, and the work counters of one run.

use std::hint::black_box;
use std::time::{Duration, Instant};

use junco_policy::{
    Action, Alphabet, AtomPattern, Bump, Comparison, ComponentPattern, GitPolicy, Head, Inclusion,
    PolicyAnalyzer, RegexExpr, Resource, Rule, RuleId, RuleMode, SearchOptions, SearchStats,
    Strategy, Subsumption, TestExpr,
};

/// States one search may insert before it reports [`Inclusion::Exhausted`].
const BUDGET: usize = 100_000;
/// Minimum measured time per row, and the bounds on repetitions.
const MEASURE: Duration = Duration::from_millis(500);
const MIN_RUNS: usize = 3;
const MAX_RUNS: usize = 25;

#[derive(Clone, Copy)]
struct Configuration {
    name: &'static str,
    options: SearchOptions,
}

fn configuration(
    name: &'static str,
    strategy: Strategy,
    subsumption: Subsumption,
    prune_visited: bool,
    alphabet: Alphabet,
) -> Configuration {
    Configuration {
        name,
        options: SearchOptions {
            strategy,
            subsumption,
            prune_visited,
            alphabet,
            max_items: Some(BUDGET),
        },
    }
}

/// The configurations compared in every table.
fn engines() -> [Configuration; 8] {
    use Alphabet::{Letters, Minterms};
    use Strategy::{Antichain, Brzozowski, Residual, Simple};
    use Subsumption::{Identity, Implication};
    [
        configuration("simple", Simple, Identity, false, Letters),
        configuration("brzozowski", Brzozowski, Identity, false, Letters),
        configuration("residual", Residual, Identity, false, Letters),
        configuration("residual+impl", Residual, Implication, false, Letters),
        configuration("residual/minterms", Residual, Identity, false, Minterms),
        configuration("antichain", Antichain, Identity, false, Letters),
        configuration("antichain+sim", Antichain, Implication, false, Letters),
        configuration("antichain+sim+prune", Antichain, Implication, true, Letters),
    ]
}

/// Tallies of query outcomes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Outcomes {
    holds: usize,
    refuted: usize,
    exhausted: usize,
}

impl Outcomes {
    fn record(&mut self, inclusion: &Inclusion) {
        match inclusion {
            Inclusion::Holds => self.holds += 1,
            Inclusion::Counterexample(_) => self.refuted += 1,
            Inclusion::Exhausted => self.exhausted += 1,
        }
    }
}

/// One measured run: outcomes and summed work counters.
#[derive(Default)]
struct Run {
    outcomes: Outcomes,
    stats: SearchStats,
}

impl Run {
    fn add(&mut self, inclusion: &Inclusion, stats: SearchStats) {
        self.outcomes.record(inclusion);
        self.stats.searches += stats.searches;
        self.stats.inserted += stats.inserted;
        self.stats.expanded += stats.expanded;
        self.stats.steps += stats.steps;
        self.stats.assignments = self.stats.assignments.saturating_add(stats.assignments);
        black_box(inclusion);
    }
}

/// A set of queries run against one fresh analyzer.
type Workload<'workload> = dyn Fn(&mut PolicyAnalyzer<'_>, &mut Run) + 'workload;

fn measure(workload: &Workload<'_>, configuration: Configuration) -> (Duration, Run) {
    let mut times = Vec::new();
    let mut last = Run::default();
    let started = Instant::now();
    while times.len() < MIN_RUNS || (times.len() < MAX_RUNS && started.elapsed() < MEASURE) {
        let arena = Bump::new();
        let mut analyzer = PolicyAnalyzer::with_options(&arena, configuration.options);
        let mut run = Run::default();
        let start = Instant::now();
        workload(&mut analyzer, &mut run);
        times.push(start.elapsed());
        last = run;
    }
    times.sort_unstable();
    (times[times.len() / 2], last)
}

fn header(title: &str) {
    println!("\n### {title}\n");
    println!(
        "| configuration | time (ms) | holds | refuted | exhausted | searches | inserted | expanded | letters | assignments |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
}

fn row(configuration: Configuration, time: Duration, run: &Run) {
    let Run { outcomes, stats } = run;
    println!(
        "| {} | {:.3} | {} | {} | {} | {} | {} | {} | {} | {} |",
        configuration.name,
        time.as_secs_f64() * 1e3,
        outcomes.holds,
        outcomes.refuted,
        outcomes.exhausted,
        stats.searches,
        stats.inserted,
        stats.expanded,
        stats.steps,
        stats.assignments,
    );
}

fn report(title: &str, workload: &Workload<'_>, configurations: &[Configuration]) {
    header(title);
    let mut reference = None;
    for configuration in configurations {
        let (time, run) = measure(workload, *configuration);
        if run.outcomes.exhausted == 0 {
            // Every configuration that finishes must reach the same verdicts.
            let outcomes = (run.outcomes.holds, run.outcomes.refuted);
            assert!(
                *reference.get_or_insert(outcomes) == outcomes,
                "{title}: {} disagrees",
                configuration.name
            );
        }
        row(*configuration, time, &run);
    }
}

// ---------------------------------------------------------------------------------------------
// Policies.

/// Every rule's redundancy in the table, then every rule's vacuity.
fn table_questions(rules: &[Rule]) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) + '_ {
    move |analyzer, run| {
        let ids = add_all(analyzer, rules);
        for rule in &ids {
            let verdict = analyzer.redundant(*rule, &ids);
            run.add(&verdict.inclusion, verdict.stats);
        }
        for rule in &ids {
            let verdict = analyzer.never_fires(*rule);
            run.add(&verdict.inclusion, verdict.stats);
        }
    }
}

/// Pairwise overlap of the distinct tails of a table: `t₁ ∩ t₂ ⊑ ∅` under a bind-all head.
fn tail_overlaps(rules: &[Rule]) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) + '_ {
    move |analyzer, run| {
        let mut tails: Vec<&RegexExpr> = Vec::new();
        for rule in rules {
            if !tails.contains(&&rule.tail) {
                tails.push(&rule.tail);
            }
        }
        let head = Head::new(
            ComponentPattern::variable("p"),
            ComponentPattern::variable("a"),
            ComponentPattern::variable("r"),
        );
        for (index, left) in tails.iter().enumerate() {
            for right in &tails[index + 1..] {
                let overlap = RegexExpr::intersect([(*left).clone(), (*right).clone()]);
                let verdict = analyzer
                    .tail_included(&head, &overlap, &RegexExpr::empty())
                    .expect("table tails compile");
                run.add(&verdict.inclusion, verdict.stats);
            }
        }
    }
}

fn add_all(analyzer: &mut PolicyAnalyzer<'_>, rules: &[Rule]) -> Vec<RuleId> {
    rules
        .iter()
        .map(|rule| analyzer.add_rule(rule).expect("benchmark rules compile"))
        .collect()
}

/// Replicas of the rule builders of marsh's agent policy (`marsh-core/src/shell/agent.rs`).
mod marsh {
    use super::*;

    const PRINCIPAL: &str = "p";

    fn principal_is(comparison: Comparison) -> TestExpr {
        TestExpr::atom(
            comparison,
            AtomPattern::Principal(ComponentPattern::variable(PRINCIPAL)),
        )
    }

    fn action_is(action: Action, comparison: Comparison) -> TestExpr {
        TestExpr::atom(
            comparison,
            AtomPattern::Action(ComponentPattern::constant(action)),
        )
    }

    fn resource_is(kind: &str, class: &str, comparison: Comparison) -> TestExpr {
        TestExpr::atom(
            comparison,
            AtomPattern::Resource(ComponentPattern::constant(Resource::new([kind, class]))),
        )
    }

    fn changed_by_p(class: &str) -> TestExpr {
        TestExpr::and([
            principal_is(Comparison::Eq),
            TestExpr::or([
                TestExpr::and([
                    action_is(Action::Edit, Comparison::Eq),
                    TestExpr::or([
                        resource_is("path", class, Comparison::Eq),
                        resource_is("new", class, Comparison::Eq),
                    ]),
                ]),
                TestExpr::and([
                    action_is(Action::Delete, Comparison::Eq),
                    resource_is("path", class, Comparison::Eq),
                ]),
            ]),
        ])
    }

    fn not_approval(label: &str) -> TestExpr {
        TestExpr::or([
            action_is(Action::Stage, Comparison::Neq),
            resource_is("approve", label, Comparison::Neq),
        ])
    }

    fn since_unapproved(trigger: TestExpr, label: &str) -> RegexExpr {
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(trigger),
            RegexExpr::star(RegexExpr::test(not_approval(label))),
        ])
    }

    fn not_declassified(class: &str) -> TestExpr {
        TestExpr::or([
            principal_is(Comparison::Neq),
            action_is(Action::Stage, Comparison::Neq),
            resource_is("declassify", class, Comparison::Neq),
        ])
    }

    fn since_undeclassified(trigger: TestExpr, class: &str) -> RegexExpr {
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(trigger),
            RegexExpr::star(RegexExpr::test(not_declassified(class))),
        ])
    }

    fn ever(event: TestExpr) -> RegexExpr {
        RegexExpr::concat([RegexExpr::all(), RegexExpr::test(event), RegexExpr::all()])
    }

    fn forbid(action: Action, resource: [&str; 2], tail: RegexExpr) -> Rule {
        Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable(PRINCIPAL),
                ComponentPattern::constant(action),
                ComponentPattern::constant(Resource::new(resource)),
            ),
            tail,
        )
    }

    fn change_heads(class: &str) -> [(Action, [&str; 2]); 3] {
        [
            (Action::Edit, ["path", class]),
            (Action::Edit, ["new", class]),
            (Action::Delete, ["path", class]),
        ]
    }

    pub(super) fn no_contact_after_read(secret_class: &str, peers: &[&str]) -> Vec<Rule> {
        let read = TestExpr::and([
            principal_is(Comparison::Eq),
            action_is(Action::Read, Comparison::Eq),
            TestExpr::or([
                resource_is("path", secret_class, Comparison::Eq),
                resource_is("taint", secret_class, Comparison::Eq),
            ]),
        ]);
        peers
            .iter()
            .map(|peer| {
                forbid(
                    Action::Edit,
                    ["net", peer],
                    since_undeclassified(read.clone(), secret_class),
                )
            })
            .collect()
    }

    pub(super) fn no_egress_after_read(secret_class: &str) -> Vec<Rule> {
        no_contact_after_read(secret_class, &["external", "unknown"])
    }

    pub(super) fn no_network(peer: &str) -> Vec<Rule> {
        vec![forbid(Action::Edit, ["net", peer], RegexExpr::all())]
    }

    pub(super) fn requires_approval(class: &str) -> Vec<Rule> {
        let approval = TestExpr::and([
            action_is(Action::Stage, Comparison::Eq),
            resource_is("approve", class, Comparison::Eq),
        ]);
        let unapproved = RegexExpr::complement(ever(approval));
        change_heads(class)
            .into_iter()
            .map(|(action, resource)| forbid(action, resource, unapproved.clone()))
            .collect()
    }

    pub(super) fn locked_after(edited: &str, locked: &str) -> Vec<Rule> {
        let tail = since_unapproved(changed_by_p(edited), locked);
        change_heads(locked)
            .into_iter()
            .map(|(action, resource)| forbid(action, resource, tail.clone()))
            .collect()
    }

    pub(super) fn tainted_by_exec(programs: &[&str], protected: &[&str]) -> Vec<Rule> {
        let ran = TestExpr::and([
            principal_is(Comparison::Eq),
            action_is(Action::Read, Comparison::Eq),
            TestExpr::or(
                programs
                    .iter()
                    .map(|program| resource_is("exec", program, Comparison::Eq)),
            ),
        ]);
        let mut rules = Vec::new();
        for class in protected {
            let tail = since_unapproved(ran.clone(), class);
            for (action, resource) in change_heads(class) {
                rules.push(forbid(action, resource, tail.clone()));
            }
        }
        rules
    }

    pub(super) fn append_only(class: &str) -> Vec<Rule> {
        [Action::Edit, Action::Delete]
            .into_iter()
            .map(|action| forbid(action, ["path", class], RegexExpr::all()))
            .collect()
    }

    pub(super) fn deletion_budget(limit: usize) -> Vec<Rule> {
        let deletion = TestExpr::and([
            principal_is(Comparison::Eq),
            action_is(Action::Delete, Comparison::Eq),
        ]);
        let quiet = RegexExpr::star(RegexExpr::test(not_approval("delete")));
        let mut tail = vec![RegexExpr::all()];
        for _ in 0..limit {
            tail.push(RegexExpr::test(deletion.clone()));
            tail.push(quiet.clone());
        }
        vec![Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable(PRINCIPAL),
                ComponentPattern::constant(Action::Delete),
                ComponentPattern::variable("r"),
            ),
            RegexExpr::concat(tail),
        )]
    }

    /// The rules of `AgentPolicy::recommended`.
    pub(super) fn recommended() -> Vec<Rule> {
        let mut rules = no_egress_after_read("secret");
        for class in ["secret", "ci", "vcs-hooks"] {
            rules.extend(requires_approval(class));
        }
        rules.extend(locked_after("src", "tests"));
        rules.extend(tainted_by_exec(
            &["curl", "wget"],
            &["ci", "lockfile", "vcs-hooks"],
        ));
        rules
    }
}

/// Strictness between marsh policy variants: adding rules keeps a policy at least as strict, and
/// the converse fails unless the added rules are redundant.
fn marsh_strictness(analyzer: &mut PolicyAnalyzer<'_>, run: &mut Run) {
    let recommended = add_all(analyzer, &marsh::recommended());
    let mut extra = Vec::new();
    extra.extend(marsh::no_network("external"));
    extra.extend(marsh::append_only("logs"));
    extra.extend(marsh::deletion_budget(3));
    let extra = add_all(analyzer, &extra);
    let extended = recommended
        .iter()
        .chain(&extra)
        .copied()
        .collect::<Vec<_>>();
    for (stricter, than) in [(&extended, &recommended), (&recommended, &extended)] {
        let verdict = analyzer.at_least_as_strict(stricter, than);
        run.add(&verdict.inclusion, verdict.stats);
    }
    // The example of the paper: egress after a read is redundant beside a network ban.
    let ban = add_all(analyzer, &marsh::no_network("external"))[0];
    let egress = add_all(analyzer, &marsh::no_egress_after_read("secret"))[0];
    let verdict = analyzer.redundant(egress, &[egress, ban]);
    run.add(&verdict.inclusion, verdict.stats);
}

/// A deletion budget of `limit` is at least as strict as any larger budget, and no budget is
/// stricter than a smaller one.
fn deletion_budgets(limit: usize) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) {
    move |analyzer, run| {
        let small = add_all(analyzer, &marsh::deletion_budget(limit));
        let large = add_all(analyzer, &marsh::deletion_budget(limit + 1));
        let verdict = analyzer.at_least_as_strict(&small, &large);
        run.add(&verdict.inclusion, verdict.stats);
        let verdict = analyzer.at_least_as_strict(&large, &small);
        run.add(&verdict.inclusion, verdict.stats);
    }
}

// ---------------------------------------------------------------------------------------------
// Synthetic families.

fn head() -> Head {
    Head::new(
        ComponentPattern::variable("p"),
        ComponentPattern::constant(Action::Edit),
        ComponentPattern::variable("r"),
    )
}

fn test(test: TestExpr) -> RegexExpr {
    RegexExpr::test(test)
}

fn read() -> TestExpr {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Read)),
    )
}

fn any() -> RegexExpr {
    test(TestExpr::true_test())
}

/// `Σ*·Read·⊤^w·Read ⊑ Σ*·Read·⊤^{w+1}`: the right side's subset construction has `2^{w+1}`
/// states, but a read `w+1` events before the end already settles the inclusion.
fn nth_from_last(width: usize) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) {
    move |analyzer, run| {
        let mut left = vec![RegexExpr::all(), test(read())];
        left.extend(std::iter::repeat_n(any(), width));
        left.push(test(read()));
        let mut right = vec![RegexExpr::all(), test(read())];
        right.extend(std::iter::repeat_n(any(), width + 1));
        let verdict = analyzer
            .tail_included(&head(), &RegexExpr::concat(left), &RegexExpr::concat(right))
            .expect("family tails compile");
        run.add(&verdict.inclusion, verdict.stats);
    }
}

fn resource_is(comparison: Comparison, constant: Option<usize>) -> TestExpr {
    let pattern = match constant {
        Some(index) => ComponentPattern::constant(Resource::new([format!("k{index}")])),
        None => ComponentPattern::variable("r"),
    };
    TestExpr::atom(comparison, AtomPattern::Resource(pattern))
}

fn ever(event: TestExpr) -> RegexExpr {
    RegexExpr::concat([RegexExpr::all(), test(event), RegexExpr::all()])
}

/// `Σ*·(R ≐ κ_R)·Σ*` against its case analysis over `n` resource constants: holds only by
/// splitting on how `κ_R` compares with each constant.
fn register_cases(constants: usize) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) {
    move |analyzer, run| {
        let own = resource_is(Comparison::Eq, None);
        let mut cases = (0..constants)
            .map(|index| {
                ever(TestExpr::and([
                    own.clone(),
                    resource_is(Comparison::Eq, Some(index)),
                ]))
            })
            .collect::<Vec<_>>();
        let mut otherwise = vec![own.clone()];
        otherwise.extend((0..constants).map(|index| resource_is(Comparison::Neq, Some(index))));
        cases.push(ever(TestExpr::and(otherwise)));
        let verdict = analyzer
            .tail_included(&head(), &ever(own), &RegexExpr::union(cases))
            .expect("family tails compile");
        run.add(&verdict.inclusion, verdict.stats);
    }
}

/// Deterministic xorshift generator.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

fn random_atom(rng: &mut Rng) -> TestExpr {
    let comparison = if rng.below(3) == 0 {
        Comparison::Neq
    } else {
        Comparison::Eq
    };
    let pattern = match rng.below(8) {
        0 => AtomPattern::Principal(ComponentPattern::constant("a")),
        1 => AtomPattern::Principal(ComponentPattern::constant("b")),
        2 => AtomPattern::Principal(ComponentPattern::variable("p")),
        3 => AtomPattern::Action(ComponentPattern::constant(Action::Read)),
        4 => AtomPattern::Action(ComponentPattern::constant(Action::Stage)),
        5 => AtomPattern::Resource(ComponentPattern::constant(["x"])),
        6 => AtomPattern::Resource(ComponentPattern::constant(["y"])),
        _ => AtomPattern::Resource(ComponentPattern::variable("r")),
    };
    TestExpr::atom(comparison, pattern)
}

fn random_test(rng: &mut Rng, depth: usize) -> TestExpr {
    match (depth, rng.below(8)) {
        (0, _) | (_, 0..=3) => random_atom(rng),
        (_, 4 | 5) => TestExpr::and([random_test(rng, depth - 1), random_test(rng, depth - 1)]),
        (_, 6) => TestExpr::or([random_test(rng, depth - 1), random_test(rng, depth - 1)]),
        _ => TestExpr::true_test(),
    }
}

/// A random temporal pattern of the kinds policies use, over random tests.
fn random_pattern(rng: &mut Rng) -> RegexExpr {
    let first = test(random_test(rng, 1));
    let second = test(random_test(rng, 1));
    match rng.below(5) {
        // Some event satisfied the first test.
        0 => RegexExpr::concat([RegexExpr::all(), first, RegexExpr::all()]),
        // The first test held at some event and the second at every later one.
        1 => RegexExpr::concat([RegexExpr::all(), first, RegexExpr::star(second)]),
        // Every event satisfied the first test.
        2 => RegexExpr::star(first),
        // The first test held exactly two events before the end.
        3 => RegexExpr::concat([RegexExpr::all(), first, any(), any()]),
        // The first test held, and later the second.
        _ => RegexExpr::concat([
            RegexExpr::all(),
            first,
            RegexExpr::all(),
            second,
            RegexExpr::all(),
        ]),
    }
}

/// A Boolean combination of `depth` levels over random patterns.
fn random_tail(rng: &mut Rng, depth: usize) -> RegexExpr {
    if depth == 0 {
        return random_pattern(rng);
    }
    let child = |rng: &mut Rng| random_tail(rng, depth - 1);
    match rng.below(4) {
        0 => RegexExpr::union([child(rng), child(rng)]),
        1 => RegexExpr::intersect([child(rng), child(rng)]),
        2 => RegexExpr::complement(child(rng)),
        _ => child(rng),
    }
}

/// Random pairs of policy-shaped tails of the given Boolean depth.
fn random_pairs(depth: usize, count: usize) -> Vec<(RegexExpr, RegexExpr)> {
    let mut rng = Rng(0x2545_F491_4F6C_DD1D ^ depth as u64);
    (0..count)
        .map(|_| (random_tail(&mut rng, depth), random_tail(&mut rng, depth)))
        .collect()
}

fn random_inclusions(
    pairs: &[(RegexExpr, RegexExpr)],
) -> impl Fn(&mut PolicyAnalyzer<'_>, &mut Run) + '_ {
    move |analyzer, run| {
        for (left, right) in pairs {
            let verdict = analyzer
                .tail_included(&head(), left, right)
                .expect("random tails compile");
            run.add(&verdict.inclusion, verdict.stats);
        }
    }
}

fn main() {
    let filter = std::env::args()
        .skip(1)
        .find(|argument| !argument.starts_with('-'));
    let selected = |name: &str| filter.as_deref().is_none_or(|filter| name.contains(filter));
    let engines = engines();

    let git = GitPolicy::rules();
    if selected("git") {
        report(
            "git: redundancy and vacuity of each of the 23 rules",
            &table_questions(&git),
            &engines,
        );
        report(
            "git: pairwise overlap of distinct tails",
            &tail_overlaps(&git),
            &engines,
        );
    }
    let recommended = marsh::recommended();
    if selected("marsh") {
        report(
            "marsh: redundancy and vacuity of each recommended rule",
            &table_questions(&recommended),
            &engines,
        );
        report(
            "marsh: pairwise overlap of distinct tails",
            &tail_overlaps(&recommended),
            &engines,
        );
        report(
            "marsh: strictness between policy variants",
            &marsh_strictness,
            &engines,
        );
    }
    if selected("budget") {
        for limit in [1, 2, 4, 8] {
            report(
                &format!("budget: deletion budgets {limit} and {}", limit + 1),
                &deletion_budgets(limit),
                &engines,
            );
        }
    }
    if selected("nth") {
        for width in [2, 4, 6, 8, 10, 12, 14] {
            report(
                &format!("nth: read {} events before the end, w = {width}", width + 2),
                &nth_from_last(width),
                &engines,
            );
        }
    }
    if selected("registers") {
        for constants in [1, 2, 4, 8, 12, 16, 20] {
            report(
                &format!("registers: case analysis over {constants} resource constants"),
                &register_cases(constants),
                &engines,
            );
        }
    }
    if selected("random") {
        for depth in [1, 2, 3, 4] {
            let pairs = random_pairs(depth, 200);
            report(
                &format!("random: 200 pairs of depth-{depth} policy-shaped tails"),
                &random_inclusions(&pairs),
                &engines,
            );
        }
    }
}
