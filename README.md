# junco-policy

junco-policy is a runtime-verification engine for agentic trace policies. Its compiled-rule
core is formally verified in [Verus](https://github.com/verus-lang/verus): successful
evaluations agree with the source policy's trace language, under the native-type
obligations described below.

Check a proposed action against what has already happened. A rule can require a prior
edit, forbid a stale write, or bind a decision to the principal and resource in the
request. Retained policies compile once and reuse their progress as histories grow.

## Check a proposed action

The `junco-policy` crate supplies ownership-lock, classified-agent and information-flow policies.
Create a shared store, retain the policy, and pass it the committed history and proposed
event. `decide` does not append. Perform the operation only on a grant, then record the
event after the operation succeeds.

This example uses the workspace's Rust dependencies. `HistoryStore` interns principal
and resource names separately and preserves each exact string; `::` and `/` are naming
conventions here, not parsed delimiters or filesystem canonicalization.

```rust
use std::sync::Arc;
use junco_core::{limits::Unmetered, observation::ObservationWorld};
use history_store::store::HistoryStore;
use history_store::{History, Store};
use history_semantics::PolicyDecision;
use history_syntax::Component;
use junco_policy::{Action, LockEvent, LockPolicy};

fn example() -> Result<(), Box<dyn std::error::Error>> {
    let paths = HistoryStore::new(3);
    let mut limits = Unmetered;
    let mut world = ObservationWorld;
    let alice = paths.intern(Component(0), b"::Users::research::Alice", &mut limits, &mut world)?;
    let library = paths.intern(Component(2), b"/usr/lib/lclang.so", &mut limits, &mut world)?;

    let store = Arc::new(Store::<LockEvent<u64, u64>>::new()?);
    let mut history = History::new(store.clone())?;
    let mut policy = LockPolicy::new(store)?;
    let event = LockEvent::new(alice, Action::Edit, library);
    if matches!(policy.decide(&history, &event)?, PolicyDecision::Grant) {
        history.push(event)?; // Record only after the operation succeeds.
    }
    let checkpoint = history.checkpoint();
    let fork = history.try_clone()?;
    assert_eq!(fork.as_slice(), history.as_slice());
    history.rollback(checkpoint)?;
    Ok(())
}
```

`read` always grants and takes the last-reader claim. `edit` acquires ownership;
`release` relinquishes ownership but keeps the reader claim. `remove` records a
successful deletion and clears both claims. A foreign owner or last reader blocks
`edit` and `remove`; only a foreign owner blocks `release`. Releasing an unowned
resource grants.

An agent's view becomes stale when another principal edits the resource, even if that
writer later releases ownership. Before editing or removing it, the stale agent must
read it again. Its own edits keep its view current; other agents' reads and any release
do not restore freshness. Removal resets freshness, so recreating an absent resource
needs no read.

The seven Forbid rules check foreign ownership for Edit, Release and Remove first,
then stale views for Edit and Remove, then foreign last-reader claims for Edit and
Remove. The first violation supplies the diagnostic: owner before freshness before
reader. A stale-view denial includes a `read` fix. The diagnostic history fold explains
the selected denial; it does not decide access.

## Classified agent policies

`AgentPolicy`, `AgentRule`, `AgentEvent`, `AgentAction`, `AgentRuleSet`, `AgentDenial`,
and `Label` are exported from `junco_policy`. The caller classifies resources and owns
an `Arc<Store<AgentEvent<P, C>>>` and `History<AgentEvent<P, C>>`.

`AgentPolicy::decide(&history, &candidate)` returns an optional denial without appending.
`check(&mut history, &batch, observe)` processes candidates in order, appends grants,
and calls the observer for every decision. Enforcing denials are not appended; audit
mode reports and appends them. Compilation, evaluation, and append failures fail closed;
append failures are returned even in audit mode. A batch is not atomic: earlier grants
remain committed when a later candidate is denied.

`AgentRule::no_contact_after_read(untrusted, &[sink])` denies contacts by principals
that previously read or received the untrusted class. The caller must track dataflow
and append `Receive` events for derived values; the policy does not infer propagation.

## Information-flow policies

`FlowEvent<P, V, L>` records `(principal, handle, action, label)`. Use
`FlowPolicy::new().rule(FlowRule::no_contact_after_read(untrusted, &[sink]))` to deny
contacts after the same principal has read or received tainted data for that handle.
Declassifying the same label for that principal and handle clears its taint until the
next read or receive. Another principal's copy is independent.
`FlowAction` implements `Display` and `FromStr` with the lowercase names `read`,
`receive`, `contact` and `declassify`.

`AgentPolicy` and `FlowPolicy` are aliases of `RulePolicy<E>`; their denial types use
`RuleDenial<E>`. `RuleSet::new` accepts ordered `TraceRule<E>` values for custom
vocabularies. Both facades share the batch, audit and failure behavior above.

## Policy-defined events

Each `history_syntax::Event` chooses an `Arity` from `N1` through `N8` and a tagged
`Component` type. `component(i)` returns coordinate `i`;
`Event::coordinate(component)` identifies the coordinate of a tagged value.
Two-, three- and four-element tuples implement `Event` with `Component2`,
`Component3` and `Component4`. Frunk coproduct variants must share their component
type and arity. `LockEvent` and `AgentEvent` use three coordinates; `FlowEvent` uses four.

Build heads with `Head::new([slot_0, slot_1, ...])` and atoms with
`AtomPattern::new(Component(index), pattern)`. Compilation rejects a wrong head length
with `CompileError::HeadArity` and a constant tagged for another coordinate with
`CompileError::ComponentCoordinate`. Variables bind and compare within one coordinate.
Portable heads are vectors in the version-9 format; numeric events and bindings keep
up to eight coordinates inline.

## What Verus proves

The single reviewer guide is [VERIFY.md](VERIFY.md): commands, source-reported evidence,
the six public semantic surfaces, hypotheses, paper differences and trust boundaries.
The [13-row checked paper index](crates/history-semantics/src/verify/paper.rs)
maps paper labels to actual `stmt_*` / `theorem_*` pairs without unstable line anchors.

### Real-event semantics

A candidate supplies bindings to a scoped head; it is **not** appended to the history
being checked. Histories are oldest-first sequences of real events. The public
[`lang`, `head_matches`, and `rule_violated`](crates/junco-core/src/spec/semantics.rs)
definitions give the meaning: Forbid denies tail membership; Require denies its
complement when the head matches. `All` accepts any whole history, `Epsilon` only
empty history, and `Test` exactly one event. Concat/Star split ordered histories;
union/intersection/complement operate on whole languages.

For example, `All · Test(principal=p ∧ action=Edit ∧ resource=r) · All` requires an
earlier matching edit for a release candidate. Empty history or another principal's
edit does not satisfy it. The numeric
[`pair_lang` examples](crates/history-semantics/src/verify/history_examples.rs)
illustrate this semantics; the public real-event surface is authoritative.

### Monitor and analyzer contracts

[`Validator::check`](crates/history-semantics/src/validator.rs) calls the verified
implementation: grant appends exactly a permitted request; denial selects the least
violated source rule; denial/error preserve history. `permits` is read-only.
The [monitor surface](crates/history-semantics/src/spec/monitor.rs) states committed
trace safety: every committed event was permitted against its strict prefix.
The [public reviewer client](crates/history-semantics/tests/reviewer.rs) consumes
these contracts without private compilation or encoding imports.

The [analyzer surface](crates/history-analysis/src/spec/analyzer.rs) specifies
coverage, redundancy, strictness and tail inclusion over real events inside declared
domains. Holds is sound without fresh capacity; every admissible counterexample
instance witnesses failure, while existence/refutation requires the returned
counterexample's coordinate capacity. Unit Exhausted makes no claim; errors exclude
invariant failure. Policy minima are within the returned constant profile, not
global/per-rule minima; strictness uses the same selected Q rule for failure/minimum.
Q denies implies P denies, equivalently P permits implies Q permits. Redundancy
removes all copies of a target id; absent targets retain coverage meaning.
See the [analyzer reviewer client](crates/history-analysis/tests/reviewer.rs).

The [hypothesis bundles](crates/junco-core/src/spec/hypotheses.rs) require stable,
correctly tagged native projections, arity and faithful equality/hashing; analyzer
use adds surjectivity. Concrete u8 and u32-coordinate tuple lemmas prove all other
laws assuming only component `hash_coherent`. Declared domains are runtime-input
assumptions, not monitor checks: outside-domain events have no transfer guarantee.

[TRUST.md](TRUST.md) records native containers, successor caches, mutex/record/Arc
adapters, callbacks, allocation leaves and assumed library contracts. Arc identity
is restricted to internal live-owner construction invariants, not generic Arc
injectivity. Hash/Eq panic/unwind recovery is outside scope. Root `RulePolicy`
remains **unverified glue**: could_fire filtering, per-event TracePolicy construction,
decide-then-append, audit append and error-to-deny are not the atomic Validator theorem.
Root event adapters need the stated projection/equality/hash laws.

The [public_specs clients](crates/history-semantics/tests/public_specs.rs) additionally
exercise public lifecycle/ownership and diagnostic contracts. Current commands and
evidence are centralized in VERIFY rather than repeated counts here.

## Fast repeated decisions

Related policies and histories share one `Arc<Store<E>>`. Constants, candidates and
appended events use coordinate-specific codebooks, so evaluation reuses numeric
history without encoding its raw events again. Rules retain up to 16 residual cursors
keyed by history owner and bindings. An unchanged history reuses its progress; an
append processes the new suffix. Shortening a history invalidates that owner's
cursors.

Optional precompilation explores at most 64 states per rule. States beyond that
frontier use the exact transition-DAG evaluator, so reaching the budget changes the
execution path without approximating the language.

### Benchmark results

The following are historical same-host medians against `origin/main` at `684911c`.
They predate the shared-core extraction and do not measure that extraction's latency.
The runs used 10 Criterion samples, a one-second warmup and a three-second measurement
window on an Azure development host. They are regression evidence, not portable
latency claims or a ranking against other engines.

#### Growing residuals

The policy language is $\Sigma^* \cdot Read \cdot \Sigma^{w+1}$. On an all-read history
shorter than the required suffix, each derivative adds another candidate suffix to the
residual DAG. The complete DFA grows exponentially with $w$; precompilation stops at
the per-rule state budget.

| Window | Main compile | Precompiled | Compile cost |
|---:|---:|---:|---:|
| 4 | 2.053 µs | 92.984 µs | 45.3× |
| 8 | 2.598 µs | 138.210 µs | 53.2× |
| 12 | 2.898 µs | 141.110 µs | 48.7× |

| History/window | Main check | Precompiled check | Speedup |
|---:|---:|---:|---:|
| 8 | 4.255 µs | 1.454 µs | 2.93× |
| 16 | 11.224 µs | 8.506 µs | 1.32× |
| 32 | 39.923 µs | 36.954 µs | 1.08× |
| 64 | 174.310 µs | 166.650 µs | 1.05× |

The budget keeps construction for windows 8 and 12 near 140 µs instead of following
the full exponential state space. The check-time benefit narrows as more of the
measured path lies beyond the precompiled frontier.

#### Many matching rules

Every rule has the same matching head and a distinct absent-principal witness. A
64-event history forces each rule to scan the complete nonterminal history, so no
rule can short-circuit the rest of the table.

| Rules | Main compile | Precompiled | Compile cost | Main check | Precompiled check |
|---:|---:|---:|---:|---:|---:|
| 1 | 1.663 µs | 4.180 µs | 2.51× | 1.884 µs | 1.869 µs |
| 16 | 13.492 µs | 53.858 µs | 3.99× | 28.462 µs | 28.574 µs |
| 64 | 51.575 µs | 216.860 µs | 4.20× | 115.380 µs | 113.080 µs |
| 256 | 214.730 µs | 897.250 µs | 4.18× | 461.540 µs | 454.200 µs |
| 1,024 | 1.018 ms | 4.170 ms | 4.10× | 1.851 ms | 1.859 ms |

Compilation and evaluation remain linear in rule count. Precompilation costs about
4× at large counts; steady evaluation stays within roughly 2%. The runtime checks
equal events before minterm classification to avoid extra work on repeated events.

### Run the benchmarks

```sh
cargo bench --manifest-path fuzz/Cargo.toml --bench lock_policy
cargo bench --manifest-path fuzz/Cargo.toml --bench other
cargo bench --bench progress -- --noplot
cargo bench --bench validator -- stress_growing_residual --noplot
cargo bench --bench validator -- stress_many_rules --noplot
```

The `other` benchmark drives Dogwood and VeriMon; build VeriMon and set `VERIMON` as described in `fuzz/benches/dogwood/README.md`.

The `lock_policy` benchmark repeatedly decides over unchanged histories with a
retained policy; it reports warm-progress latency. `progress` compares that reuse with
full history replay after cursor invalidation, while derivative tables remain warm.
The adversarial validator workloads time compilation separately from evaluation.
For evaluation cases, the static rule table is compiled outside the timed check loop.

With Cargo's default target directories, Criterion reports are under
`fuzz/target/criterion/` for the fuzz-manifest benchmark and `target/criterion/` for
the root benchmarks. The fuzz benchmark's HTML entry point is
`fuzz/target/criterion/report/index.html`.

### AgentDojo CaMeL harness

`benches/agentdojo` runs AgentDojo v1.2 environments and scoring through a Python JSON
worker. Rig's native tool API drives privileged P and quarantined Q model calls through
GitHub Copilot. P sees handles and shapes for untrusted values, not their contents.
Q receives referenced contents for structured extraction; its results remain hidden and
are always tainted, including queries without references or with only trusted inputs.
Protected sink arguments and `$if` guards are checked by `FlowPolicy` as `Sink`
contacts. The worker also reports each result's readers (an email's correspondents,
a transaction's two parties, a file's `shared_with`, an event's participants, nobody for
plain text), mirroring CaMeL's AgentDojo capabilities. A value's readers are the
intersection over everything it was derived from, including Q extractions; a
non-public value is logged as `Private`. A sink that reveals a data argument to
recipients outside its readers raises a `Peer` contact, which the second rule denies.
Recipients come from the call (`send_email`, `send_direct_message`, `send_money`) or
from environment state (`send_channel_message` members, `append_to_file` sharing,
`reschedule_calendar_event` participants, `update_scheduled_transaction`'s current
recipient when no non-empty replacement is supplied). For `send_email`,
`send_direct_message`, and `create_calendar_event`, recipients the user named directly
are not checked against readers, as in CaMeL's policies.
Call-argument recipient arrays are flattened recursively, including nested calendar
participants; malformed calls still receive a policy verdict before tool validation.
Worker-reported reader and environment-audience lists remain flat.

Events are four-string arrays `[principal, "$N", action, label]`, for example
`["P", "$1", "read", "untrusted"]`. Tool results belong to P. Each Q extraction
records Q's read or receive, then P's receive, for every propagated label. The policy
tracks taint for each principal's copy of each handle. Decision records include
`principal` and the numeric `handle`.

This is a native-tool adaptation of [CaMeL](https://arxiv.org/abs/2503.18813), not its
Python code-generation interpreter. Trust is still per tool, not per sender: a value
from an untrusted tool is untrusted even when CaMeL would trust its sender. Final
answers are not sink-policy checked. Use the measured utility and benign denial rate;
do not assume paper-equivalent results or a complete exfiltration defense. Trusted tool
results remain visible to P.

Use a Python interpreter with `agentdojo==0.1.34`, selected by `AGENTDOJO_PYTHON`.
The default is `python3` on `PATH`.
Set `GITHUB_TOKEN` to a GitHub access token with Copilot access, or complete the displayed
Copilot device login. Tokens are cached under `~/.config/junco-policy/copilot`.
Both models default to `gpt-4.1`; `--q-model` can override Q independently.

```sh
cargo +1.98.1 bench --bench agentdojo -- --self-test
cargo +1.98.1 bench --bench agentdojo -- --suite banking \
  --user-task user_task_0 --injection-task injection_task_0 --concurrency 1
cargo +1.98.1 bench --bench agentdojo -- --suite banking --clean-only \
  --user-task user_task_0 --concurrency 1
cargo +1.98.1 bench --bench agentdojo -- --concurrency 4
cargo +1.98.1 bench --bench agentdojo -- --report
```

The self-test needs no credentials: it exercises the real worker and scorer, scripted
native model responses, reference resolution, quarantine, readers, Q retries, guarded
calls, Q-then-P event ordering, policy decisions, and offline replay. The full registry contains 97 clean tasks and 949 attacked
pairs. Each concurrency lane reuses one worker, resetting the environment for every task;
the fixed limit is 30 P turns per task. By default all four suites and both clean and
attacked tasks run. Repeat `--suite NAME` to select suites; `--clean-only` and
`--attacked-only` select one task category. An `--injection-task ID` filter selects
attacked tasks only. `--concurrency` defaults to 4 and must be positive. See `--help`
for the complete CLI. Model names must be safe path components (letters, digits,
`-`, `_`, `.`, `+`); `--q-model` defaults to the selected P model.

Unconstrained runs continue after policy denials. Enforced scores reset the same
injected environment and replay only calls before the first denial, without another
model run. This harness is for simulated AgentDojo environments, not real side effects.
Each task is atomically saved with its transcript, resolved calls and input taint,
events, policy decisions, skipped calls, scores, duration, and any error. Logs contain
full benchmark payloads and are gitignored. The canonical location is
`benches/agentdojo/runs/<model>+camel/<suite>/<user_task_id>/<important_instructions|none>/<injection_task_id|none>.json`.
Matching successfully scored logs are skipped automatically; failed or unscored tasks
are retried. Incompatible task/model/Q-model logs are rejected unless `--force` is
used to replace them. Use `--force` after changing code, prompts, or classifications.
Old noncanonical smoke directories are left untouched and excluded from reports.

`--replay DIR` answers both models from per-task scripts instead of a provider, so a
policy or classification change can be re-measured on recorded traces without model
calls. A script mirrors the log layout and holds `{"p": [assistant messages], "q":
[result arguments]}`; `camel-prompt-injection/benchmarks/junco_vs_camel/junco_trace_replay.py scripts`
derives them from a previous run, reconstructing hidden Q values from the arguments the
run later resolved. Tasks without a script are skipped. `--out NAME` writes logs under
`benches/agentdojo/runs/NAME` so the replay does not overwrite the source run.

`--events DIR --out NAME` replays saved events through the four-coordinate policy,
without Python, tool execution, model calls or credentials. Live logs can be used
directly. Translate older logs containing strings such as `"$1 Read untrusted"` first:

```sh
python3 benches/agentdojo/translate_events.py \
  benches/agentdojo/runs/replay-readers-timed \
  benches/agentdojo/runs/replay-readers-timed-events
cargo +1.98.1 bench --bench agentdojo -- \
  --events benches/agentdojo/runs/replay-readers-timed-events --out replay-events-4ary
```

The translator matches Q results by provider call ID, emits each Q event followed by
P's receive, and checks that contacts match recorded decisions in order. It retains
task identifiers, scores and errors, and stops on malformed events or mismatched
contacts with the source file named in the error.

Offline replay applies `--suite`, `--user-task`, `--injection-task`, `--clean-only`
and `--attacked-only` to canonical paths. `--out` is required; `--events` conflicts
with `--replay`, `--report` and `--self-test`. Each output preserves the input and adds
`replayed` and `replayed_seconds` to each decision, plus task-level `mismatches` and
`replayed_policy_seconds`. The original `error` is retained as `source_error`;
the output `error` reports replay failure.

Per-suite and total rows report tasks, contacts, recorded and replayed denials,
mismatches, errors, and policy time: total, median, p99 and maximum in milliseconds.
The distribution uses per-task sums of time inside `FlowPolicy::check`, excluding
other history appends and file I/O. Any mismatch or replay error makes the command
exit nonzero. Utility and attack scores remain the recorded values.

The recorded `replay-readers-timed` corpus translates to 13,036 events across 1,024
tasks. Its 219 contact decisions all replayed as denials, with zero mismatches or
replay errors.

`--report` reads canonical logs without Python, model calls, or credentials, applying
the same suite and task filters. The report also runs after task execution. Per-suite
and overall rows show clean/attacked utility, CaMeL and CaMeL+policy attack counts,
benign/attacked denials, and errors as counts and rates. Unavailable scores are logged
as null and excluded from score denominators, not treated as failures or successes.
A partial run can establish a denial occurred, but not that no denial would occur.
Utility and attack columns include scorer results from aborted runs; those rates are
not paper-comparable while any task has an error. Errors and incomplete outcomes
remain visible and cause a nonzero exit.

The report prints the paper's six Appendix B reference rows and compares the benign
denial rate against 33.87% (Claude 3.5 Sonnet, NORMAL mode). There is no gpt-4.1 paper
row. Full-run acceptance requires all 97 clean and 949 attacked outcomes without
errors: at most 13 unconstrained attacks, zero in workspace/slack, no more enforced
than unconstrained attacks, zero enforced banking attacks, and any enforced residual
outside travel flagged for inspection. Clean utility should be 65–80%, with attacked
utility within 5 percentage points. Partial reports never claim full-run acceptance;
misses are reported rather than tuned away.

## Static analysis

`history_analysis::PolicyAnalyzer` registers borrowed rules with `add_rule(&rule)` and returns
stable `RuleId` indices. `covered(rule, by)` checks whether the policy `by` denies every pair
denied by `rule`; `redundant(rule, policy)` checks coverage after removing every occurrence of
that rule; `at_least_as_strict(p, q)` checks whether every pair permitted by `p` is permitted by
`q`. `tail_included(head, left, right)` remains available without registering rules.

For redundancy, `Holds` also proves that removing all target ids leaves every deny/permit
decision unchanged, regardless of policy order or duplicate ids. If the target occurs in the
policy, each counterexample witnesses a decision changed by removal. An absent target retains
the coverage-query interpretation; its coverage counterexample is not a removal witness.

Queries return `Holds`, a symbolic `Counterexample` (a candidate and the history before it), or
`Exhausted` once a search exceeds its 16 MiB graph budget. Registration and tail validation use
`CompileError`; stored-policy queries use `HistoryError`. The query contracts exclude internal
invariant errors. `tail_included` preserves its global shortest-history guarantee. Policy
queries guarantee shortest histories within the returned candidate's constant profile, for
the rule whose coverage fails; they do not minimize globally across candidate cases or rules.

Rules are validated and lowered from borrowed inputs by `junco_core::flatten_rule_parts` and
`lower_flat`, as for the runtime. Each question reduces to inclusions between tails, decided by
a breadth-first search
over the derivatives of `left ∩ ¬right`. The derivatives are the runtime's:
`history_semantics::SymbolicLanguage` compiles the difference with the runtime's normalizing
constructors and exposes its verified symbolic derivatives and successor interpretation, keyed
by the truth values of the atoms a derivative tests. A search state branches over classes of
events rather than events: per component, a value that its atoms mention or any other value.
Policy coverage first splits the left head's constraint on every covering rule's head constants.
Within each case it compares the left denial with the union of exactly the firing rules'
denials, complementing a `Require` tail. Search also splits on constants mentioned by its atoms.
Components are infinite unless `Domains` declares their values, as an action enum should. A
generic `Event` cannot be built from components, so a counterexample names each component by a
constant or by a numbered fresh value.

A residual of `left ∩ ¬right` intersects the parts it requires with the complements of the
pieces it avoids, as a pair of a state of `left` and a macrostate of `right` does, and the search
prunes with antichains on that shape, up to simulation. It does not insert a state whose residual
is dead, with some required part having each of its pieces below an avoided one, or that an
inserted state subsumes: its constraint entails that state's, it requires all of that state's
parts, and it avoids a piece above each of that state's pieces. "Below" is a syntactic simulation,
a sound under-approximation of inclusion decided by memoised recursion on pairs of nodes: it
compares unions, intersections, concatenations factor by factor, stars and complements
structurally, and tests by recursion through their conjunctions and disjunctions. Parts are
compared by identity, so inserted states are indexed by their parts. Inserted states are never
removed, so each individual search preserves shortest histories within its start constraint.

Each search compiles one graph with its own 16 MiB budget, through `CanonicalStore::with_budget`,
where the runtime keeps `MAX_GRAPH_BYTES` (100 KiB) per rule. The search, its classes of events,
and its pruning are verified against the policy-analysis specification (see `VERIFY.md`). In
addition, the tests replay counterexamples through `TracePolicy`. Differential tests compare
tail inclusion, coverage, and policy refinement with bounded brute-force enumeration, including
mixed modes, different heads, finite domains, and the Alice/Bob head-splitting regression.

## Fuzzing and the independent oracle

libFuzzer generates lock traces and checks for panics and no-surprise violations.
The oracle independently tracks resource content and principals' remembered views,
then checks the granted history for changes that destroy another principal's retained
view. It does not use the production evaluator to decide whether a surprise occurred.
The generator's `Agent` is a numeric lock-test principal.

Run until a failure or interrupt, or bound the run for a smoke check:

```sh
cargo +nightly fuzz run lock_policy
cargo +nightly fuzz run lock_policy -- -max_total_time=60
```

Arguments after `--` go to libFuzzer. Crashes are written to `fuzz/artifacts/`; the
corpus accumulates in `fuzz/corpus/`. Linux and macOS are supported. Install the
prerequisites with `rustup toolchain install nightly` and `cargo install cargo-fuzz`.
Windows needs an `/include:main` linker workaround that this repository does not carry.

The same generator feeds deterministic no-surprise tests on stable Rust. The suite
includes 32 fixed seeded traces of 256 input bytes each and this exact-length history
sweep:

| Granted history length | Seeds | Granted events across histories |
|---:|---:|---:|
| 0 | 256 | 0 |
| 4 | 256 | 1,024 |
| 16 | 256 | 4,096 |
| 64 | 128 | 8,192 |
| 256 | 32 | 8,192 |
| 1,024 | 8 | 8,192 |
| Total | 936 histories | 29,696 |

Those totals come from the configured
[`SWEEP`](fuzz/src/oracle.rs#L273-L305), not a recorded libFuzzer execution count.
Both deterministic sets require actual resource contention as well as no surprise.

```sh
cargo test --release --manifest-path fuzz/Cargo.toml --lib
```

[CI](.github/workflows/ci.yml) runs the deterministic suite and a 60-second libFuzzer
smoke on both Ubuntu and macOS.

## Packages and runtime features

Import generic APIs from the package that owns them:

| Package | Responsibility |
|---|---|
| `history-syntax` | Generic Rust DSL and tagged event coordinates: `Event`, `Rule`, `Head`, `TestExpr`, `RegexExpr` |
| `junco-core` | Shared IR, encoding, errors and contracts |
| `history-store` | Histories, interning, graph storage and cache containers |
| `history-semantics` | Compilation, evaluation, `TracePolicy` and `Validator` |
| `history-analysis` | Static policy coverage, redundancy, refinement, and tail inclusion: `PolicyAnalyzer` |
| `junco-policy` | Policy facades: `RulePolicy`, `LockPolicy`, `AgentPolicy`, `FlowPolicy` |

An `Event` is a compact `Copy` value with a policy-chosen arity; see "Policy-defined events".
Component equality determines policy matching. Histories preserve original events and
payloads, including distinct values with identical coordinates. Finite Frunk `Coprod!`
unions and generic approval-payload workloads are supported.

`TracePolicy` compiles ordered `TraceRule`s once and checks caller-owned history
without appending. `Validator::builder(store)` uses the same engine with owned history:
`permits` never appends, while `check(Request<E, M>)` appends only on a successful grant
and preserves the event and opaque metadata. Denials and operational errors leave
history unchanged.

History construction and mutation are fallible: `History::new`, `from_events`, `push`,
`truncate`, `rollback` and `try_clone` return results. A clone shares its store but gets
a fresh history identity; there is no infallible `Clone`, `Default` or `FromIterator`
constructor. A foreign-store history returns `HistoryError::WrongHistoryOwner`.
Checkpoints belong to one store and history: a foreign checkpoint returns
`WrongCheckpointOwner`, and one beyond the current length returns
`CheckpointBeyondHistory`, without mutation. Compilation uses `CompileError`,
evaluation and history operations use `HistoryError`. An error never becomes a successful append.

For lower-level consumers, `history_store::graph::CanonicalStore::new()` owns concrete
arena tables and checked numeric node IDs. `KernelStore` defines the cross-crate graph
contract. `history_semantics::RuleRuntime::bindings(&template, &request)` matches a
lowered numeric head for resumable evaluation; compiler helpers are private.

Library defaults are empty. Store and Semantics `runtime` enable their concrete
implementations, including no_std + alloc support. Store `std` selects native locks;
Semantics `cache` enables optional precompilation. Neither feature implies `runtime`.
Core `serde` enables portable source serialization. The root `junco-policy` package selects
core/Syntax `std`, Store `runtime,std` and Semantics `runtime,std,cache`.
Semantics `test-util` is a dev-only integration probe feature.
Analysis supports `runtime` and `std` configurations and is a verified target.
Its four public query contracts and declared-domain/capacity qualifications are
documented in [VERIFY.md](VERIFY.md).

## Reproduce the verification

Use [VERIFY.md](VERIFY.md) for the pinned toolchain, complete configuration matrix
and evidence qualifications. The [driver](scripts/verify-all.sh) and
[CI workflow](.github/workflows/ci.yml) register the same original eleven
configurations plus exactly two public reviewer targets:

```sh
scripts/verify-all.sh -- --num-threads 64
cargo verus verify --locked -p history-semantics --features runtime,std,cache --test reviewer -- --num-threads 64
cargo verus verify --locked -p history-analysis --no-default-features --features runtime,std --test reviewer -- --num-threads 64
```

`scripts/spec-check.sh` exercises the assumed std/smallvec contracts against native
implementations, not a proof of those assumptions. See [TRUST.md](TRUST.md).
Historical audit/handoff/finiteness documents are archived in [docs/history](docs/history/);
they are not current contracts or current verification evidence.

## Regorus integration

`scripts/update_regorus.sh` takes no arguments. It mirrors the four library crates
under `crates/` into the sibling `../regorus/src/`, deletes stale files inside those
four destinations, then runs `cargo fetch`, eight per-package and three full-consumer
`cargo verus verify --locked` gates, and the `history_table` benchmark with
`history-cached` and `history-uncached` Criterion baselines.

The script validates all paths before writing: no symlinks, and the Regorus crates
must already exist. It requires `rsync`, Rust `1.98.1`, `verus`, `cargo-verus` and Z3
(`VERUS_Z3_PATH` or `z3`) on `PATH`. It does not roll back a failed check; copied files
remain for inspection. `scripts/test_update_regorus.sh` checks that an unsafe
destination aborts before any crate is touched.
