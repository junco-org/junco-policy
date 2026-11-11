# junco-policy

junco-policy is a runtime-verification engine for agentic trace policies. Its compiled-rule
core is formally verified in [Verus](https://github.com/verus-lang/verus): successful
evaluations agree with the source policy's trace language, under the native-type
obligations described below.

Check a proposed action against what has already happened. A rule can require a prior
edit, forbid a stale write, or bind a decision to the principal and resource in the
request. Retained policies compile once and reuse their progress as histories grow.

## Check a proposed action

The `junco-policy` crate supplies ownership-lock and classified-agent policies on the generic engine.
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
use junco_policy::{Action, LockEvent, LockPolicy};

fn example() -> Result<(), Box<dyn std::error::Error>> {
    let paths = HistoryStore::global();
    let mut limits = Unmetered;
    let mut world = ObservationWorld;
    let alice = paths.intern_principal("::Users::research::Alice", &mut limits, &mut world)?;
    let library = paths.intern_resource("/usr/lib/lclang.so", &mut limits, &mut world)?;

    let store = Arc::new(Store::<LockEvent<u64, u64>>::new()?);
    let mut history = History::new(store.clone())?;
    let mut policy = LockPolicy::new(store)?;
    let event = LockEvent::new(alice.get(), Action::Edit, library.get());
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

## What Verus proves

### The top-level `pair_language` property

A rule has a head that matches the candidate and a tail that describes a language of
committed histories. The pair-language specification is named
[`pair_lang`](crates/junco-core/src/verify/history_specs.rs#L685-L688) in the source:

$$
\operatorname{pair\_lang}(H,R,q,w)
\iff
\exists\theta.\;
\operatorname{head\_match}(H,q,\theta)
\land
w \in \mathcal{L}_{\theta}(R).
$$

Here $H$ is the candidate head, $R$ the tail expression, $q$ the proposed event and
$w$ the committed history, ordered oldest to newest. The substitution $\theta$ holds
the principal, action and resource values bound by the candidate. A head constant must
equal the corresponding candidate value; a bound variable captures that value for use
in the same coordinate of a tail test. The numeric model uses zero for coordinates
that do not bind. Head matching determines a unique substitution, as proved by
[`lemma_head_match_unique_subst`](crates/junco-core/src/verify/history_specs.rs#L690-L697).

The candidate supplies bindings. It is not added to the history being checked.

$\mathcal{L}_{\theta}(R)$ is the set of complete histories accepted by $R$ after
substituting those bindings. The
[`lang` definition](crates/junco-core/src/verify/history_specs.rs#L56-L70) gives each
operator its meaning:

- `Empty` accepts no history. `Epsilon` accepts only the empty history.
- `All` accepts any complete history, including empty and multi-event histories.
- `Test(p)` accepts exactly one event, and only when that event satisfies `p`.
- `Concat` splits the history into ordered pieces, one for each child expression.
  `Star` accepts zero or more such pieces, each accepted by its child.
- Union, intersection and complement operate on whole languages.

These distinctions matter: `All` is not a one-event wildcard, and `Test(true)` does
not accept an empty history. Verus checks that empty-history distinction in
[`epsilon_versus_test_true_on_empty_history`](crates/history-semantics/src/verify/history_examples.rs#L54-L60).

### A prior edit, expressed as a language

Consider a Require rule whose head matches a release by principal $p$ on resource $r$.
Its tail is

$$
\texttt{All}\;\cdot\;
\texttt{Test}(\text{principal}=p \land \text{action}=\text{Edit} \land \text{resource}=r)
\;\cdot\;\texttt{All}.
$$

The two `All` expressions allow arbitrary history before and after one matching edit.
The rule therefore requires an earlier edit by the releasing principal on the same
resource. An empty history cannot satisfy it. An edit by another principal or on a
different resource cannot serve as the witness.

[`prior_edit_grants_matching_release`](crates/history-semantics/src/verify/history_examples.rs#L79-L101)
proves that a singleton matching-edit history satisfies `pair_lang` for the release
candidate. That proof example assigns numeric action 2 to edit and 3 to release.
This is an illustrative Require rule; the ownership-lock policy above has its own
seven-rule definition.

### From the specification to runtime answers

The proof covers the running compiled-rule implementation. The
[`public_compiled_decision`](crates/history-semantics/src/verify/typed_decision.rs#L66)
verification endpoint calls the actual `CompiledRule::new` constructor and
`accepts_history` method. Given a well-formed store and history, and the native-type
obligations below, its successful result has this meaning:

```text
Ok(None)            The candidate does not match the head.
Ok(Some(accepted))  The head matches, and accepted equals source-tail
                   language membership over the raw committed history.
```

For a matching head, `accepted` is true exactly when `pair_lang` holds. This equivalence
rules out both accepting a history outside the declared language and rejecting one
inside it on a successful evaluation. The result keeps a head mismatch separate from
a matching head whose tail rejects the history.

Checked `CompiledPolicy` and `Validator` bodies skip nonmatching heads and select the
first violating Require or Forbid rule. Their constructors preserve source order;
policy construction also preserves each source's diagnostic pairing. The
[composition clients](crates/history-semantics/src/verify/typed_decision.rs#L133)
call the real constructors and decisions. A validator grant appends the exact request
event and returns its metadata; denial and error preserve committed history.
Only a selected policy denial calls context and diagnostic, once each, through a
native invocation leaf. Grants and errors call neither.

The body proofs cover DSL structure and lowering, constant encoding as codebooks grow,
numeric compilation and evaluation, raw-to-numeric history correspondence, and cached
lifecycle and publication receipts. The
[`retained_history_lifecycle` and `compiled_cached_decision` endpoints](crates/history-semantics/src/verify/typed_decision.rs#L86)
exercise retained evaluation across append, rollback, replacement, truncation and a
fresh-owner fork, and the same production method used by cached clients.

Trace observers and result elimination reuse the compiled-policy proofs. Shared
combination lemmas handle membership inclusion and pointwise Boolean equivalence,
including empty sequences and duplicate members; atom collection uses one inclusion
proof for graph and sequence growth. These are proof-only changes: public contracts,
native signatures and trust boundaries are unchanged.

Coordinate, history-key and store-ID issuance use checked successor, key-absence and
map-insertion proofs over authorities retained in the process mutexes. Persistent
receipts distinguish byte and typed issuers and independent typed registries.
[Independent store construction](crates/history-store/src/typed.rs#L928) derives both
registry and scalar owner inequality; the
[foreign rollback client](crates/history-store/src/history.rs#L925) takes an actual
source checkpoint and proves `WrongCheckpointOwner` without changing the target.
Stale-frontier failures consume an ID; exhaustion does not. Later consumer failures
do not remove issued IDs.

The theorem is conditional on stable `Event` projections and component equality and
hashing that agree with their models. Modeled equality must be reflexive, symmetric
and transitive; equal native keys must hash coherently. These obligations are explicit
in [`native_obligations`](crates/history-store/src/typed.rs#L1039-L1042) and
[`key_obligations`](crates/history-store/src/typed/map.rs#L21-L30), not universal proofs
about arbitrary user types. Native field projections, callback invocation, const/static
installation and reference identity, mutex/Arc/record adapters, container operations
and reservations remain proof boundaries. Callbacks may panic or diverge; no purity
or determinism is assumed. Caching remains trusted. Checked byte-record callbacks
publish lifecycle snapshots at their lock acquisitions; observed byte-binding receipts
prove path reuse and separation across calls. DSL helpers and `TracePolicy` have checked
contracts. Root `LockPolicy` remains a native facade caller, and `LockEvent` remains a
native projection adapter.

Public ghost APIs expose source decisions, readiness introductions and result facts
without revealing writable graphs or native maps. The
[`public_specs` integration target](crates/history-semantics/tests/public_specs.rs)
uses only public imports to consume these contracts, including exact iterator-backed
histories, owner checks, diagnostic ordering and lifecycle receipts.

Under the native event laws, production compilation and valid decisions exclude
`HistoryError::Invariant`. Scoped sources also exclude unbound-variable,
variable-component-conflict and wrapped `InvalidPolicy` errors. Allocation, limits,
ID/revision exhaustion and foreign owners remain distinct failures. Generic stores
and encoders retain arbitrary errors unless they opt into the corresponding ghost
capabilities.

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
Q receives referenced contents for structured extraction; its results remain hidden.
Protected sink arguments and `$if` guards are checked by `AgentPolicy`.

This is a native-tool adaptation of [CaMeL](https://arxiv.org/abs/2503.18813), not its
Python code-generation interpreter. Classification is per tool, not per sender or
individual value. Legitimate recipients, amounts, or identifiers extracted from an
untrusted result can therefore be denied. Final answers are not sink-policy checked.
Use the measured utility and benign denial rate; do not assume paper-equivalent
results or a complete exfiltration defense. Trusted tool results remain visible to P.

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
native model responses, reference resolution, quarantine, Q retries, guarded calls,
policy decisions, and replay. The full registry contains 97 clean tasks and 949 attacked
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

`history_analysis::PolicyAnalyzer::tail_included(head, left, right)` decides whether every
history in `left` is in `right` for every candidate matching `head`. It returns `Holds`, a
shortest `Counterexample` (a candidate and the history before it), or `Exhausted` once a search
exceeds its 16 MiB graph budget. Validation and other runtime failures return `CompileError`.

Rules are validated and lowered by `junco_core::flatten_rule` and `lower_flat`, as for the
runtime. Each question reduces to inclusions between tails, decided by a breadth-first search
over the derivatives of `left ∩ ¬right`. The derivatives are the runtime's:
`history_semantics::SymbolicLanguage` compiles the difference with the runtime's normalizing
constructors and exposes its verified symbolic derivatives and successor interpretation, keyed
by the truth values of the atoms a derivative tests. A search state branches over classes of
events rather than events: per component, a value that its atoms mention or any other value.
The candidate is case-split only where an atom compares one of its components with a constant.
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
structurally, and tests by their conjuncts and disjuncts. Parts are compared by identity, so
inserted states are indexed by their parts. Inserted states are never removed, so
counterexamples stay shortest.

Each search compiles one graph with its own 16 MiB budget, through `CanonicalStore::with_budget`,
where the runtime keeps `MAX_GRAPH_BYTES` (100 KiB) per rule. The classes of events and the search
are unverified. Their tests replay
every counterexample through `TracePolicy`, and a differential test compares the verdicts on
random tail pairs, including counterexample lengths, with brute force over every history up to
a length bound.

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
| `history-syntax` | Generic Rust DSL and event projections: `Rule`, `Head`, `TestExpr`, `RegexExpr` |
| `junco-core` | Shared IR, encoding, errors and contracts |
| `history-store` | Histories, interning, graph storage and cache containers |
| `history-semantics` | Compilation, evaluation, `TracePolicy` and `Validator` |
| `history-analysis` | Static tail-inclusion analysis: `PolicyAnalyzer` |
| `junco-policy` | Ownership-lock consumer: `Action`, `LockEvent`, `LockPolicy` |

An `Event` is a compact `Copy` value that projects to principal, action and resource.
Component equality determines policy matching. Histories preserve original events and
payloads, including distinct values with identical projections. Finite Frunk `Coprod!`
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
Core `serde` enables portable source serialization. The root lock consumer selects
core/Syntax `std`, Store `runtime,std` and Semantics `runtime,std,cache`.
Semantics `test-util` is a dev-only integration probe feature.
Analysis has no features; it is no_std + alloc and outside the Verus job. It uses Semantics
`runtime` through `SymbolicLanguage`, a native facade like `TracePolicy` that owns a compiled
pair and calls only verified graph operations.

## Reproduce the verification

The pinned toolchain is Rust `1.98.1`, Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0` and
`vstd = 0.0.0-2026-10-04-0306`. With `verus` and `cargo-verus` on `PATH`, and
`VERUS_Z3_PATH` pointing to that Z3 binary, run the core and cached-runtime gates:

```sh
cargo verus verify --locked -p junco-core --features runtime,std,serde
cargo verus verify --locked -p history-semantics --features runtime,std,cache
cargo verus verify --locked -p history-semantics --features runtime,std,cache --test public_specs
```

The [CI workflow](.github/workflows/ci.yml#L86-L147) contains the toolchain setup and
full library feature matrix. Verified helper dependencies are pinned to
[bumpus](https://github.com/elefthei/bumpus) (`verus-bumpalo`) commit
`888a6983370524cf1686d82e5814dd17a2dd14e5` and
[hashconsius](https://github.com/elefthei/hashconsius) commit
`d7c17483a46b42a9e179cbfa0fdae9b7e8043dbf`.

The trusted std and smallvec specifications in
[`history_assumptions.rs`](crates/junco-core/src/verify/history_assumptions.rs) are not
proved. `scripts/spec-check.sh` tests each of them against the real implementation with
[verus-spec-check](https://github.com/verus-lang/verus-spec-check) (the `spec-check` CI job).
The ordering and equality specifications require vstd's `obeys_cmp` and `obeys_eq` laws of
their element type.

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
