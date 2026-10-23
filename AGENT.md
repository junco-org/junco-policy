# AGENT.md

## AgentDojo / AgentDyn benchmarks

`examples/common/mod.rs` replays recorded AgentDojo-format traces through `AgentPolicy` with
`AgentRule::no_contact_after_read("untrusted", &["sink"])` in audit mode, and reports per suite how
many successful injections it would deny and how many legitimate runs it would break.
`examples/agentdojo.rs` (AgentDojo) and `examples/agentdyn.rs` (AgentDyn, suites `shopping`,
`github`, `dailylife`) hold only the per-benchmark tables and call `common::run`.

Fetch the traces once (pinned sparse checkouts into `traces/`, gitignored; needs `git` and
Python 3):

```sh
python3 examples/fetch_traces.py
```

Add more pipelines with `git -C traces/<benchmark> sparse-checkout add runs/<pipeline>`.

Run:

```sh
cargo run --release --example agentdojo -- traces/agentdojo/runs/gpt-4o-2024-05-13         # tables
cargo run --release --example agentdojo -- <path/to/log.json>                              # one trace, per-call verdicts
cargo run --release --example agentdyn -- traces/agentdyn/runs/gpt-4o-2024-08-06
```

Two read classifiers are reported: `source` (tool-level table, the one to tune) and `oracle`
(a read is untrusted iff its result contains the injected text; the ceiling). Columns:

- `successful caught`: attacks that succeeded (`security: true`) and would have been denied.
- `no untrusted read`: successful attacks with no read classified untrusted (expected 0).
- `resisted denied`: attacked runs the model resisted that would still have been denied.
- `benign denied`: attack-free user-task runs (`user_task_*/none/none.json`) that would have been
  denied; oracle must be 0.

Tune by editing the tables in `examples/agentdojo.rs` / `examples/agentdyn.rs`: `TOOLS` (read/sink
and destination arguments), `UNTRUSTED_SOURCES` (globs over `tool:destination` keys, `/` written
as `|`). DoS attacks are skipped, and so are the injection-task utility runs
(`injection_task_*/none/none.json`, the attacker goal run as the user task). AgentDojo
`travel/injection_task_6` has no tool sink and is uncatchable by design.
