# Dogwood Criterion bench

```sh
cargo +1.98.1 bench --manifest-path fuzz/Cargo.toml --bench other
cargo +1.98.1 bench --manifest-path fuzz/Cargo.toml --bench other -- 'dogwood_fuzz/'
```

`dogwood_replay`: cold replay of 16, 64, 256, and 1,024 granted events from the lock-policy fuzz harness, through all three engines. Throughput counts granted events; preflight checks every verdict.

`dogwood_fuzz`: the harness's 32 deterministic seeded traces, including denials in generation order. All three engines must match all 449 candidates (42 denied) before timing; throughput counts candidates, not committed events.

`dogwood_examples`: Dogwood alone replays 52 default-feature doc examples. Preflight matches the CLI's verdict/rule/error stream against `expected.out`; throughput counts all input events. Dogwood has no benchmark suite at the pinned commit, so these are documentation workloads, not upstream benchmarks.

Junco retains its compiled policy/store with fresh histories; Dogwood re-lowers and rebuilds each authorizer outside timing because it consumes the policy set and has no reset. Timed routines include ingestion and teardown. Events are prebuilt: a request decides; only grants add a response visible to temporal predicates. Timestamps advance by one second, inside the 24h window. No warm Dogwood single-decision probe exists: every call appends; `../lock_policy.rs` covers junco's warm decisions.

| Junco rule | Dogwood `@id` |
| --- | --- |
| edit × owned_by_other | edit_owned_by_other |
| release × owned_by_other | release_owned_by_other |
| remove × owned_by_other | remove_owned_by_other |
| edit × stale_view | edit_stale_view |
| remove × stale_view | remove_stale_view |
| edit × read_by_other | edit_read_by_other |
| remove × read_by_other | remove_read_by_other |

## Vendored data

Source: [Dogwood](https://github.com/dogwood-policy/dogwood/tree/4ec5e2c01b44ff3882a231ae5d315b330b38fa25), commit `4ec5e2c01b44ff3882a231ae5d315b330b38fa25`; interpreter crate `dogwood-language 1.1.0` with default features. `examples/LICENSE` and `examples/NOTICE` are Dogwood's, Apache-2.0, © Amazon.com, Inc. or its affiliates.

Excluded from the 56 replayable examples: `cap_open_agent_prs_windowed`, `refund_budget_settled_plus_current`, `touchless_invoice_within_tolerance`, `touchless_share_capped` require experimental arithmetic. All other 52 names are in the fetch script below. Optional inputs: 14 `providers.json`, 5 `macros.dw`, 2 `events.dwschema`, 1 `event.dwschema`. No README, explain output, or standalone Rhai copies are vendored.

Re-fetch from the repository root:

```sh
base=https://raw.githubusercontent.com/dogwood-policy/dogwood/4ec5e2c01b44ff3882a231ae5d315b330b38fa25
dst=fuzz/benches/dogwood/examples
mkdir -p "$dst" && curl -fsSL "$base/LICENSE" -o "$dst/LICENSE" && curl -fsSL "$base/NOTICE" -o "$dst/NOTICE"
names='access_not_revoked_since_grant alert_exactly_three_transfers alert_heartbeat_and_login_rate alert_login_in_last_hour alert_same_user_login_and_transfer alert_some_login
alert_total_transfer_over_200 call_cedar_macro_with_temporal_leaf call_temporal_aggregation_macro_count call_temporal_condition_macro_once call_temporal_condition_macros_composed cedar_macro_plus_temporal_leaf
deny_overrides_sell_not_amzn desk_governance forbid_large_except_amzn forbid_read_transfers_over_1000 get_amzn_stock_info heartbeat_scope_alias
login_attempt_custom_kind macro_library_once_is_small permit_read_anyone provider_allowed_or_short provider_digitcount_forbid provider_digitcount_operator_ge
provider_enum_severity_forbid provider_enum_two_namespaces provider_filter_set_index_decimal provider_int_arithmetic_trusted provider_matches_and_not_blocked provider_principal_id_allowlist
provider_regex_analyze_fields provider_regex_matches_uppercase provider_risk_decimal_method read_after_login read_after_login_success read_heartbeat_since_login_30s
read_login_not_logout read_prev_login read_prev_login_success read_since_login sell_after_approval_valid_ticker sell_like_a_prefix
sell_shares_temporal_subexpr sell_small_only sell_threshold_by_stock submit_after_approval_injection temporal_count_formerly_login temporal_login_then_read
temporal_once_read_recent temporal_sum_formerly_transfer write_after_read write_after_read_formerly'
for d in $names; do
  mkdir -p "$dst/$d"
  for f in policy.dw schema.cedarschema trace.log expected.out; do
    curl -fsSL "$base/dogwood-docs/examples/$d/$f" -o "$dst/$d/$f"
  done
  for f in events.dwschema event.dwschema macros.dw providers.json; do
    curl -fsSL "$base/dogwood-docs/examples/$d/$f" -o "$dst/$d/$f" 2>/dev/null || rm -f "$dst/$d/$f"
  done
done
```

## VeriMon

The verified MFOTL baseline is [VeriMon](https://bitbucket.org/jshs/monpoly), pinned to commit `025a142321e4cd9174164568e38c399ec336a076`. Build and install it once:

```sh
git clone https://bitbucket.org/jshs/monpoly.git ~/git/monpoly
cd ~/git/monpoly
git checkout 025a142321e4cd9174164568e38c399ec336a076
eval "$(opam env --switch=default --set-switch)"
opam install -y --deps-only --ignore-constraints-on=libmonpoly .
dune build --release
dune install --prefix "$HOME/.local"
export VERIMON="$HOME/.local/bin/monpoly"
"$VERIMON" -version
```

At this commit the final command prints `MonPoly, version 025a142`. The benchmark reads `VERIMON`, falling back to `monpoly` on `PATH`, and always passes `-verified`. `verimon/lock.sig` defines the event vocabulary; `verimon/lock.mfotl` encodes the three lock-policy denial predicates.

Time points 0–2 are the readiness prelude. Candidate requests and granted commits start at time point 3; denied requests have no commit. A guaranteed trailing violation marks completion. The timed region covers writing the prepared log and reading verdicts. Process start-up, formula parsing, and process exit are outside timing.
