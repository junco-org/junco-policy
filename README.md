# rust-validator

Capability validation for Junco, written in Rust and exposed to TypeScript through a napi binding.
It owns the git trace policy: the rule table, its no-surprise oracle, and the harness that both the
fuzzer and the benchmark drive.

## Fuzzing

libFuzzer generates git traces and checks the policy for panics and no-surprise violations. It runs
until it finds a crash or you stop it, so bound it when you just want a smoke run:

```sh
bun run --cwd packages/rust-validator fuzz
bun run --cwd packages/rust-validator fuzz -max_total_time=60
```

Arguments after the script name go straight to libFuzzer. Crashing inputs are written to
`fuzz/artifacts/`, and the corpus accumulates in `fuzz/corpus/`.

Requires the nightly toolchain and `cargo-fuzz` (`rustup toolchain install nightly`,
`cargo install cargo-fuzz`). Keep the default AddressSanitizer — `--sanitizer=none` does not link on
Windows.

## Benchmarking

Criterion measures a single policy check as committed history grows from 0 to 1024 operations, so
the scaling reads off directly. The static Git rule table is compiled once per benchmark case,
outside the timed loop, matching the retained policy used by the napi validator:

```sh
bun run --cwd packages/rust-validator bench
```

The HTML report is written to `fuzz/target/criterion/report/index.html`. Criterion compares each run
against the previous one, so run it twice to see a delta.
