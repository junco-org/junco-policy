//! libFuzzer driver for the git trace-policy generator and checker.
//!
//! Fuzzes trace generation and policy evaluation for panics; it executes no git and no filesystem
//! operation. The ground-truth replay of granted operations lives in the simple-git oracle
//! (`packages/rust-validator/test/git-policy-fuzz.test.ts`), which drives the generator from its
//! own seeds rather than from this target's corpus; the corpus stays local to libFuzzer.
//!
//! `bun run --cwd packages/rust-validator fuzz`, which is
//! `cargo +nightly fuzz run git_policy --no-include-main-msvc` — the MSVC flag is inert elsewhere,
//! see `fuzz/build.rs`. Keep the default AddressSanitizer: `--sanitizer=none` does not link on
//! windows-msvc, because rustc's coverage pass emits ELF-style `__start___sancov_*` section
//! bounds that `link.exe` cannot synthesize and only the sanitizer runtime supplies.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let trace = git_policy_harness::validate_trace(data);
    if let Some(surprise) = git_policy_harness::no_surprise_violation(&trace.history) {
        panic!("no-surprise violated: {surprise}");
    }
});
