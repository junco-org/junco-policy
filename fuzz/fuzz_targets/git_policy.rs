//! libFuzzer driver for the git trace-policy generator and checker.
//!
//! Fuzzes trace generation and policy evaluation for panics; it executes no git and no filesystem
//! operation. The ground-truth replay of granted operations lives in the simple-git oracle
//! (`packages/rust-validator/test/git-policy-fuzz.test.ts`), which drives the generator from its
//! own seeds rather than from this target's corpus; the corpus stays local to libFuzzer.
//!
//! `cargo fuzz run git_policy` (nightly). On Windows add `--no-include-main-msvc` — see
//! `fuzz/build.rs` — and make `clang_rt.asan_dynamic-x86_64.dll` (shipped with the MSVC toolchain)
//! reachable by the loader, or pass `--sanitizer=none`.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let trace = git_policy_harness::validate_trace(data);
    if let Some(surprise) = git_policy_harness::no_surprise_violation(&trace.history) {
        panic!("no-surprise violated: {surprise}");
    }
});
