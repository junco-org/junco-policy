//! libFuzzer driver for the git trace-policy generator and checker.
//!
//! Fuzzes trace generation and policy evaluation for panics; it executes no git and no filesystem
//! operations. The ground-truth replay of granted operations lives in the git2 replay oracle
//! (`fuzz/tests/git_oracle.rs`), which drives the generator from its own seeds rather than from
//! this target's corpus; the corpus stays local to libFuzzer.
//!
//! Run with `cargo +nightly fuzz run git_policy`; anything after `--` goes to libFuzzer. Linux and
//! macOS only: their linkers pull libFuzzer's `main` out of the `libfuzzer-sys` static archive
//! unaided, and the MSVC `/include:main` link workaround that Windows needed is deliberately not
//! carried.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let trace = git_policy_harness::validate_trace(data);
    if let Some(surprise) = git_policy_harness::no_surprise_violation(&trace.history) {
        panic!("no-surprise violated: {surprise}");
    }
});
