//! libFuzzer driver for the lock trace-policy generator and checker.
//!
//! Fuzzes trace generation and policy evaluation for panics and checks every granted history
//! against the no-surprise oracle; it executes no filesystem operations. The corpus stays local to
//! libFuzzer.
//!
//! Run with `cargo +nightly fuzz run lock_policy`; anything after `--` goes to libFuzzer. Linux
//! and macOS only: their linkers pull libFuzzer's `main` out of the `libfuzzer-sys` static archive
//! unaided, and the MSVC `/include:main` link workaround that Windows needed is deliberately not
//! carried.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let trace = lock_policy_harness::validate_trace(data);
    if let Some(surprise) = lock_policy_harness::no_surprise_violation(trace.history.as_slice()) {
        panic!("no-surprise violated: {surprise}");
    }
});
