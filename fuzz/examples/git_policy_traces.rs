//! Exports deterministic policy-validated git traces as JSON on stdout.
//!
//! This is the single boundary between Rust's trace generator/policy checker and the simple-git
//! ground-truth oracle in `../test/git-policy-fuzz.test.ts`: Rust decides what the policy grants,
//! the oracle replays those grants against a real repository. The exporter itself never runs git
//! and never touches a scratch repository.
//!
//! Two input sets are exported: the fixed seeded byte stream (`seed/0 … seed/31`), which locks
//! generation against silent drift, and a freshly seeded random set (`random/0 …`) that explores
//! traces no previous run replayed. The random set's seed travels in the export so a failing run
//! can be replayed exactly — see `random_seed`.
//!
//! Stdout carries JSON only; diagnostics and panics go to stderr.

use git_policy_harness::{
    BYTES_PER_TRACE, DETERMINISTIC_SEED, MAX_FILE_NUMBER, RANDOM_TRACE_COUNT, SEEDED_TRACE_COUNT,
    ValidatedTrace, entropy, random_seed, validate_trace,
};
use serde_json::{Value, json};

fn main() {
    let seeded = entropy(DETERMINISTIC_SEED, SEEDED_TRACE_COUNT * BYTES_PER_TRACE);

    let mut traces = Vec::with_capacity(SEEDED_TRACE_COUNT + RANDOM_TRACE_COUNT);
    let mut granted = 0usize;
    let mut denied = 0usize;
    let mut commits = 0usize;

    for (index, bytes) in seeded.chunks(BYTES_PER_TRACE).enumerate() {
        let trace = validate_trace(bytes);
        granted += trace.summary.granted;
        denied += trace.summary.denied;
        commits += trace.summary.commits;
        traces.push(render(&format!("seed/{index}"), &trace));
    }

    let seed = random_seed();
    let random = entropy(seed, RANDOM_TRACE_COUNT * BYTES_PER_TRACE);
    for (index, bytes) in random.chunks(BYTES_PER_TRACE).enumerate() {
        let trace = validate_trace(bytes);
        traces.push(render(&format!("random/{index}"), &trace));
    }

    let export = json!({
        "fileCount": MAX_FILE_NUMBER,
        "seededSummary": { "granted": granted, "denied": denied, "commits": commits },
        "randomSeed": format!("{seed:#018x}"),
        "randomTraceCount": RANDOM_TRACE_COUNT,
        "traces": traces,
    });

    let rendered = serde_json::to_string(&export)
        .unwrap_or_else(|error| panic!("serialize validated traces: {error}"));
    println!("{rendered}");
}

/// One trace as its wire object: the grants an executor must replay, in order.
fn render(source: &str, trace: &ValidatedTrace) -> Value {
    let operations: Vec<Value> = trace
        .operations
        .iter()
        .map(|operation| {
            json!({
                "principal": format!("agent{}", operation.agent),
                "operation": operation.operation.as_str(),
                "path": format!("src/file{}.txt", operation.file),
                "step": operation.step,
            })
        })
        .collect();

    json!({
        "source": source,
        "summary": {
            "granted": trace.summary.granted,
            "denied": trace.summary.denied,
            "commits": trace.summary.commits,
        },
        "operations": operations,
    })
}
