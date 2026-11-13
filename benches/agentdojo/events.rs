use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use history_semantics::PolicyDecision;
use history_store::{History, Store};
use junco_policy::FlowAction;
use serde::Deserialize;
use serde_json::{Value, json};

use super::camel::{CamelEvent, camel_policy};
use super::{Options, SUITES, Task, collect_logs, safe_component, save_json};

#[derive(Default)]
struct Stats {
    tasks: usize,
    contacts: usize,
    recorded_denials: usize,
    replayed_denials: usize,
    mismatches: usize,
    errors: usize,
    seconds: Vec<f64>,
}

impl Stats {
    fn add(&mut self, other: &Self) {
        self.tasks += other.tasks;
        self.contacts += other.contacts;
        self.recorded_denials += other.recorded_denials;
        self.replayed_denials += other.replayed_denials;
        self.mismatches += other.mismatches;
        self.errors += other.errors;
        self.seconds.extend_from_slice(&other.seconds);
    }

    fn print(&mut self, name: &str) {
        self.seconds.sort_by(f64::total_cmp);
        let n = self.seconds.len();
        let (median, p99, max) = if n == 0 {
            (0.0, 0.0, 0.0)
        } else {
            let median = if n.is_multiple_of(2) {
                (self.seconds[n / 2 - 1] + self.seconds[n / 2]) / 2.0
            } else {
                self.seconds[n / 2]
            };
            (median, self.seconds[n - n / 100 - 1], self.seconds[n - 1])
        };
        println!(
            "{name:<10} {:>6} {:>8} {:>13} {:>13} {:>10} {:>6} {:>12.6} {:>12.6} {:>12.6} {:>12.6}",
            self.tasks,
            self.contacts,
            self.recorded_denials,
            self.replayed_denials,
            self.mismatches,
            self.errors,
            self.seconds.iter().sum::<f64>() * 1000.0,
            median * 1000.0,
            p99 * 1000.0,
            max * 1000.0,
        );
    }
}

fn parse_event(parts: &[String; 4]) -> Result<CamelEvent, String> {
    Ok(CamelEvent {
        principal: parts[0].parse()?,
        handle: parts[1].parse()?,
        action: parts[2].parse()?,
        label: parts[3].parse()?,
    })
}

#[derive(Deserialize)]
struct Trace {
    suite: String,
    user_task_id: String,
    injection_task_id: Option<String>,
    events: Vec<[String; 4]>,
    attempted_events: Option<Vec<[String; 4]>>,
    policy_decisions: Vec<Value>,
}

fn replay_inner(
    log: &mut Value,
    stats: &mut Stats,
    seconds: &mut f64,
    audit: bool,
) -> Result<(), String> {
    let trace = Trace::deserialize(&*log).map_err(|e| format!("invalid task log: {e}"))?;
    if !SUITES.contains(&trace.suite.as_str())
        || !safe_component(&trace.user_task_id)
        || trace
            .injection_task_id
            .as_deref()
            .is_some_and(|id| !safe_component(id))
    {
        return Err("invalid task metadata".to_owned());
    }
    // Enforcing runs omit denied contacts from committed events; replay attempts instead.
    let events = trace
        .attempted_events
        .as_ref()
        .unwrap_or(&trace.events)
        .iter()
        .enumerate()
        .map(|(i, event)| parse_event(event).map_err(|e| format!("events[{i}]: {e}")))
        .collect::<Result<Vec<_>, _>>()?;
    stats.contacts = events
        .iter()
        .filter(|e| e.action == FlowAction::Contact)
        .count();
    if stats.contacts != trace.policy_decisions.len() {
        return Err(format!(
            "{} contacts but {} policy decisions",
            stats.contacts,
            trace.policy_decisions.len()
        ));
    }
    // Validate the entire correspondence before replaying: an ordered decision for a
    // different contact must never count as a successful reproduction.
    for (i, (event, decision)) in events
        .iter()
        .filter(|e| e.action == FlowAction::Contact)
        .zip(&trace.policy_decisions)
        .enumerate()
    {
        if decision.get("principal").and_then(Value::as_str)
            != Some(event.principal.to_string().as_str())
            || decision.get("handle").and_then(Value::as_u64) != Some(u64::from(event.handle.0))
            || decision.get("class").and_then(Value::as_str)
                != Some(event.label.to_string().as_str())
        {
            return Err(format!(
                "policy_decisions[{i}] does not identify its contact principal/handle/class"
            ));
        }
        match decision.get("decision").and_then(Value::as_str) {
            Some("deny") => stats.recorded_denials += 1,
            Some("grant") => {}
            _ => return Err(format!("policy_decisions[{i}] has invalid decision")),
        }
    }
    let store = Arc::new(Store::new().map_err(|e| e.to_string())?);
    let mut history = History::new(store).map_err(|e| e.to_string())?;
    let policy = camel_policy(audit);
    let mut contact = 0;
    for event in &events {
        if event.action != FlowAction::Contact {
            history.push(*event).map_err(|e| e.to_string())?;
            continue;
        }
        let mut observed = None;
        let started = Instant::now();
        let result = policy.check(&mut history, std::slice::from_ref(event), |_, decision| {
            observed = Some(match decision {
                PolicyDecision::Grant => "grant",
                PolicyDecision::Deny { .. } => "deny",
            });
        });
        let elapsed = started.elapsed().as_secs_f64();
        *seconds += elapsed;
        let replayed = observed.ok_or("policy check did not report a decision")?;
        if audit || replayed != "deny" {
            result.map_err(|denials| format!("policy check failed: {denials:?}"))?;
        }
        let decision = &mut log["policy_decisions"][contact];
        decision["replayed"] = json!(replayed);
        decision["replayed_seconds"] = json!(elapsed);
        stats.replayed_denials += usize::from(replayed == "deny");
        stats.mismatches += usize::from(decision["decision"].as_str() != Some(replayed));
        contact += 1;
    }
    log["attempted_events"] = super::event_log(&events);
    log["events"] = super::event_log(history.as_slice());
    Ok(())
}

// A historical tool/model error is metadata, not a replay failure. Move it out
// of `error`, whose meaning in replay output is exclusively the replay outcome.
fn process(log: &mut Value, audit: bool) -> Stats {
    let mut stats = Stats {
        tasks: 1,
        ..Stats::default()
    };
    if !log.is_object() {
        *log = json!({"source_log": log.take(), "error": "task log must be an object",
            "mismatches": 0, "replayed_policy_seconds": 0.0});
        stats.errors = 1;
        stats.seconds.push(0.0);
        return stats;
    }
    if let Some(error) = log
        .as_object_mut()
        .and_then(|object| object.remove("error"))
        && !error.is_null()
    {
        // Keep preexisting provenance when replaying an already replayed log.
        if log.get("source_error").is_none() {
            log["source_error"] = error;
        }
    }
    // Offline policy replay does not execute tools or score a changed environment.
    // Preserve legacy metadata without guessing its mode or relabeling its scores.
    if log.get("source_policy_mode").is_none() {
        log["source_policy_mode"] = log.get("policy_mode").cloned().unwrap_or(Value::Null);
    }
    if log.get("source_run_kind").is_none() {
        log["source_run_kind"] = log.get("run_kind").cloned().unwrap_or(Value::Null);
    }
    if log.get("source_scores").is_none() {
        log["source_scores"] = json!({
            "utility": log.get("utility"), "injection_success": log.get("injection_success"),
            "deny_prefix_counterfactual": log.get("deny_prefix_counterfactual"),
            "legacy_secpol": log.get("secpol")
        });
    }
    log["utility"] = Value::Null;
    log["injection_success"] = Value::Null;
    log["deny_prefix_counterfactual"] = Value::Null;
    log.as_object_mut().unwrap().remove("secpol");
    log["policy_mode"] = json!(if audit { "audit" } else { "enforce" });
    log["run_kind"] = json!("events");
    log["error"] = Value::Null;
    if let Some(decisions) = log
        .get_mut("policy_decisions")
        .and_then(Value::as_array_mut)
    {
        for decision in decisions {
            if let Some(object) = decision.as_object_mut() {
                object.remove("replayed");
                object.remove("replayed_seconds");
            }
        }
    }
    let mut seconds = 0.0;
    if let Err(error) = replay_inner(log, &mut stats, &mut seconds, audit) {
        log["error"] = json!(error);
        stats.errors = 1;
    }
    stats.seconds.push(seconds);
    log["mismatches"] = json!(stats.mismatches);
    log["replayed_policy_seconds"] = json!(seconds);
    stats
}

fn path_task(relative: &Path) -> Option<Task> {
    let parts = relative
        .iter()
        .map(|s| s.to_str())
        .collect::<Option<Vec<_>>>()?;
    let [suite, user, attack, filename] = parts.as_slice() else {
        return None;
    };
    let injection = filename.strip_suffix(".json")?;
    if !SUITES.contains(suite) || !safe_component(user) || !safe_component(injection) {
        return None;
    }
    let injection_task_id = match (*attack, injection) {
        ("none", "none") => None,
        ("important_instructions", id) if id != "none" => Some(id.to_owned()),
        _ => return None,
    };
    Some(Task {
        suite: (*suite).to_owned(),
        user_task_id: (*user).to_owned(),
        injection_task_id,
    })
}

pub(super) fn replay(options: &Options) -> Result<(), String> {
    let source = options
        .events
        .as_ref()
        .ok_or("--events requires a source directory")?;
    let source = fs::canonicalize(source).map_err(|e| format!("{}: {e}", source.display()))?;
    let output = options.root();
    fs::create_dir_all(&output).map_err(|e| format!("{}: {e}", output.display()))?;
    let output = fs::canonicalize(&output).map_err(|e| format!("{}: {e}", output.display()))?;
    if source == output {
        return Err("--events source and output directories must differ".to_owned());
    }
    let mut paths = Vec::new();
    collect_logs(&source, 0, &mut paths)?;
    paths.sort();
    let mut suites = BTreeMap::<String, Stats>::new();
    let mut total = Stats::default();
    for path in paths {
        let relative = path.strip_prefix(&source).map_err(|e| e.to_string())?;
        let Some(task) = path_task(relative) else {
            continue;
        };
        if !options.selects(&task) {
            continue;
        }
        let destination = output.join(relative);
        if destination.exists() && !options.force {
            return Err(format!(
                "{} already exists; choose a new --out or use --force",
                destination.display()
            ));
        }
        let loaded = fs::read(&path)
            .map_err(|e| e.to_string())
            .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).map_err(|e| e.to_string()));
        let (mut log, mut stats) = match loaded {
            Ok(mut log) => {
                let stats = process(&mut log, options.audit);
                (log, stats)
            }
            Err(error) => (
                json!({"suite": task.suite, "user_task_id": task.user_task_id,
                "injection_task_id": task.injection_task_id, "error": format!("cannot read task log: {error}"),
                "mismatches": 0, "replayed_policy_seconds": 0.0}),
                Stats {
                    tasks: 1,
                    errors: 1,
                    seconds: vec![0.0],
                    ..Stats::default()
                },
            ),
        };
        log["policy_mode"] = json!(options.mode());
        log["run_kind"] = json!("events");
        if let Err(error) = save_json(&output.join(relative), &log) {
            eprintln!("{error}");
            stats.errors = 1;
            log["error"] = json!(error);
        }
        if let Some(error) = log["error"].as_str() {
            eprintln!("{}: {error}", path.display());
        }
        suites.entry(task.suite).or_default().add(&stats);
        total.add(&stats);
    }
    if total.tasks == 0 {
        return Err("--events selected no canonical task logs".to_owned());
    }
    println!(
        "Policy mode: {}; run kind: events; no tool execution or utility/attack measurement",
        options.mode()
    );
    println!(
        "suite       tasks contacts recorded_deny replayed_deny mismatches errors     total_ms    median_ms       p99_ms       max_ms"
    );
    for suite in SUITES {
        if let Some(stats) = suites.get_mut(*suite) {
            stats.print(suite);
        }
    }
    total.print("total");
    if total.errors != 0 || total.mismatches != 0 {
        return Err(format!(
            "event replay failed: {} mismatches, {} task errors",
            total.mismatches, total.errors
        ));
    }
    Ok(())
}

pub(super) fn self_test() -> Result<(), String> {
    let fixture = || {
        json!({
            "suite": "banking", "user_task_id": "user_task_0", "injection_task_id": null,
            "utility": true, "error": "historical model error",
            "events": [
                ["Q", "$1", "receive", "untrusted"],
                ["P", "$1", "contact", "sink"],
                ["Q", "$1", "contact", "sink"],
                ["P", "$1", "receive", "untrusted"],
                ["P", "$1", "contact", "sink"],
                ["P", "$1", "declassify", "untrusted"],
                ["P", "$1", "contact", "sink"],
                ["P", "$2", "read", "private"],
                ["P", "$2", "contact", "peer"],
                ["P", "$3", "read", "trusted"],
                ["P", "$3", "contact", "sink"]
            ],
            "policy_decisions": [
                {"principal":"P", "handle":1, "class":"sink", "decision":"grant"},
                {"principal":"Q", "handle":1, "class":"sink", "decision":"deny"},
                {"principal":"P", "handle":1, "class":"sink", "decision":"deny"},
                {"principal":"P", "handle":1, "class":"sink", "decision":"grant"},
                {"principal":"P", "handle":2, "class":"peer", "decision":"deny"},
                {"principal":"P", "handle":3, "class":"sink", "decision":"grant"}
            ]
        })
    };
    let mut log = fixture();
    let trace = Trace::deserialize(&log).map_err(|e| e.to_string())?;
    let events = trace
        .events
        .iter()
        .map(parse_event)
        .collect::<Result<Vec<_>, _>>()?;
    log["events"] = super::event_log(&events);
    let stats = process(&mut log, false);
    if stats.errors != 0
        || stats.mismatches != 0
        || stats.contacts != 6
        || stats.replayed_denials != 3
        || !log["error"].is_null()
        || log["source_error"] != "historical model error"
        || !log["utility"].is_null()
        || log["source_scores"]["utility"] != true
        || log["source_policy_mode"] != Value::Null
        || log["policy_mode"] != "enforce"
        || log["events"].as_array().unwrap().len() != events.len() - 3
        || log["policy_decisions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["replayed"] != d["decision"] || !d["replayed_seconds"].is_number())
    {
        return Err(format!("event replay self-test: valid trace failed: {log}"));
    }
    for (coordinate, invalid) in [
        (0, "R"),
        (1, "$"),
        (1, "$-1"),
        (1, "$4294967296"),
        (2, "Read"),
        (3, "unknown"),
    ] {
        let mut log = fixture();
        log["events"][0][coordinate] = json!(invalid);
        if process(&mut log, false).errors != 1
            || !log["error"].is_string()
            || log["source_error"] != "historical model error"
        {
            return Err(format!(
                "event replay self-test: accepted invalid coordinate {coordinate}: {invalid}"
            ));
        }
    }
    for (field, invalid) in [
        ("principal", json!("Q")),
        ("handle", json!(2)),
        ("class", json!("peer")),
        ("decision", json!("allow")),
    ] {
        let mut log = fixture();
        log["policy_decisions"][0][field] = invalid;
        if process(&mut log, false).errors != 1 {
            return Err(format!("event replay self-test: accepted invalid {field}"));
        }
    }
    let mut log = fixture();
    log["policy_decisions"].as_array_mut().unwrap().pop();
    if process(&mut log, false).errors != 1 {
        return Err("event replay self-test: accepted missing decision".to_owned());
    }
    let mut log = fixture();
    log["events"][0] = json!(["P", "$1", "read"]);
    if process(&mut log, false).errors != 1 {
        return Err("event replay self-test: accepted three-coordinate event".to_owned());
    }
    let mut log = fixture();
    log["policy_decisions"][0]["decision"] = json!("deny");
    let stats = process(&mut log, false);
    if stats.mismatches != 1 || stats.errors != 0 || log["mismatches"] != 1 {
        return Err("event replay self-test: failed to count mismatch".to_owned());
    }
    let mut log = fixture();
    let stats = process(&mut log, true);
    if stats.errors != 0
        || stats.mismatches != 0
        || log["events"].as_array().unwrap().len() != 11
        || log["policy_mode"] != "audit"
    {
        return Err("event replay self-test: audit did not commit denied contacts".to_owned());
    }
    Ok(())
}
