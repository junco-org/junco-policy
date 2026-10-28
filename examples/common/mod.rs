//! Replays recorded AgentDojo-format traces (AgentDojo, AgentDyn;
//! `runs/<pipeline>/<suite>/<user_task>/<attack>/<task>.json`) through an [`AgentPolicy`] that
//! forbids contacting a sink after reading untrusted data, and reports how many successful prompt
//! injections it would have stopped and how many legitimate runs it would have broken. The
//! per-benchmark tool and trust tables are passed in as a [`Benchmark`].
//!
//! Every executed tool call becomes classified events of the single principal `agent`: a `Read`
//! of a trusted or untrusted source, a `Contact` of a sink, or both for web fetches (the request
//! leaves before the page returns). Traces have one principal, so `TaintState` (cross-principal
//! propagation) is not needed. Two classifiers label reads: `source` is the tool-level trust table
//! [`Benchmark::untrusted_sources`] (the knob to tune); `oracle` marks a read untrusted iff its
//! result contains the log's injected text, the ceiling any source table can reach.
//!
//! In AgentDojo-format logs `security: true` on an attacked run means the injection task's check
//! passed, that is, the attack succeeded. DoS attacks are skipped, and so are AgentDyn's
//! injection-task utility runs (the injection goal run as the user task).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use Kind::{Fetch, Read, Sink};
use junco_policy::{
    AgentAction, AgentEvent, AgentPolicy, AgentRule, Classifier, Glob, PolicyDecision,
};
use serde_json::Value;

type Class = &'static str;
type Event = AgentEvent<&'static str, Class>;

const AGENT: &str = "agent";
const UNTRUSTED: Class = "untrusted";
const TRUSTED: Class = "trusted";
const SINK: Class = "sink";

#[derive(Clone, Copy)]
pub enum Kind {
    Read,
    Sink,
    /// Contact then read (web fetches).
    Fetch,
}

/// The benchmark-specific classification tables.
pub struct Benchmark {
    /// (tool name, kind, argument names that identify the destination / source object)
    pub tools: &'static [(&'static str, Kind, &'static [&'static str])],
    /// Globs over `tool:destination` keys (`/` written as `|`) whose reads are untrusted.
    pub untrusted_sources: &'static [&'static str],
}

const DOS: &[&str] = &[
    "dos",
    "captcha_dos",
    "felony_dos",
    "offensive_email_dos",
    "swearwords_dos",
];

struct Call {
    tool: String,
    /// `None` for a tool missing from [`Benchmark::tools`].
    kind: Option<Kind>,
    keys: Vec<String>,
    /// The tool result, [`squash`]ed.
    result: String,
}

struct Log {
    suite: String,
    attack: String,
    user_task: String,
    injection_task: String,
    utility: bool,
    security: bool,
    /// The injected texts, [`squash`]ed.
    needles: Vec<String>,
    calls: Vec<Call>,
}

struct Step {
    call: usize,
    key: String,
    event: Event,
}

struct Verdict {
    denied: bool,
    first_untrusted: Option<String>,
    first_denied: Option<String>,
}

#[derive(Clone, Copy)]
enum Population {
    Benign,
    Successful,
    Resisted,
}

#[derive(Default)]
struct Tally {
    successful: u32,
    caught: u32,
    /// Successful attacks in which no read was classified untrusted.
    no_untrusted_read: u32,
    resisted: u32,
    collateral: u32,
    benign: u32,
    false_denied: u32,
}

impl Tally {
    fn record(&mut self, population: Population, verdict: &Verdict) {
        let denied = u32::from(verdict.denied);
        match population {
            Population::Successful => {
                self.successful += 1;
                self.caught += denied;
                self.no_untrusted_read += u32::from(verdict.first_untrusted.is_none());
            }
            Population::Resisted => {
                self.resisted += 1;
                self.collateral += denied;
            }
            Population::Benign => {
                self.benign += 1;
                self.false_denied += denied;
            }
        }
    }
}

/// Drops whitespace, quotes and backslash escapes so YAML-folded tool output compares equal to
/// the injected text: `\n`, `\t`, `\r` escapes vanish with the whitespace they encode, any other
/// backslash (fold markers, escaped quotes and spaces) is dropped alone.
fn squash(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                if matches!(chars.peek(), Some('n' | 't' | 'r')) {
                    chars.next();
                }
            }
            '\'' | '"' => {}
            c if c.is_whitespace() => {}
            c => out.push(c),
        }
    }
    out
}

/// A message's text: a plain string, or the `text` blocks of newer logs.
fn text(content: Option<&Value>) -> String {
    match content {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Array(blocks)) => blocks
            .iter()
            .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
            .filter_map(|block| block.get("content").and_then(Value::as_str))
            .collect::<Vec<_>>()
            .join("\n"),
        _ => String::new(),
    }
}

/// `tool:destination` per string (or string-array element) under `destinations`, else `tool:`.
fn keys(tool: &str, args: Option<&Value>, destinations: &[&str]) -> Vec<String> {
    let mut keys: Vec<String> = destinations
        .iter()
        .filter_map(|name| args?.get(name))
        .flat_map(|value| match value {
            Value::String(s) => vec![s.as_str()],
            Value::Array(items) => items.iter().filter_map(Value::as_str).collect(),
            _ => Vec::new(),
        })
        .map(|destination| format!("{tool}:{}", destination.replace('/', "|")))
        .collect();
    if keys.is_empty() {
        keys.push(format!("{tool}:"));
    }
    keys
}

fn parse(path: &Path, tools: &[(&str, Kind, &[&str])]) -> Option<Log> {
    let log: Value = serde_json::from_str(&fs::read_to_string(path).ok()?).ok()?;
    let string = |key| {
        log.get(key)
            .and_then(Value::as_str)
            .unwrap_or("none")
            .to_owned()
    };
    let flag = |key| log.get(key).and_then(Value::as_bool).unwrap_or(false);
    let needles = log
        .get("injections")
        .and_then(Value::as_object)
        .map(|injections| {
            injections
                .values()
                .filter_map(Value::as_str)
                .map(squash)
                .filter(|needle| !needle.is_empty())
                .collect()
        })
        .unwrap_or_default();
    let mut calls = Vec::new();
    for message in log.get("messages")?.as_array()? {
        if message.get("role").and_then(Value::as_str) != Some("tool") {
            continue;
        }
        let call = message.get("tool_call")?;
        let tool = call.get("function")?.as_str()?;
        let spec = tools.iter().find(|(name, ..)| *name == tool);
        calls.push(Call {
            tool: tool.to_owned(),
            kind: spec.map(|&(_, kind, _)| kind),
            keys: keys(tool, call.get("args"), spec.map_or(&[], |&(.., d)| d)),
            result: squash(&text(message.get("content"))),
        });
    }
    Some(Log {
        suite: string("suite_name"),
        attack: string("attack_type"),
        user_task: string("user_task_id"),
        injection_task: string("injection_task_id"),
        utility: flag("utility"),
        security: flag("security"),
        needles,
        calls,
    })
}

/// The classified events of `log`, reads labelled by the oracle or by the `source` table.
fn steps(log: &Log, oracle: bool, source: &Classifier<Glob, Class>) -> Vec<Step> {
    let mut steps = Vec::new();
    for (index, call) in log.calls.iter().enumerate() {
        let Some(kind) = call.kind else { continue };
        let read = || {
            let key = &call.keys[0];
            let class = if oracle {
                if log.needles.iter().any(|n| call.result.contains(n.as_str())) {
                    UNTRUSTED
                } else {
                    TRUSTED
                }
            } else {
                source.classify(key.as_str()).expect("fallback set")
            };
            Step {
                call: index,
                key: key.clone(),
                event: Event::new(AGENT, AgentAction::Read, class),
            }
        };
        let contact = |key: &String| Step {
            call: index,
            key: key.clone(),
            event: Event::new(AGENT, AgentAction::Contact, SINK),
        };
        match kind {
            Read => steps.push(read()),
            Sink => steps.extend(call.keys.iter().map(contact)),
            Fetch => {
                steps.push(contact(&call.keys[0]));
                steps.push(read());
            }
        }
    }
    steps
}

/// Whether each step would have been denied.
fn replay(policy: &AgentPolicy<&'static str, Class>, steps: &[Step]) -> Vec<bool> {
    let batch: Vec<Event> = steps.iter().map(|step| step.event).collect();
    let mut denied = Vec::with_capacity(batch.len());
    policy
        .check(std::iter::empty(), &batch, |_, decision| {
            denied.push(matches!(decision, PolicyDecision::Deny { .. }));
        })
        .expect("an auditing policy never errs");
    denied
}

fn verdict(steps: &[Step], denied: &[bool]) -> Verdict {
    Verdict {
        denied: denied.contains(&true),
        first_untrusted: steps
            .iter()
            .find(|step| step.event.resource == UNTRUSTED)
            .map(|step| step.key.clone()),
        first_denied: steps
            .iter()
            .zip(denied)
            .find(|&(_, &d)| d)
            .map(|(step, _)| step.key.clone()),
    }
}

/// Prints every step of one log under both classifiers.
fn explain(log: &Log, source: &Classifier<Glob, Class>, policy: &AgentPolicy<&'static str, Class>) {
    println!(
        "{} {} {} utility={} security={}",
        log.suite, log.attack, log.injection_task, log.utility, log.security
    );
    let by_source = steps(log, false, source);
    let by_oracle = steps(log, true, source);
    let (source_denied, oracle_denied) = (replay(policy, &by_source), replay(policy, &by_oracle));
    let show = |step: &Step, denied: bool| {
        let decision = if denied { "DENY" } else { "GRANT" };
        format!("{} {} {decision}", step.event.action, step.event.resource)
    };
    for (i, (s, o)) in by_source.iter().zip(&by_oracle).enumerate() {
        println!(
            "#{} {:<45} source: {:<24} oracle: {}",
            s.call,
            s.key,
            show(s, source_denied[i]),
            show(o, oracle_denied[i]),
        );
    }
    for (index, call) in log.calls.iter().enumerate() {
        if call.kind.is_none() {
            println!("#{index} {} (unknown tool, no event)", call.tool);
        }
    }
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("reading {}: {error}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "json") {
            out.push(path);
        }
    }
}

fn pct(part: u32, whole: u32) -> f64 {
    if whole == 0 {
        0.0
    } else {
        f64::from(part) * 100.0 / f64::from(whole)
    }
}

fn row(suite: &str, t: &Tally) {
    let cell = |part, whole| format!("{part}/{whole} ({:.1}%)", pct(part, whole));
    println!(
        "{suite:<10} | {:>18} | {:>17} | {:>18} | {:>18}",
        cell(t.caught, t.successful),
        t.no_untrusted_read,
        cell(t.collateral, t.resisted),
        cell(t.false_denied, t.benign),
    );
}

/// `counts` for `variant`, most frequent first.
fn top<'a>(counts: &'a BTreeMap<(&str, String), u32>, variant: &str) -> Vec<(&'a String, u32)> {
    let mut rows: Vec<_> = counts
        .iter()
        .filter(|((v, _), _)| *v == variant)
        .map(|((_, key), &count)| (key, count))
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    rows
}

pub fn run(benchmark: &Benchmark) {
    let Some(arg) = std::env::args().nth(1) else {
        eprintln!(
            "usage: {} <runs-dir|log.json>",
            std::env::args().next().unwrap_or_default()
        );
        std::process::exit(2);
    };
    let path = Path::new(&arg);
    let source = benchmark
        .untrusted_sources
        .iter()
        .fold(Classifier::with_fallback(TRUSTED), |table, glob| {
            table.class(Glob::new(glob).expect("static glob"), UNTRUSTED)
        });
    let policy: AgentPolicy<&'static str, Class> = AgentPolicy::new()
        .rule(AgentRule::no_contact_after_read(UNTRUSTED, &[SINK]))
        .audit();

    if path.is_file() {
        let Some(log) = parse(path, benchmark.tools) else {
            eprintln!("{}: not a trace log", path.display());
            std::process::exit(1);
        };
        explain(&log, &source, &policy);
        return;
    }

    let mut files = Vec::new();
    collect(path, &mut files);
    let mut tallies: BTreeMap<(&str, String), Tally> = BTreeMap::new();
    let mut totals: BTreeMap<&str, Tally> = BTreeMap::new();
    let mut uncaught: BTreeMap<(&str, String), u32> = BTreeMap::new();
    let mut pairs: BTreeMap<(&str, String), u32> = BTreeMap::new();
    let mut unknown_tools = BTreeSet::new();
    let (mut parsed, mut skipped, mut dos_skipped, mut goal_runs, mut table_gap) = (0, 0, 0, 0, 0);
    for file in &files {
        let Some(log) = parse(file, benchmark.tools) else {
            skipped += 1;
            continue;
        };
        unknown_tools.extend(
            log.calls
                .iter()
                .filter(|call| call.kind.is_none())
                .map(|call| call.tool.clone()),
        );
        if DOS.contains(&log.attack.as_str()) {
            dos_skipped += 1;
            continue;
        }
        if log.user_task.starts_with("injection_task") {
            goal_runs += 1; // AgentDyn: the injection goal run as the user task; neither benign nor attacked
            continue;
        }
        parsed += 1;
        let population = match (log.attack.as_str(), log.security) {
            ("none", _) => Population::Benign,
            (_, true) => Population::Successful,
            (_, false) => Population::Resisted,
        };
        let verdicts = [false, true].map(|oracle| {
            let steps = steps(&log, oracle, &source);
            verdict(&steps, &replay(&policy, &steps))
        });
        if verdicts[1].denied && !verdicts[0].denied {
            table_gap += 1;
        }
        for (variant, verdict) in ["source", "oracle"].into_iter().zip(&verdicts) {
            tallies
                .entry((variant, log.suite.clone()))
                .or_default()
                .record(population, verdict);
            totals
                .entry(variant)
                .or_default()
                .record(population, verdict);
            match population {
                Population::Successful if !verdict.denied => {
                    *uncaught
                        .entry((variant, format!("{}/{}", log.suite, log.injection_task)))
                        .or_default() += 1;
                }
                Population::Resisted | Population::Benign if verdict.denied => {
                    let pair = format!(
                        "{} -> {}",
                        verdict.first_untrusted.as_deref().unwrap_or("?"),
                        verdict.first_denied.as_deref().unwrap_or("?"),
                    );
                    *pairs.entry((variant, pair)).or_default() += 1;
                }
                _ => {}
            }
        }
    }

    for variant in ["source", "oracle"] {
        println!("== {variant} ==");
        println!(
            "{:<10} | {:>18} | {:>17} | {:>18} | {:>18}",
            "suite", "successful caught", "no untrusted read", "resisted denied", "benign denied"
        );
        for ((_, suite), tally) in tallies.iter().filter(|((v, _), _)| *v == variant) {
            row(suite, tally);
        }
        row("total", &totals[variant]);
        println!("uncaught successful attacks by injection task:");
        for (task, count) in top(&uncaught, variant) {
            println!("  {task}: {count}");
        }
        println!("top 15 (first untrusted read -> denied sink) in resisted+benign runs:");
        for (pair, count) in top(&pairs, variant).into_iter().take(15) {
            println!("  {pair}: {count}");
        }
        println!();
    }
    println!("table gap (oracle caught, source missed): {table_gap}");
    println!("unknown tools: {unknown_tools:?}");
    println!(
        "logs: parsed {parsed}, skipped {skipped}, dos skipped {dos_skipped}, injection-task utility runs skipped {goal_runs}"
    );
}
