//! Classifies every policy denial as ownership or read-claim contention, and asks the
//! no-surprise oracle whether each claim denial prevented a real surprise or was over-strict.

use lock_policy_harness::{
    BYTES_PER_TRACE, DETERMINISTIC_SEED, SEEDED_TRACE_COUNT, entropy, no_surprise_violation,
    validate_trace,
};

/// Traces drawn purely to widen the strictness sample; unrelated to the replay oracle's
/// `RANDOM_TRACE_COUNT`, which is how many randomized traces it replays per run.
const SAMPLED_TRACES: u64 = 20_000;

#[derive(Default)]
struct Tally {
    granted: usize,
    legality_denials: usize,
    claim_denials: usize,
    prevented_surprise: usize,
    over_strict: usize,
    surprises_among_grants: usize,
}

fn analyse(data: &[u8], tally: &mut Tally) {
    let trace = validate_trace(data);
    tally.granted += trace.history.len();
    if no_surprise_violation(&trace.history).is_some() {
        tally.surprises_among_grants += 1;
    }
    for denial in &trace.denials {
        if !denial.failed_precondition.contains(" was last read by ") {
            tally.legality_denials += 1;
            continue;
        }
        tally.claim_denials += 1;
        let mut counterfactual = trace.history[..denial.granted_prefix_len].to_vec();
        counterfactual.push(denial.event.clone());
        let last = counterfactual.len() - 1;
        match no_surprise_violation(&counterfactual) {
            Some(surprise) if surprise.index == last => tally.prevented_surprise += 1,
            _ => tally.over_strict += 1,
        }
    }
}

fn report(label: &str, tally: &Tally) {
    let denied = tally.legality_denials + tally.claim_denials;
    let pct = |part: usize, whole: usize| {
        if whole == 0 {
            0.0
        } else {
            part as f64 * 100.0 / whole as f64
        }
    };
    println!("== {label} ==");
    println!("granted events:            {}", tally.granted);
    println!("denied candidates:         {denied}");
    println!("  ownership denials:       {}", tally.legality_denials);
    println!("  read-claim denials:      {}", tally.claim_denials);
    println!(
        "    prevented a surprise:  {} ({:.1}% of claim denials)",
        tally.prevented_surprise,
        pct(tally.prevented_surprise, tally.claim_denials),
    );
    println!(
        "    over-strict:           {} ({:.1}% of claim denials)",
        tally.over_strict,
        pct(tally.over_strict, tally.claim_denials),
    );
    println!(
        "surprising granted traces: {}",
        tally.surprises_among_grants
    );
}

fn main() {
    let mut deterministic = Tally::default();
    let seeded = entropy(DETERMINISTIC_SEED, SEEDED_TRACE_COUNT * BYTES_PER_TRACE);
    for bytes in seeded.chunks(BYTES_PER_TRACE) {
        analyse(bytes, &mut deterministic);
    }
    report("deterministic set (32 seeded)", &deterministic);

    let mut random = Tally::default();
    for seed in 0..SAMPLED_TRACES {
        let bytes = entropy(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15), BYTES_PER_TRACE);
        analyse(&bytes, &mut random);
    }
    println!();
    report(&format!("{SAMPLED_TRACES} sampled traces"), &random);
}
