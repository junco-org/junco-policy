//! Throwaway counter-free reproduction of dogwood_replay/junco.
use std::sync::Arc;
use std::time::Instant;

use history_store::History;
use junco_policy::LockPolicy;
use lock_policy_harness::{BYTES_PER_EVENT, check, entropy, granted_history};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: replay_loop L R");
    let length: usize = args[1].parse()?;
    let repeats: usize = args[2].parse()?;
    assert!(length > 0 && repeats > 0);
    let events = granted_history(&entropy(SEED, length * BYTES_PER_EVENT), length)?;
    let store = Arc::clone(events.store());
    let mut policy = LockPolicy::new(Arc::clone(&store))?;
    let start = Instant::now();
    for _ in 0..repeats {
        let mut history = History::new(Arc::clone(&store))?;
        for event in events.as_slice() {
            assert!(check(&mut policy, &history, event)?);
            history.push(*event)?;
        }
        assert_eq!(history.len(), length);
    }
    let elapsed = start.elapsed().as_nanos();
    let decisions = length * repeats;
    println!(
        "decisions={decisions} elapsed_ns={elapsed} ns_per_decision={:.3}",
        elapsed as f64 / decisions as f64
    );
    Ok(())
}
