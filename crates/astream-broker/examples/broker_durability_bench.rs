//! Durability-dial throughput: the SAME single-producer workload at each tier, so the
//! cost of durability is explicit (not hidden inside a benchmark). DURABILITY=strict
//! acks after an fsync (survives power loss); DURABILITY=relaxed acks after a page-cache
//! write (survives a process crash, not power loss) and so is far faster on the
//! single-producer path because the fsync leaves the hot path.
//!
//! The METRIC line is labeled by the tier that actually ran
//! (`broker_strict_ops_per_sec` / `broker_relaxed_ops_per_sec`), and DURABILITY is
//! matched case-insensitively with any other value REJECTED (exit 2) — a mistyped
//! tier can never quietly measure Relaxed and report it as Strict. That mapping is
//! [`tier_of`], pinned by the unit tests below (this example is built with
//! `test = true`, so `cargo test -p astream-broker` runs them); the gated bench
//! command itself only ever runs the relaxed tier.
//!
//!   DURABILITY=relaxed BENCH_N=20000 cargo run --release -p astream-broker --example broker_durability_bench

#[cfg(any(unix, test))]
use astream_broker::Durability;
#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::time::Instant;

/// The canonical lowercase tier name (the METRIC label) and the [`Durability`] it
/// selects, from the raw `DURABILITY` value. `None` for anything else — the value is
/// REJECTED rather than defaulted, so a mistyped tier can never measure Relaxed and
/// report it under the Strict label. Label and durability come from ONE match, so
/// they cannot disagree.
#[cfg(any(unix, test))]
fn tier_of(raw: &str) -> Option<(&'static str, Durability)> {
    match raw.trim().to_ascii_lowercase().as_str() {
        "strict" => Some(("strict", Durability::Strict)),
        "relaxed" => Some(("relaxed", Durability::Relaxed)),
        _ => None,
    }
}

/// The bench serves the broker on a Unix-domain socket; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_durability_bench requires Unix-domain sockets; run it on a unix host");
}

/// Removes the bench's files when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the broker, so it drops after it.
#[cfg(unix)]
struct Cleanup(Vec<String>);

#[cfg(unix)]
impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let _ = std::fs::remove_file(path);
        }
    }
}

#[cfg(unix)]
fn main() {
    let pid = std::process::id();
    let log = format!("/tmp/asdur_{pid}.log");
    let sock = format!("/tmp/asdur_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup(vec![log.clone(), sock.clone()]);

    let raw_tier = std::env::var("DURABILITY").unwrap_or_else(|_| "relaxed".into());
    let Some((tier, durability)) = tier_of(&raw_tier) else {
        eprintln!(
            "broker_durability_bench: DURABILITY must be `strict` or `relaxed`, got {raw_tier:?}"
        );
        std::process::exit(2);
    };
    let n: u64 = std::env::var("BENCH_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20000);
    let payload = vec![0xABu8; 64];

    let broker = Broker::open_with(&log, durability).unwrap();
    let _h = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    let start = Instant::now();
    for i in 1..=n {
        c.publish(1, i, "/a/bench/x", &payload).unwrap(); // awaits ack (tier-defined)
    }
    let secs = start.elapsed().as_secs_f64();
    let ops = n as f64 / secs;

    println!("METRIC broker_{tier}_ops_per_sec {ops:.0}");
    eprintln!(
        "astream-broker {tier}: {n} single-producer publishes in {secs:.3}s = {ops:.0} ops/s (UDS)"
    );
}

#[cfg(test)]
mod tests {
    use super::tier_of;
    use astream_broker::Durability;

    /// The METRIC label and the Durability that actually runs come from one match,
    /// so a Strict figure can never be published under the Relaxed label (or the
    /// reverse). Spelling is case-insensitive and surrounding whitespace is trimmed.
    #[test]
    fn the_label_and_the_durability_cannot_disagree() {
        assert_eq!(tier_of("strict"), Some(("strict", Durability::Strict)));
        assert_eq!(tier_of("  Strict\n"), Some(("strict", Durability::Strict)));
        assert_eq!(tier_of("RELAXED"), Some(("relaxed", Durability::Relaxed)));
    }

    /// An unrecognized DURABILITY is REJECTED (the caller exits 2), never silently
    /// measured as Relaxed and reported under whatever label was asked for.
    #[test]
    fn an_unrecognized_durability_is_refused_not_defaulted() {
        assert_eq!(tier_of("bogus"), None);
        assert_eq!(tier_of(""), None);
        assert_eq!(tier_of("strictly"), None);
    }
}
