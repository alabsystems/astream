//! Durability-dial throughput: the SAME single-producer workload at each tier, so the
//! cost of durability is explicit (not hidden inside a benchmark). DURABILITY=strict
//! acks after an fsync (survives power loss); DURABILITY=ordered acks after an ordering
//! barrier (F_BARRIERFSYNC: survives a power loss as a prefix of whole batches, the newest
//! possibly lost; served strict off Apple or off the boot volume, and then LABELLED strict,
//! saying so on stderr), with a full flush once HORIZON_MS has passed since the first ack
//! none covers (astream's one-second default when unset; aterm runs 100); DURABILITY=relaxed
//! acks after a page-cache write (survives a process crash, not power loss) and so is far
//! faster on the single-producer path because the fsync leaves the hot path.
//!
//! The METRIC lines are labeled by the tier the broker SERVED, read after the run
//! (`broker_strict_ops_per_sec` / `broker_ordered_ops_per_sec` / `broker_relaxed_ops_per_sec`,
//! and `broker_<tier>_full_flushes_per_sec` and `broker_<tier>_barriers_per_sec`, the full
//! flushes and the ordering barriers this process asked the OS for during the run per
//! second of it, from `astream_sys::flush_tally`, which counts each flush call the broker
//! makes whether or not `Broker::flush_counts` counts it; Relaxed issues neither; the one
//! broker is all that flushes here). DURABILITY is matched
//! case-insensitively with any other value REJECTED (exit 2), and so is a HORIZON_MS for
//! another tier or one that is not a number — a mistyped tier can never quietly measure
//! Relaxed and report it as Strict; an empty HORIZON_MS is unset, so `HORIZON_MS=` before
//! a command clears one it would inherit. A broker serving Ordered at another horizon
//! than the one asked for also exits 2. That parsing is `bench_tier` (shared with
//! `broker_pipeline_bench`), pinned by its unit tests (this example is built with
//! `test = true`, so `targo --unverified test -p astream-broker` runs them).
//!
//!   DURABILITY=relaxed BENCH_N=20000 targo --unverified run --release -p astream-broker --example broker_durability_bench
//!   DURABILITY=ordered HORIZON_MS=100 BENCH_N=5000 targo --unverified run --release -p astream-broker --example broker_durability_bench

#[cfg(any(unix, test))]
#[path = "bench_tier/mod.rs"]
mod bench_tier;

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::process::ExitCode;
#[cfg(unix)]
use std::time::Instant;

/// The bench serves the broker on a Unix-domain socket; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_durability_bench requires Unix-domain sockets; run it on a unix host");
}

/// Removes the bench's files when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the broker, so it drops after it. A refusal returns its
/// exit code from `main` rather than calling `std::process::exit`, which runs no
/// destructor and would leave the log and its sidecar behind.
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
fn main() -> ExitCode {
    let pid = std::process::id();
    let log = format!("/tmp/asdur_{pid}.log");
    let sock = format!("/tmp/asdur_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    // The log's identity sidecar too, which every open writes beside it.
    let _tmp = Cleanup(vec![log.clone(), format!("{log}.id"), sock.clone()]);

    let raw_tier = std::env::var("DURABILITY").unwrap_or_else(|_| "relaxed".into());
    let raw_horizon = std::env::var("HORIZON_MS").ok();
    let (asked, durability) = match bench_tier::tier_of(&raw_tier, raw_horizon.as_deref()) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("broker_durability_bench: {e}");
            return ExitCode::from(2);
        }
    };
    let n: u64 = std::env::var("BENCH_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20000);
    let payload = vec![0xABu8; 64];

    let broker = Broker::open_with(&log, durability).unwrap();
    if let Some(why) = bench_tier::horizon_mismatch(durability, &broker.served_durability()) {
        eprintln!("broker_durability_bench: {why}");
        return ExitCode::from(2);
    }
    let _h = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    let flushes_before = astream_sys::flush_tally();
    let start = Instant::now();
    for i in 1..=n {
        c.publish(1, i, "/a/bench/x", &payload).unwrap(); // awaits ack (tier-defined)
    }
    let run = start.elapsed();
    let flushes_after = astream_sys::flush_tally();
    let secs = run.as_secs_f64();
    let full = flushes_after.full.saturating_sub(flushes_before.full);
    let per_sec = bench_tier::full_flushes_per_sec(flushes_before, flushes_after, run);
    let barrier = flushes_after.barrier.saturating_sub(flushes_before.barrier);
    let barriers_per_sec = bench_tier::barriers_per_sec(flushes_before, flushes_after, run);
    let ops = n as f64 / secs;

    // The label is the tier SERVED once the run is over: an ordered request served
    // strict (off Apple, off the boot volume) or latched to strict during the run is
    // measured as what it is.
    let served = broker.served_durability();
    let tier = bench_tier::served_label(&served);
    if tier != asked {
        eprintln!(
            "broker_durability_bench: asked {raw_tier:?}, served {tier} ({:?})",
            served.reason
        );
    }
    println!("METRIC broker_{tier}_ops_per_sec {ops:.0}");
    println!("METRIC broker_{tier}_full_flushes_per_sec {per_sec:.2}");
    println!("METRIC broker_{tier}_barriers_per_sec {barriers_per_sec:.2}");
    eprintln!(
        "astream-broker {tier} (horizon {:?} ms): {n} single-producer publishes in {secs:.3}s = \
         {ops:.0} ops/s, {full} full flushes ({per_sec:.2} a second), {barrier} barriers \
         ({barriers_per_sec:.2} a second) (UDS)",
        served.horizon_ms
    );
    ExitCode::SUCCESS
}
