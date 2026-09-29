//! Group-commit throughput: N concurrent producers, each AWAITING durable acks. The
//! single writer thread folds everything that queued while one fsync ran into the next
//! batch, so aggregate durable-append throughput scales with concurrency — while every
//! record keeps the SAME Strict guarantee as the single-producer path (acked only
//! after the fsync that covers it). Contrast `broker_microbench` (1 producer, 1 fsync
//! per message): same durability, the difference is purely batched fsync.
//!
//!   PRODUCERS=64 BENCH_N=2000 cargo run --release -p astream-broker --example broker_groupcommit_bench

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::time::Instant;

#[cfg(unix)]
fn env(k: &str, d: u64) -> u64 {
    std::env::var(k)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(d)
}

/// The bench serves the broker on a Unix-domain socket; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_groupcommit_bench requires Unix-domain sockets; run it on a unix host");
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
    let log = format!("/tmp/asgc_{pid}.log");
    let sock = format!("/tmp/asgc_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup(vec![log.clone(), sock.clone()]);
    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();

    let producers: u64 = env("PRODUCERS", 64);
    let per: u64 = env("BENCH_N", 2000); // durable publishes per producer
    let total = producers * per;
    let payload = vec![0xABu8; 64];

    let start = Instant::now();
    let handles: Vec<_> = (0..producers)
        .map(|p| {
            let sock = sock.clone();
            let payload = payload.clone();
            std::thread::spawn(move || {
                let mut c = Client::connect(&sock).unwrap();
                let producer_id = p + 1; // a distinct exactly-once identity per thread
                for i in 1..=per {
                    // Blocks until the broker's batch fsync makes this record durable.
                    c.publish(producer_id, i, "/a/bench/x", &payload).unwrap();
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
    let secs = start.elapsed().as_secs_f64();
    let ops = total as f64 / secs;

    println!("METRIC broker_groupcommit_ops_per_sec {ops:.0}");
    eprintln!(
        "astream-broker group commit: {total} durable publishes ({producers} producers x {per}) \
         in {secs:.3}s = {ops:.0} ops/s (UDS, Strict, batched fsync)"
    );
}
