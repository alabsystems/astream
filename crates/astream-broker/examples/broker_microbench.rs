//! Broker durable-publish throughput, for the regression floor and the cross-system
//! comparison. Each publish AWAITS its ack — and the broker acks only after the
//! Strict fsync — so this measures genuine fsync-per-message durable-append
//! throughput over a Unix socket, single producer (the strictest, fairest workload
//! to compare against another bus at equal durability).
//!
//!   cargo run --release -p astream-broker --example broker_microbench

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::time::Instant;

/// The bench serves the broker on a Unix-domain socket; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_microbench requires Unix-domain sockets; run it on a unix host");
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
    let log = format!("/tmp/asbench_{pid}.log");
    let sock = format!("/tmp/asbench_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup(vec![log.clone(), sock.clone()]);

    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    let n: u64 = std::env::var("BENCH_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);
    let payload = vec![0xABu8; 64];

    let start = Instant::now();
    for i in 1..=n {
        c.publish(1, i, "/a/bench/x", &payload).unwrap(); // awaits ack == durable (fsync'd)
    }
    let secs = start.elapsed().as_secs_f64();
    let ops = n as f64 / secs;
    println!("METRIC broker_publish_ops_per_sec {ops:.0}");
    eprintln!("astream-broker: {n} durable publishes in {secs:.3}s = {ops:.0} ops/s (UDS, Strict fsync-per-msg)");
}
