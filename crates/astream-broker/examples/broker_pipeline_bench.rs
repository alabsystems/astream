//! Single-connection pipelining throughput: ONE producer connection with many publishes
//! in flight at once. The broker streams acks back IN ORDER on a cloned write half while
//! it keeps reading, so the in-flight publishes coalesce into shared group-commit fsyncs
//! — one connection saturates the writer. Contrast `broker_microbench` (one connection,
//! ONE publish in flight, an fsync per round trip): SAME Strict fsync-before-ack
//! guarantee, the difference is purely depth-of-pipeline.
//!
//!   WINDOW=512 BENCH_N=20000 cargo run --release -p astream-broker --example broker_pipeline_bench

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
    eprintln!("broker_pipeline_bench requires Unix-domain sockets; run it on a unix host");
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
    let log = format!("/tmp/aspipe_{pid}.log");
    let sock = format!("/tmp/aspipe_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup(vec![log.clone(), sock.clone()]);
    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    let n = env("BENCH_N", 20000) as usize;
    let window = env("WINDOW", 512) as usize;
    let payload = vec![0xABu8; 64];
    let bodies: Vec<&[u8]> = (0..n).map(|_| payload.as_slice()).collect();

    let start = Instant::now();
    let acks = c
        .publish_pipelined(1, "/a/bench/x", &bodies, window)
        .unwrap();
    let secs = start.elapsed().as_secs_f64();
    assert_eq!(acks.len(), n, "every pipelined publish was acked");
    let ops = n as f64 / secs;

    println!("METRIC broker_pipeline_ops_per_sec {ops:.0}");
    eprintln!(
        "astream-broker pipeline: {n} durable publishes on ONE connection \
         (window {window}) in {secs:.3}s = {ops:.0} ops/s (UDS, Strict, batched fsync)"
    );
}
