//! Egress / replay throughput: fill a log with N records, then a subscriber replays the
//! whole backlog from offset 0. This exercises the catch-up read path — `read_range`
//! hands out shared `Arc` records a bounded chunk at a time (no deep copy of
//! subject/body out of the log) and each delivery frame is assembled directly from the
//! borrowed record (no clone-to-deliver). Records/sec here is the delivery hot path,
//! separate from the publish/durability path.
//!
//!   BENCH_N=20000 BODY=256 cargo run --release -p astream-broker --example broker_replay_bench

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
    eprintln!("broker_replay_bench requires Unix-domain sockets; run it on a unix host");
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
    let log = format!("/tmp/asreplay_{pid}.log");
    let sock = format!("/tmp/asreplay_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup(vec![log.clone(), sock.clone()]);
    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();

    let n = env("BENCH_N", 20000);
    let body = vec![0xCDu8; env("BODY", 256) as usize];

    // Fill the log (pipelined so setup is fast; durability is not what we measure here).
    {
        let mut p = Client::connect(&sock).unwrap();
        let bodies: Vec<&[u8]> = (0..n).map(|_| body.as_slice()).collect();
        p.publish_pipelined(1, "/a/replay/x", &bodies, 256).unwrap();
    }

    // Replay the whole backlog from offset 0 through the egress path.
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/replay/>")
        .unwrap();
    let start = Instant::now();
    for _ in 0..n {
        sub.recv().unwrap().unwrap();
    }
    let secs = start.elapsed().as_secs_f64();
    let ops = n as f64 / secs;

    println!("METRIC broker_replay_ops_per_sec {ops:.0}");
    eprintln!(
        "astream-broker replay: {n} records ({} B body) delivered from offset 0 \
         in {secs:.3}s = {ops:.0} deliveries/s (UDS, Arc-shared egress)",
        body.len()
    );
}
