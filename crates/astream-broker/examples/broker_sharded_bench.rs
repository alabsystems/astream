//! Share-nothing sharding throughput probe: SHARDS independent brokers, PRODUCERS
//! concurrent producers spreading durable publishes across them. A measurement TOOL,
//! not a regression-gated claim — and the honest result on a SINGLE DISK at Strict
//! durability is that throughput does NOT scale with shards and can DROP: one
//! optimally-batched log is already disk-fsync-bound, so splitting a fixed producer set
//! across N shards fragments group-commit batching across N fsync streams contending
//! for the one disk. Sharding's win is HORIZONTAL (multiple disks/nodes) or in a
//! CPU/lock-bound regime (the Relaxed tier). Use this to measure your hardware; do not
//! read a single-disk Strict run as a scaling win. Compare SHARDS=1 vs 2 vs 4 vs 8.
//!
//!   SHARDS=4 PRODUCERS=64 BENCH_N=300 cargo run --release -p astream-broker --example broker_sharded_bench

#[cfg(unix)]
use astream_broker::{ShardedBroker, ShardedClient};
#[cfg(unix)]
use std::time::Instant;

#[cfg(unix)]
fn env(k: &str, d: u64) -> u64 {
    std::env::var(k)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(d)
}

/// The bench serves one Unix-domain socket per shard; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_sharded_bench requires Unix-domain sockets; run it on a unix host");
}

/// Removes the bench's directory when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the broker, so it drops after it.
#[cfg(unix)]
struct Cleanup(std::path::PathBuf);

#[cfg(unix)]
impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[cfg(unix)]
fn main() {
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("astream_shbench_{pid}"));
    let _ = std::fs::remove_dir_all(&dir);
    let _tmp = Cleanup(dir.clone());
    let logs = dir.join("logs");
    let socks = dir.join("socks");

    let shards = env("SHARDS", 4) as u32;
    let producers = env("PRODUCERS", 64);
    let per = env("BENCH_N", 300); // durable publishes per producer
    let total = producers * per;
    let payload = vec![0xABu8; 64];

    let b = ShardedBroker::open(&logs, shards).unwrap();
    let _h = b.serve(&socks).unwrap();

    let start = Instant::now();
    let handles: Vec<_> = (0..producers)
        .map(|p| {
            let socks = socks.clone();
            let payload = payload.clone();
            std::thread::spawn(move || {
                let mut c = ShardedClient::connect(&socks, shards).unwrap();
                // Distinct subject per producer → routes (statistically) across shards,
                // so all writers stay busy.
                let subject = format!("/a/sh/{p}");
                for i in 1..=per {
                    c.publish(p + 1, i, &subject, &payload).unwrap();
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
    let secs = start.elapsed().as_secs_f64();
    let ops = total as f64 / secs;

    println!("METRIC broker_sharded_ops_per_sec {ops:.0}");
    eprintln!(
        "astream-broker sharded: {total} durable publishes ({producers} producers x {per}) \
         across {shards} shards in {secs:.3}s = {ops:.0} ops/s (UDS, Strict)"
    );
}
