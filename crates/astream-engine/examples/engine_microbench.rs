//! Engine-layer microbenchmarks for the regression gate.
//!
//! Prints `METRIC <name> <ops_per_sec>` lines that `astream-evidence` checks
//! against a floor. This is a *regression* gate (catch a catastrophic slowdown on
//! the engine's hot paths — record append and read-by-offset replay), not a
//! cross-system comparison; those land with the broker on disclosed hardware.
//!
//! Run with `--release` for representative numbers:
//!   cargo run --release -p astream-engine --example engine_microbench

use astream_engine::{Disk, Effects, Log, MemDisk, Offset, Seeded};
use astream_term::Record;
use std::hint::black_box;
use std::time::Instant;

fn main() {
    // Append throughput: Record -> versioned envelope -> CRC frame -> in-memory disk
    // through the effect seam (the single-writer hot path).
    let iters: u64 = 200_000;
    let mut fx = Seeded::new(1);
    let mut log = Log::new();
    let record = Record::Out(vec![0xABu8; 64]);
    let start = Instant::now();
    let mut acc = 0u64;
    for _ in 0..iters {
        let off = log.append(&mut fx, record.clone()).unwrap();
        acc += off.0;
    }
    black_box(acc);
    let ops = iters as f64 / start.elapsed().as_secs_f64();
    println!("METRIC engine_append_ops_per_sec {ops:.0}");

    // Replay throughput: a separate read-by-offset pass over ONLY the stored bytes
    // (Frame::decode + Envelope::from_payload), the replay hot path.
    let stored = fx.disk().read_all().to_vec();
    let disk = MemDisk::from_bytes(stored);
    let start2 = Instant::now();
    let mut n = 0u64;
    for item in Log::read_from(&disk, Offset::ZERO) {
        let env = item.expect("decode envelope from stored bytes");
        n += env.seq.0 & 1; // touch the decoded value so it can't be optimized away
    }
    black_box(n);
    let rops = iters as f64 / start2.elapsed().as_secs_f64();
    println!("METRIC engine_replay_ops_per_sec {rops:.0}");
}
