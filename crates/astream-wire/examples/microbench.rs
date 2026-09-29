//! Wire-layer microbenchmarks for the regression gate.
//!
//! Prints `METRIC <name> <ops_per_sec>` lines that `astream-evidence` checks
//! against a floor. This is a *regression* gate (catch a catastrophic slowdown
//! on the substrate's hot paths), not a cross-system comparison — those land
//! with the broker, on disclosed hardware, in a later phase.
//!
//! Run with `--release` for representative numbers:
//!   cargo run --release -p astream-wire --example microbench

use astream_wire::{crc32_ieee, Filter, Frame, Subject};
use std::hint::black_box;
use std::time::Instant;

fn main() {
    // Frame encode + decode round-trip throughput.
    let payload = vec![0xABu8; 256];
    let iters: u64 = 200_000;
    let start = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        let bytes = Frame::new(payload.clone()).encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        acc += decoded.frame.payload.len();
    }
    black_box(acc);
    let ops = iters as f64 / start.elapsed().as_secs_f64();
    println!("METRIC frame_roundtrip_ops_per_sec {ops:.0}");

    // Wildcard matcher throughput.
    let filter = Filter::new("/a/*/events/>").unwrap();
    let subject = Subject::new("/a/stream/events/x/y").unwrap();
    let iters2: u64 = 1_000_000;
    let start2 = Instant::now();
    let mut hits = 0u64;
    for _ in 0..iters2 {
        if filter.matches(&subject) {
            hits += 1;
        }
    }
    black_box(hits);
    let mops = iters2 as f64 / start2.elapsed().as_secs_f64();
    println!("METRIC match_ops_per_sec {mops:.0}");

    // CRC-32 payload-integrity throughput. crc32_ieee runs on EVERY frame encode
    // and decode, so its per-byte cost is the broker's per-record floor.
    //
    // The thing worth gating is that the table-driven form has not regressed to the
    // eight-shifts-per-byte bitwise one, and that is a RATIO, not a rate. An absolute
    // MiB/s floor cannot express it: machine load moves the absolute number and leaves
    // the ratio alone, so an absolute floor fails on a busy machine while a genuine
    // regression on an idle one can still clear it. So measure both forms over the same
    // buffer, back to back, under whatever contention this machine happens to be under,
    // and gate the ratio. The MiB/s line is still printed, for information only.
    let buf = vec![0x5Au8; 64 * 1024];
    let iters3: u64 = 4_000;
    let start3 = Instant::now();
    let mut cacc = 0u32;
    for _ in 0..iters3 {
        cacc ^= crc32_ieee(black_box(&buf));
    }
    black_box(cacc);
    let table_secs = start3.elapsed().as_secs_f64();
    let mib = (iters3 as f64 * buf.len() as f64) / (1024.0 * 1024.0) / table_secs;
    println!("METRIC crc32_mib_per_sec {mib:.0}");

    // The naive form this crate deliberately does not use: one shift per bit, eight per
    // byte, no table. Kept HERE and never in the library, so the reference cannot drift
    // into the hot path. Fewer iterations because it is expected to be several times
    // slower; the ratio is normalised by bytes processed, so the counts need not match.
    let iters4: u64 = 500;
    let start4 = Instant::now();
    let mut bacc = 0u32;
    for _ in 0..iters4 {
        bacc ^= crc32_bitwise(black_box(&buf));
    }
    black_box(bacc);
    let bitwise_secs = start4.elapsed().as_secs_f64();
    let bitwise_mib = (iters4 as f64 * buf.len() as f64) / (1024.0 * 1024.0) / bitwise_secs;
    println!("METRIC crc32_bitwise_mib_per_sec {bitwise_mib:.0}");
    println!("METRIC crc32_speedup_vs_bitwise {:.2}", mib / bitwise_mib);

    // Both forms must agree, or the ratio above is comparing two different functions.
    assert_eq!(
        crc32_ieee(&buf),
        crc32_bitwise(&buf),
        "the bitwise reference and the table-driven form disagree, so the speedup ratio \
         above is meaningless"
    );
}

/// The eight-shifts-per-byte CRC-32/IEEE, as the reference the table-driven form in
/// `astream-wire` is gated against. Deliberately confined to this example.
fn crc32_bitwise(bytes: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}
