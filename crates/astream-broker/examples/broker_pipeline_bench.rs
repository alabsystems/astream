//! Single-connection pipelining throughput: ONE producer connection with many publishes
//! in flight at once. The broker streams acks back IN ORDER on a cloned write half while
//! it keeps reading, so the in-flight publishes coalesce into shared batches — one
//! connection saturates the writer. Contrast `broker_microbench` (one connection, ONE
//! publish in flight, an fsync per round trip): SAME fsync-before-ack guarantee at the
//! default DURABILITY=strict, the difference is purely depth-of-pipeline.
//!
//! DURABILITY and HORIZON_MS choose the tier exactly as `broker_durability_bench` does
//! (the same `bench_tier` match; strict when DURABILITY is unset, an empty HORIZON_MS
//! unset, an unknown tier, a horizon for another tier or a non-numeric one refused with
//! exit 2, and so is a broker serving Ordered at another horizon than the one asked
//! for). A command that must measure one tier says so (`DURABILITY=strict HORIZON_MS=`),
//! so neither knob reaches it from the environment it runs in. An aterm bridge uses one
//! pipelined Ordered connection. The commands of `broker.bench.ordered-pipeline-floor`
//! and `-full-flush-ceiling` select their own HORIZON_MS= and WINDOW= literals
//! (`evidence/manifest.toml`): each batch acked on an ordering barrier, and a full flush
//! once the horizon has passed since the first ack none covers. Those command values
//! are not derived from aterm's runtime configuration. aterm-link's fixture comparisons
//! cover the Ordered policy and retention fixtures; this example reads neither aterm's
//! constants nor those fixtures.
//!
//! AT_REST=1 seals the log at rest under a fixed bench key (`OpenOptions::at_rest_key`,
//! bound: a fresh `<log>.seal`), which a build without `--features at-rest` refuses with
//! exit 2; unset, empty or `0` is a plaintext log. Its metrics say so in their name
//! (`broker_<tier>_at_rest_pipeline_*`), so a sealed run never reads as a plaintext one and
//! a claim that reads the plaintext metric finds none in a sealed run.
//!
//! The METRIC lines are labeled by the tier the broker SERVED, read after the run
//! (`broker_<tier>_pipeline_ops_per_sec`, and `broker_<tier>_pipeline_full_flushes_per_sec`
//! and `broker_<tier>_pipeline_barriers_per_sec`, the full flushes and the ordering
//! barriers this process asked the OS for during the run per second of it, from
//! `astream_sys::flush_tally`, as `broker_durability_bench` reads them).
//!
//!   DURABILITY=strict HORIZON_MS= WINDOW=512 BENCH_N=20000 targo --unverified run --release -p astream-broker --example broker_pipeline_bench
//!   DURABILITY=ordered HORIZON_MS=100 WINDOW=64 BENCH_N=20000 targo --unverified run --release -p astream-broker --example broker_pipeline_bench
//!   AT_REST=1 DURABILITY=ordered HORIZON_MS=100 WINDOW=64 BENCH_N=20000 targo --unverified run --release -p astream-broker --features at-rest --example broker_pipeline_bench

#[cfg(unix)]
#[path = "bench_tier/mod.rs"]
mod bench_tier;

#[cfg(unix)]
use astream_broker::{Broker, Client, OpenOptions, Prepared};
#[cfg(unix)]
use std::process::ExitCode;
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
    let log = format!("/tmp/aspipe_{pid}.log");
    let sock = format!("/tmp/aspipe_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    // The log's identity sidecar too, which every open writes beside it, and a sealed
    // log's binding.
    let _tmp = Cleanup(vec![
        log.clone(),
        format!("{log}.id"),
        format!("{log}.seal"),
        sock.clone(),
    ]);
    let at_rest = match std::env::var("AT_REST").as_deref().map(str::trim) {
        Err(_) | Ok("" | "0") => false,
        Ok("1") => true,
        Ok(other) => {
            eprintln!("broker_pipeline_bench: AT_REST must be 1, 0 or unset, got {other:?}");
            return ExitCode::from(2);
        }
    };
    if at_rest && !cfg!(feature = "at-rest") {
        eprintln!("broker_pipeline_bench: AT_REST=1 needs a build with --features at-rest");
        return ExitCode::from(2);
    }

    let raw_tier = std::env::var("DURABILITY").unwrap_or_else(|_| "strict".into());
    let raw_horizon = std::env::var("HORIZON_MS").ok();
    let (asked, durability) = match bench_tier::tier_of(&raw_tier, raw_horizon.as_deref()) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("broker_pipeline_bench: {e}");
            return ExitCode::from(2);
        }
    };
    #[cfg_attr(not(feature = "at-rest"), allow(unused_mut))]
    let mut opts = OpenOptions::new(durability);
    #[cfg(feature = "at-rest")]
    if at_rest {
        opts.at_rest_key = Some([0x42; 32]);
        opts.require_bound_at_rest = true;
    }
    let broker = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
    if let Some(why) = bench_tier::horizon_mismatch(durability, &broker.served_durability()) {
        eprintln!("broker_pipeline_bench: {why}");
        return ExitCode::from(2);
    }
    let _h = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    let n = env("BENCH_N", 20000) as usize;
    let window = env("WINDOW", 512) as usize;
    let payload = vec![0xABu8; 64];
    let bodies: Vec<&[u8]> = (0..n).map(|_| payload.as_slice()).collect();

    let flushes_before = astream_sys::flush_tally();
    let start = Instant::now();
    let acks = c
        .publish_pipelined(1, "/a/bench/x", &bodies, window)
        .unwrap();
    let run = start.elapsed();
    let flushes_after = astream_sys::flush_tally();
    let secs = run.as_secs_f64();
    let full = flushes_after.full.saturating_sub(flushes_before.full);
    let per_sec = bench_tier::full_flushes_per_sec(flushes_before, flushes_after, run);
    let barrier = flushes_after.barrier.saturating_sub(flushes_before.barrier);
    let barriers_per_sec = bench_tier::barriers_per_sec(flushes_before, flushes_after, run);
    assert_eq!(acks.len(), n, "every pipelined publish was acked");
    let ops = n as f64 / secs;

    // The label is the tier SERVED once the run is over (see broker_durability_bench).
    let served = broker.served_durability();
    let served_tier = bench_tier::served_label(&served);
    let tier = if at_rest {
        format!("{served_tier}_at_rest")
    } else {
        served_tier.to_string()
    };
    if served_tier != asked {
        eprintln!(
            "broker_pipeline_bench: asked {raw_tier:?}, served {tier} ({:?})",
            served.reason
        );
    }
    println!("METRIC broker_{tier}_pipeline_ops_per_sec {ops:.0}");
    println!("METRIC broker_{tier}_pipeline_full_flushes_per_sec {per_sec:.2}");
    println!("METRIC broker_{tier}_pipeline_barriers_per_sec {barriers_per_sec:.2}");
    eprintln!(
        "astream-broker pipeline: {n} publishes on ONE connection (window {window}) in \
         {secs:.3}s = {ops:.0} ops/s (UDS, {tier}, horizon {:?} ms, {full} full flushes, \
         {per_sec:.2} a second, {barrier} barriers, {barriers_per_sec:.2} a second)",
        served.horizon_ms
    );
    ExitCode::SUCCESS
}
