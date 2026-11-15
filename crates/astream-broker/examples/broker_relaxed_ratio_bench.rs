// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Relaxed against Strict IN ONE RUN: how many times a single producer's Relaxed ack
//! rate is its Strict ack rate, on two brokers in this process whose legs take turns,
//! so whatever slows the volume (another process flushing it in full, a busy host)
//! slows both legs within the same fraction of a second.
//!
//! `broker_relaxed_strict_ratio` — the Relaxed leg's publishes a second over the Strict
//! leg's — is gated by the claim `broker.bench.relaxed-strict-ratio`. A Relaxed ack that
//! waits for a full flush costs what a Strict ack costs however that flush is made, so
//! the ratio falls to about 1 on any volume where a full flush costs more than a
//! page-cache write. The Relaxed run's two flush-count ceilings count the flush calls the
//! process makes into astream-sys (`astream_sys::flush_tally`), which is every flush the
//! broker makes but a full one through `std::fs::File` directly; this ratio sees that one
//! too. It is gated by the claim, not by an exit here: a ratio of two rates is a timing
//! measurement, and the evidence runner re-measures a bench that misses its bound, which
//! an exit would bypass.
//!
//! `broker_ratio_relaxed_ops_per_sec` and `broker_ratio_strict_ops_per_sec`, each leg's
//! own rate, are reported and not gated.
//!
//! BENCH_ROUNDS rounds (default 100), each `STRICT_PER_ROUND` Strict publishes and then
//! `RELAXED_PER_ROUND` Relaxed ones, each leg timed alone and summed over the rounds. A
//! broker that does not serve the tier its leg names (Strict, Relaxed) exits 2: that is
//! no timing, and no re-measurement mends it.
//!
//!   BENCH_ROUNDS=100 targo --unverified run --release -p astream-broker --example broker_relaxed_ratio_bench

#[cfg(unix)]
use astream_broker::{Broker, Client, Durability, Tier};
#[cfg(unix)]
use std::process::ExitCode;
#[cfg(unix)]
use std::time::{Duration, Instant};

/// Strict publishes in each round, one in flight at a time.
#[cfg(unix)]
const STRICT_PER_ROUND: u64 = 10;

/// Relaxed publishes in each round, one in flight at a time: ten times the Strict ones,
/// so on a quiet volume, where a Relaxed ack is a hundred or more times faster, the
/// Relaxed leg is still long enough to time, and beside a neighbour, where it is a few
/// times faster, the run stays within about a minute.
#[cfg(unix)]
const RELAXED_PER_ROUND: u64 = 100;

/// The bench serves the brokers on Unix-domain sockets; std has no UDS on Windows, so
/// there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_relaxed_ratio_bench requires Unix-domain sockets; run it on a unix host");
}

/// Removes the bench's files when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the brokers, so it drops after them. A refusal returns
/// its exit code from `main` rather than calling `std::process::exit`, which runs no
/// destructor and would leave the logs and their sidecars behind.
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

/// One leg's share of a round: `n` publishes on `c`, each awaiting its ack, from
/// producer sequence `*seq + 1` on, timed together.
#[cfg(unix)]
fn leg(c: &mut Client, seq: &mut u64, n: u64, payload: &[u8]) -> Duration {
    let start = Instant::now();
    for _ in 0..n {
        *seq += 1;
        c.publish(1, *seq, "/a/bench/x", payload).unwrap();
    }
    start.elapsed()
}

#[cfg(unix)]
fn main() -> ExitCode {
    let pid = std::process::id();
    let strict_log = format!("/tmp/asratio_{pid}_strict.log");
    let relaxed_log = format!("/tmp/asratio_{pid}_relaxed.log");
    let strict_sock = format!("/tmp/asratio_{pid}_strict.sock");
    let relaxed_sock = format!("/tmp/asratio_{pid}_relaxed.sock");
    let _ = std::fs::remove_file(&strict_log);
    let _ = std::fs::remove_file(&relaxed_log);
    // Each log's identity sidecar too, which every open writes beside it.
    let _tmp = Cleanup(vec![
        strict_log.clone(),
        format!("{strict_log}.id"),
        relaxed_log.clone(),
        format!("{relaxed_log}.id"),
        strict_sock.clone(),
        relaxed_sock.clone(),
    ]);

    let rounds: u64 = std::env::var("BENCH_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let payload = vec![0xABu8; 64];

    let strict = Broker::open_with(&strict_log, Durability::Strict).unwrap();
    let relaxed = Broker::open_with(&relaxed_log, Durability::Relaxed).unwrap();
    let _hs = strict.serve(&strict_sock).unwrap();
    let _hr = relaxed.serve(&relaxed_sock).unwrap();
    let mut sc = Client::connect(&strict_sock).unwrap();
    let mut rc = Client::connect(&relaxed_sock).unwrap();

    // One untimed publish on each, so neither leg's first round pays for its
    // connection's first exchange.
    let (mut sseq, mut rseq) = (0u64, 0u64);
    let _ = leg(&mut sc, &mut sseq, 1, &payload);
    let _ = leg(&mut rc, &mut rseq, 1, &payload);

    let (mut strict_time, mut relaxed_time) = (Duration::ZERO, Duration::ZERO);
    for _ in 0..rounds {
        strict_time += leg(&mut sc, &mut sseq, STRICT_PER_ROUND, &payload);
        relaxed_time += leg(&mut rc, &mut rseq, RELAXED_PER_ROUND, &payload);
    }

    // The tiers SERVED once the run is over: a leg its broker did not serve at the tier
    // it names measured something else.
    for (name, broker, want) in [
        ("strict", &strict, Tier::Strict),
        ("relaxed", &relaxed, Tier::Relaxed),
    ] {
        let served = broker.served_durability();
        if served.served != want {
            eprintln!(
                "broker_relaxed_ratio_bench: the {name} leg's broker serves {:?} ({:?})",
                served.served, served.reason
            );
            return ExitCode::from(2);
        }
    }

    let strict_n = rounds * STRICT_PER_ROUND;
    let relaxed_n = rounds * RELAXED_PER_ROUND;
    let strict_ops = strict_n as f64 / strict_time.as_secs_f64().max(1e-9);
    let relaxed_ops = relaxed_n as f64 / relaxed_time.as_secs_f64().max(1e-9);
    let ratio = relaxed_ops / strict_ops.max(1e-9);
    println!("METRIC broker_relaxed_strict_ratio {ratio:.2}");
    println!("METRIC broker_ratio_relaxed_ops_per_sec {relaxed_ops:.0}");
    println!("METRIC broker_ratio_strict_ops_per_sec {strict_ops:.0}");
    eprintln!(
        "astream-broker relaxed against strict, {rounds} rounds: {relaxed_n} Relaxed \
         publishes at {relaxed_ops:.0} ops/s, {strict_n} Strict at {strict_ops:.0} ops/s, \
         ratio {ratio:.2} (UDS, one in flight each)"
    );
    ExitCode::SUCCESS
}
