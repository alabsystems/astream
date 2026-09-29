//! LIVE FAN-OUT throughput (fabric R12): `SUBS` subscribers are already tailing one
//! filter when `BENCH_N` records are published, and every one of them receives every
//! record, in order, with no gap. The broker fans out as N independent tail loops over
//! `Arc`-shared records (`broker.rs` `tail_loop`, `store.rs` `read_range`), so delivery
//! is OFF the commit path — this is the number that says whether that is still true.
//!
//! Three legs, one run, one publishing connection, so the legs differ only in how
//! many subscribers were attached:
//!
//! * `broker_fanout_deliveries_per_sec` — `SUBS x BENCH_N` deliveries over the wall
//!   time from the first publish to the last subscriber's last record. The gated
//!   floor.
//! * `broker_fanout_ingest_ratio` — durable publishes/s with `SUBS_LOW` live
//!   subscribers over publishes/s with NONE, in the same run. This is the SAME-RUN
//!   structural gate, and it runs at a low subscriber count deliberately: it must
//!   isolate "delivery is on the write path" from "this machine has fewer cores than
//!   subscribers". Fan-out done on, or synchronized with, the commit path costs the
//!   producer once per observer and collapses this toward `1/SUBS_LOW`. Below
//!   `MIN_INGEST_RATIO` the bench exits 2 — the run fails, not just a metric.
//! * `broker_fanout_ingest_ratio_full` — the same ratio at the full `SUBS`. REPORTED,
//!   NOT GATED, and it is not a structural signal: broker, writer and all `SUBS`
//!   subscribers are threads of THIS process, so past the core count it measures a
//!   saturated machine. It is printed because the honest headline is that fan-out to
//!   many observers is not free for the producer on a shared box.
//!
//!   SUBS=64 BENCH_N=20000 cargo run --release -p astream-broker --example broker_fanout_bench

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::sync::mpsc;
#[cfg(unix)]
use std::time::Instant;

/// Ingest with `SUBS_LOW` live subscribers must keep at least this share of its own
/// no-subscriber rate in the SAME run. A fan-out paid for on the write path would
/// divide the producer's rate by the observer count (0.25 at four); the observed
/// ratio is near 1, so this sits far from both.
#[cfg(unix)]
const MIN_INGEST_RATIO: f64 = 0.5;

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
    eprintln!("broker_fanout_bench requires Unix-domain sockets; run it on a unix host");
}

/// One leg: attach `subs` subscribers to `subject` at the current head, publish `n`
/// records on `w`, and wait for every subscriber to have received every one of them
/// at the exact offset the dense spine demands. Returns
/// `(durable publishes/s, aggregate deliveries/s)`.
#[cfg(unix)]
fn leg(
    w: &mut Client,
    sock: &str,
    subject: &'static str,
    producer_id: u64,
    subs: u64,
    bodies: &[&[u8]],
    window: usize,
) -> (f64, f64) {
    let n = bodies.len() as u64;
    let from = w.fetch(0, subject, 0).unwrap().1 .1;
    let (ready_tx, ready_rx) = mpsc::channel::<()>();
    let mut readers = Vec::with_capacity(subs as usize);
    for _ in 0..subs {
        let sock = sock.to_string();
        let ready = ready_tx.clone();
        readers.push(std::thread::spawn(move || {
            let mut sub = Client::connect(&sock)
                .unwrap()
                .subscribe(from, subject)
                .unwrap();
            ready.send(()).unwrap();
            let mut got = 0u64;
            // Every delivery is checked against the dense offset spine it must have,
            // so a fast-but-lossy fan-out cannot post a high number here.
            while got < n {
                match sub.recv().unwrap() {
                    Some((off, _, _)) if off == from + got => got += 1,
                    other => {
                        eprintln!("fan-out gap: expected offset {}, got {other:?}", from + got);
                        std::process::exit(2);
                    }
                }
            }
            got
        }));
    }
    for _ in 0..subs {
        ready_rx.recv().unwrap();
    }

    let t = Instant::now();
    w.publish_pipelined(producer_id, subject, bodies, window)
        .unwrap();
    let ops = n as f64 / t.elapsed().as_secs_f64();
    let mut delivered = 0u64;
    for r in readers {
        delivered += r.join().unwrap();
    }
    let secs = t.elapsed().as_secs_f64();
    if delivered != subs * n {
        eprintln!("expected {} deliveries, counted {delivered}", subs * n);
        std::process::exit(2);
    }
    (ops, delivered as f64 / secs)
}

/// Removes the bench's files when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the broker, so it drops after it; `main` drops it
/// by hand before a `process::exit`, which runs no destructors.
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
    let log = format!("/tmp/asfanout_{pid}.log");
    let sock = format!("/tmp/asfanout_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup(vec![log.clone(), sock.clone()]);
    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();

    let subs = env("SUBS", 64).max(1);
    let low = env("SUBS_LOW", 4).max(1).min(subs);
    let n = env("BENCH_N", 20_000).max(1);
    let window = env("WINDOW", 512).max(1) as usize;
    let body = vec![0xCDu8; env("BODY", 64) as usize];
    let bodies: Vec<&[u8]> = (0..n).map(|_| body.as_slice()).collect();

    let mut w = Client::connect(&sock).unwrap();

    // Leg 1: no subscribers — the producer's own rate, this run, this disk.
    let (quiet_ops, _) = leg(&mut w, &sock, "/fan/quiet", 1, 0, &bodies, window);
    // Leg 2: a few subscribers — the structural gate.
    let (low_ops, _) = leg(&mut w, &sock, "/fan/low", 2, low, &bodies, window);
    // Leg 3: the full fan-out — the gated delivery floor.
    let (full_ops, dps) = leg(&mut w, &sock, "/fan/live", 3, subs, &bodies, window);

    let ratio = low_ops / quiet_ops;
    let ratio_full = full_ops / quiet_ops;

    println!("METRIC broker_fanout_deliveries_per_sec {dps:.0}");
    println!("METRIC broker_fanout_ingest_ratio {ratio:.3}");
    println!("METRIC broker_fanout_ingest_ratio_full {ratio_full:.3}");
    eprintln!(
        "astream-broker fan-out: {subs} live subscribers x {n} records ({} B body) \
         = {} deliveries at {dps:.0} deliveries/s; durable ingest {quiet_ops:.0} ops/s with \
         no subscriber, {low_ops:.0} with {low} (ratio {ratio:.3}), {full_ops:.0} with \
         {subs} (ratio {ratio_full:.3}, machine-bound, not gated)",
        body.len(),
        subs * n
    );
    let _ = std::fs::remove_file(&log);

    if ratio < MIN_INGEST_RATIO {
        eprintln!(
            "FAIL: ingest ratio {ratio:.3} < {MIN_INGEST_RATIO} with only {low} subscribers — \
             the fan-out is being paid for on the write path"
        );
        drop(tmp);
        std::process::exit(2);
    }
}
