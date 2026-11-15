// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! GUARDED HANDSHAKE latency: how long a connection of an already-bound principal
//! takes to present aterm's eight-grant node ring (`Hello` + `attach_all`, four of the
//! grants `rw,p=<node>`), idle and beside one busy Strict publisher, and how long a
//! bare `Hello` takes on an open connection beside that publisher. Before claim
//! `broker.attach-settled-bind`, each of the four `rw,p=` grants queued a `Bind` to
//! the writer — an empty batch behind whatever batch, fsync included, the writer was
//! in — and `Hello` read the log identity under the log lock the writer holds across
//! its fsync. Uses only API every guarded broker version has, so the same file
//! measures an older checkout for an interleaved A/B.
//!
//! Modes (first argument; N samples each, default 100):
//!
//! * `idle [N]` — `attach_all` of the bound ring on a fresh connection, nothing else
//!   running.
//! * `busy [N]` — the same beside one thread publishing serially on its own connection
//!   (each publish its own Strict batch and fsync), then N bare `Hello`s on one open
//!   connection beside it.
//!
//! A fixed-seed uniform 0-5 ms pause precedes each sample, so samples land at
//! unrelated phases of the publisher's fsync cycle and every run pauses alike. Each
//! timed series prints every sample (`raw <series> ...`, for pooling interleaved runs),
//! then `n`, `p50/p95/p99/mean` in milliseconds; the broker's `stats()` is printed
//! before and after the attach series (on a broker with them, the writer counters:
//! their growth over N is the per-connection round trips and empty batches; the busy
//! publisher's own batches are never empty and make no blocking round trip).
//!
//!   targo --unverified run --release -p astream-broker --features cap --example broker_attach_bench -- busy 100

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use astream_cap::{mint, producer_id_of, Capability};
#[cfg(unix)]
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(unix)]
use std::sync::Arc;
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_attach_bench requires Unix-domain sockets; run it on a unix host");
}

#[cfg(unix)]
const SECRET: &[u8] = b"attach-bench-secret";

/// Percentile `q` (0..=1) of sorted `v`, nearest rank.
#[cfg(unix)]
fn pct(v: &[f64], q: f64) -> f64 {
    let i = ((q * v.len() as f64).ceil() as usize).clamp(1, v.len()) - 1;
    v[i]
}

/// A fixed-seed xorshift: the same pause sequence in every run of every checkout.
#[cfg(unix)]
struct Pauses(u64);

#[cfg(unix)]
impl Pauses {
    fn next_us(&mut self, max: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % (max + 1)
    }
}

/// The shape of aterm's node ring (`enable::node_grants`, as of aterm `1a907413db`) for
/// `node` on fleet `F`.
#[cfg(unix)]
fn node_ring(node: &str) -> Vec<Capability> {
    [
        format!("rw,p={node}:/f/F/pub/{node}/>"),
        "ro:/f/F/pub/>".to_string(),
        "ro:/f/F/fleet/>".to_string(),
        format!("rw,p={node}:/f/F/in/*/*/{node}/*"),
        format!("ro:/f/F/in/{node}/>"),
        format!("rw,p={node}:/f/F/cur/{node}/>"),
        format!("ro:/f/F/term/{node}/>"),
        format!("rw,p={node}:/f/F/term/{node}/*/screen"),
    ]
    .iter()
    .map(|g| mint(SECRET, g).expect("mint"))
    .collect()
}

#[cfg(unix)]
fn attach(c: &mut Client, ring: &[Capability]) {
    c.attach_all(ring.iter().map(|g| (g.filter.as_str(), &g.tag[..])))
        .expect("attach_all");
}

#[cfg(unix)]
fn report(series: &str, mut ms: Vec<f64>) {
    let mean = ms.iter().sum::<f64>() / ms.len() as f64;
    let raw: Vec<String> = ms.iter().map(|m| format!("{m:.4}")).collect();
    println!("raw {series} {}", raw.join(" "));
    ms.sort_by(f64::total_cmp);
    println!(
        "{series} n={} p50={:.3} p95={:.3} p99={:.3} mean={:.3} ms",
        ms.len(),
        pct(&ms, 0.50),
        pct(&ms, 0.95),
        pct(&ms, 0.99),
        mean
    );
}

#[cfg(unix)]
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.first().map_or("busy", String::as_str);
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(100);
    // Under /tmp: a Darwin TMPDIR can push a socket path past SUN_LEN; /tmp is on the
    // same APFS volume as a real fabric log.
    let dir = std::path::PathBuf::from(format!("/tmp/asatb-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("bench dir");
    let sock = dir.join("b.sock");
    let broker = Broker::open_guarded(dir.join("b.log"), SECRET.to_vec()).expect("open");
    let unix = broker.serve(&sock).expect("serve unix");
    let ring = node_ring("n-node1");
    // Bind the principal once, as an earlier attach of the node would have.
    attach(&mut Client::connect(&sock).expect("connect"), &ring);

    let stop = Arc::new(AtomicBool::new(false));
    let publisher = (mode == "busy").then(|| {
        let mut p = Client::connect(&sock).expect("connect publisher");
        attach(
            &mut p,
            &[mint(SECRET, "rw,p=n-pub:/f/F/pub/n-pub/>").expect("mint")],
        );
        let stop = Arc::clone(&stop);
        std::thread::spawn(move || {
            let pid = producer_id_of("n-pub");
            let mut seq = 0u64;
            while !stop.load(Ordering::Relaxed) {
                seq += 1;
                p.publish(pid, seq, "/f/F/pub/n-pub/ev", b"busy")
                    .expect("publish");
            }
            seq
        })
    });
    if publisher.is_some() {
        // Let the publisher reach its steady fsync cycle before sampling.
        std::thread::sleep(Duration::from_millis(200));
    }

    let mut pauses = Pauses(0x9e37_79b9_7f4a_7c15);
    println!("before {:?}", broker.stats());
    let mut attach_ms = Vec::with_capacity(n);
    let mut total_ms = Vec::with_capacity(n);
    for _ in 0..n {
        std::thread::sleep(Duration::from_micros(pauses.next_us(5_000)));
        let t0 = Instant::now();
        let mut c = Client::connect(&sock).expect("connect");
        let t1 = Instant::now();
        attach(&mut c, &ring);
        let t2 = Instant::now();
        attach_ms.push((t2 - t1).as_secs_f64() * 1e3);
        total_ms.push((t2 - t0).as_secs_f64() * 1e3);
    }
    println!("after {:?}", broker.stats());
    report(&format!("{mode}-attach"), attach_ms);
    report(&format!("{mode}-connect+attach"), total_ms);

    if publisher.is_some() {
        let mut c = Client::connect(&sock).expect("connect");
        let mut hello_ms = Vec::with_capacity(n);
        for _ in 0..n {
            std::thread::sleep(Duration::from_micros(pauses.next_us(5_000)));
            let t = Instant::now();
            c.hello().expect("hello");
            hello_ms.push(t.elapsed().as_secs_f64() * 1e3);
        }
        report(&format!("{mode}-hello"), hello_ms);
    }
    stop.store(true, Ordering::Relaxed);
    if let Some(p) = publisher {
        println!("publishes {}", p.join().expect("publisher"));
    }
    drop(unix);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}
