// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! CONNECTION SETUP latency: how long a NEW connection takes to be served — connect,
//! then one `Hello` round trip, timed from before the connect to after the reply. The
//! acceptor's design is the whole story here: a polling acceptor (the 20 ms
//! `ACCEPT_POLL` it replaced) makes each connection wait out the rest of the sleep it
//! lands in, a blocking one takes it the instant it arrives (claim
//! `broker.blocking-accept`). Uses only API every broker version has, so the same file
//! measures an older checkout for an A/B.
//!
//! Modes (first argument):
//!
//! * `b2b [N]` — N connections over a Unix socket, each opened right after the previous
//!   one was served: the pattern of an aterm attach's serial dials, and the polling
//!   acceptor's worst case (it went back to sleep the moment the queue was empty).
//! * `random [N]` — the same with a uniform 0-40 ms pause before each connect (a fixed
//!   seed, so every run pauses alike): connections arriving at unrelated times, like
//!   CLI verbs.
//! * `tcp [N]` — `b2b` over loopback TCP.
//! * `idle SECS` — serve a Unix and a TCP listener and do nothing for SECS. Run under
//!   `/usr/bin/time -l` at two durations: on macOS the slope of INVOLUNTARY context
//!   switches is the idle process's wakeups per second (the writer's 100 ms idle poll
//!   included in both checkouts) — about 93/s polling against 10/s blocking. The
//!   VOLUNTARY count does not track timer wakeups there (it stayed flat or fell
//!   between 2 s and 6 s in both checkouts), so its slope says nothing. The acceptor
//!   counters in the printed `stats()` are the direct measure.
//!
//! Each timed mode prints every sample (`raw <mode> ...`, for pooling interleaved
//! runs), then `n`, `p50/p95/p99/mean` in milliseconds, then the broker's `stats()`
//! (which, on a broker with them, carries the acceptor counters).
//!
//!   targo --unverified run --release -p astream-broker --example broker_accept_bench -- b2b 100

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_accept_bench requires Unix-domain sockets; run it on a unix host");
}

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
    fn next_ms(&mut self, max: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % (max + 1)
    }
}

#[cfg(unix)]
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.first().map_or("b2b", String::as_str);
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(100);
    // Under /tmp: a Darwin TMPDIR can push a socket path past SUN_LEN.
    let dir = std::path::PathBuf::from(format!("/tmp/asab-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("bench dir");
    let sock = dir.join("b.sock");
    let broker = Broker::open(dir.join("b.log")).expect("open");
    let unix = broker.serve(&sock).expect("serve unix");
    let tcp = broker.serve_tcp("127.0.0.1:0").expect("serve tcp");
    let tcp_addr = tcp.tcp_addr().expect("tcp addr").to_string();

    if mode == "idle" {
        std::thread::sleep(Duration::from_secs(n as u64));
        println!("idle {n}s {:?}", broker.stats());
    } else {
        let mut pauses = Pauses(0x9e37_79b9_7f4a_7c15);
        let mut ms = Vec::with_capacity(n);
        for _ in 0..n {
            if mode == "random" {
                std::thread::sleep(Duration::from_millis(pauses.next_ms(40)));
            }
            let t = Instant::now();
            if mode == "tcp" {
                Client::connect_tcp(&tcp_addr)
                    .expect("connect")
                    .hello()
                    .expect("hello");
            } else {
                Client::connect(&sock)
                    .expect("connect")
                    .hello()
                    .expect("hello");
            }
            ms.push(t.elapsed().as_secs_f64() * 1e3);
        }
        let mean = ms.iter().sum::<f64>() / ms.len() as f64;
        // Every sample, in arrival order, so runs interleaved with another checkout's
        // can be pooled before taking percentiles.
        let raw: Vec<String> = ms.iter().map(|m| format!("{m:.4}")).collect();
        println!("raw {mode} {}", raw.join(" "));
        ms.sort_by(f64::total_cmp);
        println!(
            "{mode} n={} p50={:.3} p95={:.3} p99={:.3} mean={:.3} ms",
            ms.len(),
            pct(&ms, 0.50),
            pct(&ms, 0.95),
            pct(&ms, 0.99),
            mean
        );
        println!("{:?}", broker.stats());
    }
    drop(unix);
    drop(tcp);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}
