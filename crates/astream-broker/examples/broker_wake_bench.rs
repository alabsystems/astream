// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SUBSCRIBER WAKES AND PEER PROBES per delivered message: what one subscriber's
//! delivery costs every OTHER subscriber tail on the broker, and how long a record that
//! follows a batch some tail did not match waits to reach its subscriber.
//!
//! Every batch the writer commits used to wake every parked tail — a batch that made
//! nothing visible (an attach's re-bind, a deduplicated retry) and one holding only
//! hidden records (a group commit) included — and a tail that read a batch without
//! matching any of it then sat in a 1 ms blocking read of its own socket (the liveness
//! probe), deaf to the next wakeup. A lone delivery through aterm's bridge is two
//! batches: the publish, then a hidden `/a/commit`. aterm commits its inbox group once
//! per burst (aterm `78e8cbfdaf`: once no inbox record is queued, or every 256 records),
//! so only a delivery nothing is queued behind pays a commit of its own; `fanout`
//! measures exactly that lone delivery.
//!
//! Modes (first argument; `strict` anywhere picks the Strict tier, else Relaxed;
//! `selective` anywhere enables selective filter-indexed tail wakeups):
//!
//! * `fanout K [N]` — one subscriber on `/m/>` and K on `/n<i>/>` that match nothing;
//!   N messages (default 300), each a `/m/x` publish, its delivery, then a commit of
//!   group `g` to that offset, 2 ms apart. Prints the publish ack RTT and publish →
//!   recv, and per message the writer's batches, broadcasts, selective wakes, the tails'
//!   wakeups and the peer probes, from the broker's own counters.
//! * `probewin [N] [LAG_US]` — one subscriber on `/m/>`. Control: `/m/x` alone. Then a
//!   non-matching `/o/y` first and `/m/x` LAG µs later (default 300). Prints publish →
//!   recv and ack → recv for `/m/x` in each, and the probes per sample.
//!
//! Each timed series prints every sample (`raw <series> ...`, for pooling interleaved
//! runs), then `n`, `p50/p95/p99/mean` in milliseconds. Logs and sockets live under
//! /tmp (a Darwin TMPDIR can push a socket path past SUN_LEN; /tmp is on the same APFS
//! volume as a real fabric log).
//!
//!   targo --unverified run --release -p astream-broker --example broker_wake_bench -- fanout 32 300

#[cfg(unix)]
use astream_broker::{Broker, BrokerStats, Client, Durability};
#[cfg(unix)]
use std::sync::mpsc;
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_wake_bench requires Unix-domain sockets; run it on a unix host");
}

/// A wait for something that must happen: a hang detector, never a latency budget.
#[cfg(unix)]
const HANG: Duration = Duration::from_secs(60);

/// Percentile `q` (0..=1) of sorted `v`, nearest rank.
#[cfg(unix)]
fn pct(v: &[f64], q: f64) -> f64 {
    let i = ((q * v.len() as f64).ceil() as usize).clamp(1, v.len()) - 1;
    v[i]
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

/// The broker's counters over a series, per message.
#[cfg(unix)]
fn per_message(series: &str, before: &BrokerStats, after: &BrokerStats, n: usize) {
    let per = |a: u64, b: u64| (a - b) as f64 / n as f64;
    println!(
        "{series} per-message: batches={:.2} broadcasts={:.2} selective_wakes={:.2} wakeups={:.2} probes={:.2}",
        per(after.writer_batches, before.writer_batches),
        per(after.tail_broadcasts, before.tail_broadcasts),
        per(after.selective_tail_wakes, before.selective_tail_wakes),
        per(after.tail_wakeups, before.tail_wakeups),
        per(after.peer_probes, before.peer_probes),
    );
}

/// Wait until `tails` subscriber tails are parked: every wake of the last message has
/// been taken, so the counters read after this hold all of them.
#[cfg(unix)]
fn settle(broker: &Broker, tails: usize) {
    let t = Instant::now();
    while broker.stats().parked_tails != tails {
        assert!(t.elapsed() < HANG, "{tails} tails never parked");
        std::thread::sleep(Duration::from_millis(1));
    }
}

/// The receive side of the subscriber on `/m/>`: each delivery's body starts with its
/// sample number, sent here with the instant it was read.
#[cfg(unix)]
fn matching_subscriber(sock: &std::path::Path) -> mpsc::Receiver<(u64, Instant)> {
    let (tx, rx) = mpsc::channel();
    let mut sub = Client::connect(sock)
        .expect("connect")
        .subscribe(0, "/m/>")
        .expect("subscribe");
    std::thread::spawn(move || {
        while let Ok(Some((_off, _subject, body))) = sub.recv() {
            let seq = u64::from_le_bytes(body[..8].try_into().expect("sample number"));
            if tx.send((seq, Instant::now())).is_err() {
                break;
            }
        }
    });
    rx
}

#[cfg(unix)]
fn body(seq: u64) -> Vec<u8> {
    let mut b = seq.to_le_bytes().to_vec();
    b.extend_from_slice(&[7u8; 192]);
    b
}

#[cfg(unix)]
fn fanout(broker: &Broker, sock: &std::path::Path, k: usize, n: usize) {
    let rx = matching_subscriber(sock);
    let others: Vec<_> = (0..k)
        .map(|i| {
            Client::connect(sock)
                .expect("connect")
                .subscribe(0, &format!("/n{i}/>"))
                .expect("subscribe")
        })
        .collect();
    settle(broker, k + 1);
    let mut w = Client::connect(sock).expect("connect");
    let mut cm = Client::connect(sock).expect("connect");
    let before = broker.stats();
    let mut ack = Vec::with_capacity(n);
    let mut lat = Vec::with_capacity(n);
    for i in 0..n as u64 {
        let t0 = Instant::now();
        let (off, _) = w.publish(9, i + 1, "/m/x", &body(i)).expect("publish");
        ack.push(t0.elapsed().as_secs_f64() * 1e3);
        let (seq, at) = rx.recv_timeout(HANG).expect("delivery");
        assert_eq!(seq, i);
        lat.push((at - t0).as_secs_f64() * 1e3);
        cm.commit("g", off).expect("commit");
        std::thread::sleep(Duration::from_millis(2));
    }
    settle(broker, k + 1);
    let after = broker.stats();
    println!("fanout: 1 matching + {k} non-matching subscribers, publish then commit, 2 ms apart");
    report(&format!("fanout{k}-ack"), ack);
    report(&format!("fanout{k}-publish->recv"), lat);
    per_message(&format!("fanout{k}"), &before, &after, n);
    drop(others);
}

#[cfg(unix)]
fn probewin(broker: &Broker, sock: &std::path::Path, n: usize, lag: Duration) {
    let rx = matching_subscriber(sock);
    settle(broker, 1);
    let mut a = Client::connect(sock).expect("connect");
    let mut o = Client::connect(sock).expect("connect");
    let mut seq = 0u64;
    for (series, first) in [("alone", false), ("after-nonmatching", true)] {
        let before = broker.stats();
        let mut lat = Vec::with_capacity(n);
        let mut after_ack = Vec::with_capacity(n);
        for _ in 0..n {
            seq += 1;
            if first {
                o.publish(21, seq, "/o/y", b"o").expect("publish /o/y");
                let t = Instant::now();
                while t.elapsed() < lag {
                    std::hint::spin_loop();
                }
            }
            let t0 = Instant::now();
            a.publish(22, seq, "/m/x", &body(seq))
                .expect("publish /m/x");
            let acked = Instant::now();
            let (got, at) = rx.recv_timeout(HANG).expect("delivery");
            assert_eq!(got, seq);
            lat.push((at - t0).as_secs_f64() * 1e3);
            // Signed: the subscriber can read the record before the publisher reads
            // its ack.
            after_ack.push(if at >= acked {
                (at - acked).as_secs_f64() * 1e3
            } else {
                -(acked - at).as_secs_f64() * 1e3
            });
            std::thread::sleep(Duration::from_millis(3));
        }
        settle(broker, 1);
        let after = broker.stats();
        println!("probewin: {series} (lag {} us)", lag.as_micros());
        report(&format!("probewin-{series}-publish->recv"), lat);
        report(&format!("probewin-{series}-ack->recv"), after_ack);
        per_message(&format!("probewin-{series}"), &before, &after, n);
    }
}

#[cfg(unix)]
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let strict = args.iter().any(|a| a == "strict");
    let selective = args.iter().any(|a| a == "selective");
    let nums: Vec<u64> = args.iter().filter_map(|a| a.parse().ok()).collect();
    let mode = args.first().map_or("fanout", String::as_str);
    let dir = std::path::PathBuf::from(format!("/tmp/aswake-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("bench dir");
    let sock = dir.join("b.sock");
    let durability = if strict {
        Durability::Strict
    } else {
        Durability::Relaxed
    };
    let broker = Broker::open_with(dir.join("b.log"), durability).expect("open");
    if selective {
        broker.set_selective_tail_wake(true);
    }
    let unix = broker.serve(&sock).expect("serve unix");
    println!(
        "tier={} selective={selective}",
        if strict { "strict" } else { "relaxed" }
    );
    match mode {
        "probewin" => {
            let n = nums.first().copied().unwrap_or(300) as usize;
            let lag = Duration::from_micros(nums.get(1).copied().unwrap_or(300));
            probewin(&broker, &sock, n, lag);
        }
        _ => {
            let k = nums.first().copied().unwrap_or(5) as usize;
            let n = nums.get(1).copied().unwrap_or(300) as usize;
            fanout(&broker, &sock, k, n);
        }
    }
    println!("final {:?}", broker.stats());
    drop(unix);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}
