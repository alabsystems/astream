// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! READERS AND TAILS BESIDE A BUSY STRICT WRITER: what the log lock costs them while a
//! batch is written and flushed. Before claim `broker.unlocked-batch-write` the writer
//! held the log lock from staging through the batch's `write` and `F_FULLFSYNC` to its
//! promotion, so every reader that takes the lock — a `Fetch` page, a `Last` round, a
//! tail copying the record it was just woken for — waited out most of an fsync, and a
//! subscriber woken by one batch could lose the lock to the next queued batch and
//! receive its record a whole fsync after the ack. Uses only API every broker version
//! has, so the same file measures an older checkout for an interleaved A/B.
//!
//! Modes (first argument; N samples per series, default 200):
//!
//! * `reads [N]` — on one open connection, a `Hello`, a 4-row `Fetch` and a 4-row
//!   `Last` page, first with the broker idle, then beside one thread publishing
//!   serially on its own connection (each publish its own Strict batch and fsync). The
//!   publisher writes a subject the reads do not match, so every read returns the same
//!   four rows. (`Hello` takes no log lock on a broker with claim
//!   `broker.attach-settled-bind`; it is the control.)
//! * `behind [N]` — one subscriber on `/m/>`. Series `alone`: producer A publishes
//!   `/m/x` and waits for its ack and its delivery. Series `queued`: the same, and 1 ms
//!   after A's publish (inside A's fsync) producer B publishes `/o/y` on another
//!   connection, so B's batch is queued the moment A's ends — the tail woken for A
//!   races B's batch for the log lock.
//!
//! A fixed-seed uniform 0-5 ms pause precedes each `reads` sample (and a fixed 3 ms
//! gap each `behind` sample), so samples land at unrelated phases of the publisher's
//! fsync cycle and every run pauses alike. Each timed series prints every sample
//! (`raw <series> ...`, for pooling interleaved runs), then `n`, `p50/p95/p99/mean` in
//! milliseconds; `recv-minus-ack` is signed (negative: the delivery came first). The
//! broker's `stats()` is printed around each phase.
//!
//!   targo --unverified run --release -p astream-broker --example broker_unlocked_write_bench -- reads 200

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
#[cfg(unix)]
use std::sync::{mpsc, Arc};
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_unlocked_write_bench requires Unix-domain sockets; run it on a unix host");
}

/// A short, exclusively created parent. Never adopts or pre-removes an occupied name.
#[cfg(unix)]
struct Scratch(std::path::PathBuf);

#[cfg(unix)]
impl Scratch {
    fn new() -> std::io::Result<Self> {
        use std::os::unix::fs::DirBuilderExt;
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let path = std::path::PathBuf::from(format!("/tmp/asuwb-{}-{n}", std::process::id()));
            match builder.create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e),
            }
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "no exclusive benchmark scratch name",
        ))
    }
}

#[cfg(unix)]
impl Drop for Scratch {
    fn drop(&mut self) {
        // Only a parent this owner successfully created can reach cleanup.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Owns the subscriber thread and the exact socket that can stop its blocking read.
#[cfg(unix)]
struct Subscriber {
    stop: std::os::unix::net::UnixStream,
    join: Option<std::thread::JoinHandle<()>>,
}

#[cfg(unix)]
impl Drop for Subscriber {
    fn drop(&mut self) {
        let _ = self.stop.shutdown(std::net::Shutdown::Both);
        if let Some(join) = self.join.take() {
            let _ = join.join();
        }
    }
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
    fn next_us(&mut self, max: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % (max + 1)
    }
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
fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// One thread publishing serially on its own connection until `stop`: each publish is
/// its own Strict batch, so the writer is always in a batch or about to be. Returns the
/// publish round trips.
#[cfg(unix)]
fn busy_publisher(
    sock: &std::path::Path,
    stop: &Arc<AtomicBool>,
) -> std::thread::JoinHandle<Vec<f64>> {
    let mut p = Client::connect(sock).expect("connect publisher");
    let stop = Arc::clone(stop);
    std::thread::spawn(move || {
        let mut rtt = Vec::new();
        let mut seq = 0u64;
        while !stop.load(Ordering::Relaxed) {
            seq += 1;
            let t = Instant::now();
            p.publish(9, seq, "/p/ev", b"busy").expect("publish");
            rtt.push(ms(t.elapsed()));
        }
        rtt
    })
}

#[cfg(unix)]
fn reads(broker: &Broker, sock: &std::path::Path, n: usize) {
    // Four subjects, 25 records each: offsets 0..100, the last four /t/0../t/3.
    let mut w = Client::connect(sock).expect("connect");
    for i in 0..100u64 {
        w.publish(1, i + 1, &format!("/t/{}", i % 4), &[7u8; 200])
            .expect("fill");
    }
    let mut c = Client::connect(sock).expect("connect reader");
    let mut pauses = Pauses(0x9e37_79b9_7f4a_7c15);
    for phase in ["idle", "busy"] {
        let stop = Arc::new(AtomicBool::new(false));
        let publisher = (phase == "busy").then(|| busy_publisher(sock, &stop));
        if publisher.is_some() {
            // Let the publisher reach its steady fsync cycle before sampling.
            std::thread::sleep(Duration::from_millis(200));
        }
        println!("before-{phase} {:?}", broker.stats());
        let (mut hello, mut fetch, mut last) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..n {
            std::thread::sleep(Duration::from_micros(pauses.next_us(5_000)));
            let t = Instant::now();
            c.hello().expect("hello");
            hello.push(ms(t.elapsed()));
            std::thread::sleep(Duration::from_micros(pauses.next_us(5_000)));
            let t = Instant::now();
            let page = c.fetch(96, "/t/>", 4).expect("fetch");
            fetch.push(ms(t.elapsed()));
            assert_eq!(page.0.len(), 4, "the Fetch page");
            std::thread::sleep(Duration::from_micros(pauses.next_us(5_000)));
            let t = Instant::now();
            let page = c.last("/t/>", "", 4).expect("last");
            last.push(ms(t.elapsed()));
            assert_eq!(page.0.len(), 4, "the Last page");
        }
        stop.store(true, Ordering::Relaxed);
        let publishes = publisher.map(|p| p.join().expect("publisher"));
        println!("after-{phase} {:?}", broker.stats());
        report(&format!("{phase}-hello"), hello);
        report(&format!("{phase}-fetch4"), fetch);
        report(&format!("{phase}-last4"), last);
        if let Some(rtt) = publishes {
            report(&format!("{phase}-publisher-publish"), rtt);
        }
    }
}

#[cfg(unix)]
fn behind(broker: &Broker, sock: &std::path::Path, n: usize) {
    let (tx, rx) = mpsc::channel::<(u64, Instant)>();
    let mut sub = Client::connect(sock)
        .expect("connect subscriber")
        .subscribe(0, "/m/>")
        .expect("subscribe");
    // Clone before handing the subscription to its worker: this guard can stop only
    // this owned connection, and joins on completion and on an unwinding exit.
    let stop = sub
        .get_ref()
        .try_clone()
        .expect("subscriber shutdown handle");
    let join = std::thread::spawn(move || {
        while let Ok(Some((_, _, body))) = sub.recv() {
            let seq = u64::from_le_bytes(body[..8].try_into().expect("seq"));
            if tx.send((seq, Instant::now())).is_err() {
                break;
            }
        }
    });
    let _subscriber = Subscriber {
        stop,
        join: Some(join),
    };
    let mut a = Client::connect(sock).expect("connect A");
    let mut b = Client::connect(sock).expect("connect B");
    for (series, queued) in [("alone", false), ("queued", true)] {
        println!("before-{series} {:?}", broker.stats());
        let (mut ack, mut recv, mut gap) = (Vec::new(), Vec::new(), Vec::new());
        for i in 0..n as u64 {
            let seq = if queued { 1_000_000 + i } else { i + 1 };
            let mut body = seq.to_le_bytes().to_vec();
            body.extend_from_slice(&[1u8; 100]);
            let t0 = Instant::now();
            a.send_publish(11, seq, "/m/x", &body).expect("A send");
            if queued {
                std::thread::sleep(Duration::from_millis(1));
                b.send_publish(12, seq, "/o/y", b"other").expect("B send");
            }
            a.recv_publish_ack().expect("A ack");
            let acked = Instant::now();
            let (got, at) = rx
                .recv_timeout(Duration::from_secs(60))
                .expect("the delivery of A's record");
            assert_eq!(got, seq, "the delivery is A's record");
            if queued {
                b.recv_publish_ack().expect("B ack");
            }
            ack.push(ms(acked - t0));
            recv.push(ms(at - t0));
            gap.push(if at >= acked {
                ms(at - acked)
            } else {
                -ms(acked - at)
            });
            std::thread::sleep(Duration::from_millis(3));
        }
        println!("after-{series} {:?}", broker.stats());
        report(&format!("{series}-ack"), ack);
        report(&format!("{series}-publish-to-recv"), recv);
        report(&format!("{series}-recv-minus-ack"), gap);
    }
}

#[cfg(unix)]
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.first().map_or("reads", String::as_str);
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200);
    // Under /tmp: a Darwin TMPDIR can push a socket path past SUN_LEN; /tmp is on the
    // same APFS volume as a real fabric log.
    let scratch = Scratch::new().expect("exclusive bench dir");
    let sock = scratch.0.join("b.sock");
    let broker = Broker::open(scratch.0.join("b.log")).expect("open");
    let unix = broker.serve(&sock).expect("serve unix");
    match mode {
        "reads" => reads(&broker, &sock, n),
        "behind" => behind(&broker, &sock, n),
        other => eprintln!("unknown mode {other:?}: reads | behind"),
    }
    drop(unix);
    drop(broker);
}
