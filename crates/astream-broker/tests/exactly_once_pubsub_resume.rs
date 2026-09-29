//! Evidence for `broker.exactly-once-pubsub-resume`: the servable broker delivers
//! ordered, exactly-once-ingest pub/sub over a Unix socket with Filter routing,
//! resume-from-offset across a consumer crash, deterministic replay-from-0, and
//! restart durability. Fully in-process + std-only; NO sleeps — every step
//! synchronizes on data (a publish blocks for its ack; a subscriber blocks for an
//! exact, known number of deliveries), so assertions are interleaving-invariant.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{Broker, BrokerHandle, Client};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
        Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
    }
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            remove_with_sidecars(path);
        }
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

/// Fresh broker on unique short paths (/tmp keeps the socket under the 104-byte
/// sun_path limit). Returns the paths' cleanup guard, the broker, its handle, the
/// socket path, and the log path.
fn fresh(tag: &str) -> (Cleanup, Broker, BrokerHandle, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/asb_{pid}_{tag}_{n}.sock");
    let log = format!("/tmp/asb_{pid}_{tag}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock, log)
}

fn client(sock: &str) -> Client {
    Client::connect(sock).unwrap()
}

#[test]
fn ordered_exactly_once_pubsub_with_filter_routing() {
    let (_tmp, _b, _h, sock, _log) = fresh("pubsub");
    let mut p = client(&sock);
    // Five messages to /a/stream/x (offsets 0..4), one to /a/queue/y (offset 5).
    for i in 1..=5u64 {
        let (off, dup) = p
            .publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false), "dense, non-dedup offsets");
    }
    assert_eq!(p.publish(1, 6, "/a/queue/y", b"q").unwrap(), (5, false));

    // Subscribe /a/stream/> from 0: exactly the five stream records, in order; the
    // /a/queue/y record (offset 5) is filtered out.
    let mut sub = client(&sock).subscribe(0, "/a/stream/>").unwrap();
    let mut got = Vec::new();
    for _ in 0..5 {
        let (off, subj, body) = sub.recv().unwrap().unwrap();
        got.push((off, subj, body));
    }
    assert_eq!(
        got.iter().map(|(o, ..)| *o).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4],
        "ordered, queue/y filtered out"
    );
    assert_eq!(got[2].2, b"m3");
}

#[test]
fn dedup_is_exactly_once_into_the_log() {
    let (_tmp, _b, _h, sock, _log) = fresh("dedup");
    let mut p = client(&sock);
    assert_eq!(p.publish(7, 1, "/a/stream/x", b"a").unwrap(), (0, false));
    assert_eq!(p.publish(7, 2, "/a/stream/x", b"b").unwrap(), (1, false));
    assert_eq!(p.publish(7, 3, "/a/stream/x", b"c").unwrap(), (2, false));
    // Re-send (7,2): original offset, deduped, NOT re-appended.
    assert_eq!(p.publish(7, 2, "/a/stream/x", b"b").unwrap(), (1, true));

    // The log still has exactly three records (the dup added nothing).
    let mut sub = client(&sock).subscribe(0, "/a/>").unwrap();
    let offs: Vec<u64> = (0..3).map(|_| sub.recv().unwrap().unwrap().0).collect();
    assert_eq!(offs, vec![0, 1, 2]);
}

#[test]
fn consumer_crash_then_resume_is_gapless_no_dup() {
    let (_tmp, _b, _h, sock, _log) = fresh("resume");
    let mut p = client(&sock);
    for i in 1..=3u64 {
        p.publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
    }
    // Consumer A reads 0,1,2 then CRASHES (drops the connection).
    let mut a = client(&sock).subscribe(0, "/a/stream/>").unwrap();
    let mut seen = Vec::new();
    for _ in 0..3 {
        seen.push(a.recv().unwrap().unwrap().0);
    }
    assert_eq!(seen, vec![0, 1, 2]);
    drop(a); // crash

    // More messages while no consumer is attached.
    p.publish(1, 4, "/a/stream/x", b"m4").unwrap();
    p.publish(1, 5, "/a/stream/x", b"m5").unwrap();

    // Consumer B resumes from last_committed+1 = 3: gets EXACTLY 3,4 — 0,1,2 not
    // re-sent, 3,4 not lost.
    let mut b = client(&sock).subscribe(3, "/a/stream/>").unwrap();
    let resumed: Vec<u64> = (0..2).map(|_| b.recv().unwrap().unwrap().0).collect();
    assert_eq!(resumed, vec![3, 4], "gapless resume, no dup");
}

#[test]
fn replay_from_zero_is_deterministic() {
    let (_tmp, _b, _h, sock, _log) = fresh("replay");
    let mut p = client(&sock);
    for i in 1..=5u64 {
        p.publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
    }
    let replay = |sock: &str| -> Vec<(u64, String, Vec<u8>)> {
        let mut s = client(sock).subscribe(0, "/a/>").unwrap();
        (0..5).map(|_| s.recv().unwrap().unwrap()).collect()
    };
    assert_eq!(
        replay(&sock),
        replay(&sock),
        "two replays from 0 are byte-identical"
    );
}

#[test]
fn live_tail_wakes_on_publish_not_poll() {
    let (_tmp, _b, _h, sock, _log) = fresh("tail");
    let mut p = client(&sock);
    p.publish(1, 1, "/a/stream/x", b"s").unwrap(); // offset 0, non-matching for the sub below

    // Subscribe to /a/queue/> — catch-up matches nothing, so the subscriber PARKS.
    let mut sub = client(&sock).subscribe(0, "/a/queue/>").unwrap();
    // Now publish a matching record; the parked subscriber must WAKE (Condvar) and
    // deliver it. recv blocks until it arrives — proving a notify, not a poll.
    p.publish(1, 2, "/a/queue/z", b"qz").unwrap(); // offset 1
    let (off, subj, body) = sub.recv().unwrap().unwrap();
    assert_eq!(
        (off, subj.as_str(), body.as_slice()),
        (1, "/a/queue/z", b"qz".as_slice())
    );
}

#[test]
fn dead_non_matching_subscriber_does_not_break_the_broker() {
    let (_tmp, _b, _h, sock, _log) = fresh("deadsub");
    // A subscriber to a subject that is never published: it parks immediately (no
    // catch-up match), then the client vanishes — the exact parked-subscriber leak
    // scenario. The broker must reap it and stay fully functional.
    let dead = client(&sock).subscribe(0, "/a/never/>").unwrap();
    drop(dead);
    // The bus still works: publish + a fresh matching subscriber receives it.
    let mut p = client(&sock);
    p.publish(1, 1, "/a/stream/x", b"ok").unwrap();
    let mut sub = client(&sock).subscribe(0, "/a/stream/>").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"ok");
}

#[test]
fn survives_broker_restart() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asb_{pid}_restart_{n}.log");
    let sock1 = format!("/tmp/asb_{pid}_restart1_{n}.sock");
    let sock2 = format!("/tmp/asb_{pid}_restart2_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock1, &sock2]);

    // Broker 1: publish five (producer 7, seqs 1..=5), then shut down.
    {
        let b1 = Broker::open(&log).unwrap();
        let mut h1 = b1.serve(&sock1).unwrap();
        let mut p = client(&sock1);
        for i in 1..=5u64 {
            p.publish(7, i, "/a/stream/x", format!("m{i}").as_bytes())
                .unwrap();
        }
        drop(p); // let the producer conn thread exit
        h1.shutdown();
    }

    // Broker 2: reopen the SAME log. Everything fsync-acked is recovered.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut sub = client(&sock2).subscribe(0, "/a/>").unwrap();
    let got: Vec<(u64, Vec<u8>)> = (0..5)
        .map(|_| {
            let (o, _s, b) = sub.recv().unwrap().unwrap();
            (o, b)
        })
        .collect();
    assert_eq!(
        got.iter().map(|(o, _)| *o).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4],
        "history recovered"
    );
    assert_eq!(got[2].1, b"m3");

    // Dedup map recovered too: re-sending (7,3) dedups to its original offset 2.
    let mut p2 = client(&sock2);
    assert_eq!(
        p2.publish(7, 3, "/a/stream/x", b"m3").unwrap(),
        (2, true),
        "dedup survived restart"
    );
}

/// A `Broker` that is opened but never served (the shape of `serve` failing and the
/// error propagating) owns its writer thread: dropping it stops and joins the writer
/// and releases the log's exclusive lock, so nothing leaks and the log is reopenable at
/// once. If the writer did not exit, the drop would hang here.
#[test]
fn dropping_an_unserved_broker_stops_its_writer_and_releases_the_log() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asb_{pid}_unserved_{n}.log");
    let sock = format!("/tmp/asb_{pid}_unserved_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    let b = Broker::open(&log).unwrap();
    // Exclusively locked while open: a second broker on the same log is refused.
    let err = Broker::open(&log)
        .err()
        .expect("a second broker on an open log");
    assert_eq!(err.kind(), std::io::ErrorKind::AlreadyExists, "{err}");
    drop(b);
    // Reopenable immediately: the writer is gone and the lock released.
    let b2 = Broker::open(&log).unwrap();
    let _h = b2.serve(&sock).unwrap();
    assert_eq!(
        client(&sock).publish(1, 1, "/a/stream/x", b"m1").unwrap(),
        (0, false)
    );
}

/// `serve` never displaces a LIVE broker: a socket path a broker answers on is
/// `AddrInUse` (the first broker keeps serving); a leftover socket FILE nobody answers
/// on — what a crashed broker leaves behind — is unlinked and taken over.
#[test]
fn serve_refuses_a_live_socket_and_takes_over_a_stale_one() {
    let (_tmp, b, mut h, sock, log) = fresh("live");
    let log2 = format!("{log}.2");
    let _ = std::fs::remove_file(&log2);
    let b2 = Broker::open(&log2).unwrap();
    let err = b2
        .serve(&sock)
        .err()
        .expect("must not displace a live broker");
    assert_eq!(err.kind(), std::io::ErrorKind::AddrInUse, "{err}");
    assert_eq!(
        client(&sock).publish(1, 1, "/a/stream/x", b"m1").unwrap(),
        (0, false),
        "the live broker was not disturbed"
    );
    h.shutdown();
    drop(b);
    // A stale socket file: bound once, nobody listening any more.
    drop(std::os::unix::net::UnixListener::bind(&sock).unwrap());
    assert!(std::path::Path::new(&sock).exists());
    let _h2 = b2.serve(&sock).unwrap();
    assert_eq!(
        client(&sock).publish(1, 1, "/a/stream/x", b"m1").unwrap(),
        (0, false),
        "the stale socket was taken over"
    );
}
