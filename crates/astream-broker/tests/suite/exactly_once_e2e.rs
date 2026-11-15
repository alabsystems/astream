//! Evidence for `broker.true-exactly-once-e2e`: true end-to-end exactly-once, the
//! Pareto win over Kafka's coordinator-based EOS.
//!
//! 1. DURABLE GROUP COMMITS: a consumer group's committed offset lives on the broker
//!    (not a client cursor) and survives a BROKER restart — resume never re-delivers
//!    a committed record.
//! 2. ATOMIC READ-PROCESS-WRITE: produce the output AND commit the input offset in
//!    ONE durable record (one fsync). A retried transaction is deduped, so the output
//!    appears exactly once and the offset is committed exactly once — even across a
//!    crash mid-transaction. No transaction coordinator.
//!
//! In-process, no sleeps.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{Broker, Client};
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

fn client(sock: &str) -> Client {
    Client::connect(sock).unwrap()
}

#[test]
fn group_commit_is_durable_and_resumes_across_a_broker_restart() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ase_{pid}_g_{n}.log");
    let sock1 = format!("/tmp/ase_{pid}_g1_{n}.sock");
    let sock2 = format!("/tmp/ase_{pid}_g2_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock1, &sock2]);

    // Broker 1: publish m1..m3 (offsets 0,1,2); group G consumes them and commits upto=2.
    {
        let b1 = Broker::open(&log).unwrap();
        let mut h1 = b1.serve(&sock1).unwrap();
        let mut p = client(&sock1);
        for i in 1..=3u64 {
            p.publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
                .unwrap();
        }
        let mut g = client(&sock1).subscribe_group("G", "/a/stream/>").unwrap();
        for _ in 0..3 {
            g.recv().unwrap().unwrap();
        }
        client(&sock1).commit("G", 2).unwrap(); // durable group commit (offset 3 = commit record)
        drop(g);
        drop(p);
        h1.shutdown();
    }

    // Broker 2: reopen the SAME log. The group commit is recovered from disk.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut p2 = client(&sock2);
    p2.publish(1, 4, "/a/stream/x", b"m4").unwrap(); // offset 4 (offset 3 was the commit record)
    p2.publish(1, 5, "/a/stream/x", b"m5").unwrap(); // offset 5

    // G resumes from the durable commit (offset 3) — it gets ONLY m4, m5, never the
    // already-committed m1,m2,m3.
    let mut g = client(&sock2).subscribe_group("G", "/a/stream/>").unwrap();
    let got: Vec<(u64, Vec<u8>)> = (0..2)
        .map(|_| {
            let (o, _s, b) = g.recv().unwrap().unwrap();
            (o, b)
        })
        .collect();
    assert_eq!(
        got[0],
        (4, b"m4".to_vec()),
        "resumed past the committed records"
    );
    assert_eq!(got[1], (5, b"m5".to_vec()));
}

#[test]
fn atomic_read_process_write_is_exactly_once() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ase_{pid}_t_{n}.log");
    let sock = format!("/tmp/ase_{pid}_t_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let _h = b.serve(&sock).unwrap();

    let mut p = client(&sock);
    p.publish(1, 1, "/a/in/x", b"input-0").unwrap(); // input at offset 0

    // Process input offset 0: produce the output AND commit group G to upto=0 atomically.
    let mut worker = client(&sock);
    assert_eq!(
        worker
            .process_and_produce(9, 1, "/a/out/y", b"processed-0", "G", 0)
            .unwrap(),
        (1, false)
    );
    // Retry the SAME transaction (e.g. a crash before the ack): deduped to the
    // original offset — the output is NOT re-appended and the commit is not re-applied.
    assert_eq!(
        worker
            .process_and_produce(9, 1, "/a/out/y", b"processed-0", "G", 0)
            .unwrap(),
        (1, true)
    );

    // The output subject holds EXACTLY ONE processed record: a sentinel published
    // afterward is the NEXT /a/out delivery (would be a 2nd processed-0 if the dup
    // had wrongly appended).
    let mut out = client(&sock).subscribe(0, "/a/out/>").unwrap();
    assert_eq!(
        out.recv().unwrap().unwrap(),
        (1, "/a/out/y".to_string(), b"processed-0".to_vec())
    );
    client(&sock)
        .publish(2, 1, "/a/out/y", b"sentinel")
        .unwrap(); // offset 2
    assert_eq!(
        out.recv().unwrap().unwrap().2,
        b"sentinel",
        "only one processed-0 was appended"
    );

    // The atomic commit took durably: group G resumes past the committed input-0.
    let mut g = client(&sock).subscribe_group("G", "/a/in/>").unwrap();
    client(&sock).publish(3, 1, "/a/in/x", b"input-1").unwrap(); // offset 3
    let (o, _s, body) = g.recv().unwrap().unwrap();
    assert_eq!(
        (o, body),
        (3, b"input-1".to_vec()),
        "G resumed past the committed input-0"
    );
}

/// Regression: pure consumer-group commit records live on the reserved `/a/commit`
/// subject, which a WILDCARD data filter (`/a/>`) matches. They must never be
/// delivered to a data subscriber — they are internal bookkeeping, and an empty-bodied
/// commit record would otherwise corrupt every wildcard consumer's stream.
#[test]
fn commit_records_never_leak_to_wildcard_subscribers() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ase_{pid}_leak_{n}.log");
    let sock = format!("/tmp/ase_{pid}_leak_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let _h = b.serve(&sock).unwrap();

    // A live wildcard subscriber under /a/ — the common NATS-style case.
    let mut sub = client(&sock).subscribe(0, "/a/>").unwrap();

    let mut p = client(&sock);
    p.publish(1, 1, "/a/data/x", b"hello").unwrap(); // offset 0 (data)
    client(&sock).commit("g1", 0).unwrap(); // offset 1 (pure /a/commit record)
    p.publish(1, 2, "/a/data/x", b"world").unwrap(); // offset 2 (data)

    // The subscriber sees ONLY the two data records — the /a/commit record at offset
    // 1 is skipped (filter-independently), so the next delivery after "hello" is
    // "world", NOT (1, "/a/commit", []).
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (0, "/a/data/x".to_string(), b"hello".to_vec())
    );
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (2, "/a/data/x".to_string(), b"world".to_vec()),
        "commit record at offset 1 was NOT delivered to the wildcard subscriber"
    );
}

/// `/a/commit` is the broker-INTERNAL subject of consumer-group commit records. It is a
/// syntactically valid Subject, so it must be refused explicitly: a client record there
/// would bypass exactly-once dedup (the commit-subject exemption) and never be delivered
/// (delivery skips the subject) — a publish acked "new" at a fresh offset on every
/// retry, invisible to every subscriber. Refused as a publish, as a read-process-write
/// output, and as a fork replacement, with nothing appended and the idempotency key
/// left unconsumed; consumer-group commits go through Commit / ProcessAndProduce.
#[test]
fn the_reserved_commit_subject_cannot_be_published_to() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ase_{pid}_reserved_{n}.log");
    let sock = format!("/tmp/ase_{pid}_reserved_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let _h = b.serve(&sock).unwrap();

    let mut p = client(&sock);
    for attempt in 0..2 {
        let err = p.publish(5, 1, "/a/commit", b"x").unwrap_err();
        assert!(
            err.to_string().contains("reserved subject"),
            "attempt {attempt}: {err}"
        );
    }
    let err = p
        .process_and_produce(5, 2, "/a/commit", b"x", "G", 0)
        .unwrap_err();
    assert!(err.to_string().contains("reserved subject"), "{err}");
    let mut fork = client(&sock)
        .fork_subscribe(0, "/a/commit", b"x", "/a/>")
        .unwrap();
    let err = fork.recv().unwrap_err();
    assert!(err.to_string().contains("reserved subject"), "{err}");
    assert_eq!(b.head(), 0, "nothing was appended");

    // The refused key was never consumed: a legitimate publish under it is a first
    // send, and a real commit still lands on the reserved subject as a commit record.
    assert_eq!(p.publish(5, 1, "/a/stream/x", b"real").unwrap(), (0, false));
    assert_eq!(p.commit("G", 0).unwrap(), 1);
    assert_eq!(b.head(), 2);
}
