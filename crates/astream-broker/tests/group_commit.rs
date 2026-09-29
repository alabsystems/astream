//! Evidence for `broker.group-commit-durability`: the batched (group-commit) write
//! path preserves Strict durability + exactly-once ingest UNDER CONCURRENCY. Many
//! producers publish at once and the broker's single writer thread folds their appends
//! into shared fsyncs (one fsync amortized over a whole batch), yet every acked record
//! is durable, distinct, gap-free, deduplicated, and survives a broker restart.
//!
//! This is the throughput mechanism that lets astream scale past fsync-per-message
//! while keeping the SAME guarantee (ack ⟹ fsync'd). No sleeps — every step
//! synchronizes on the durable ack or a delivery. The failure side of the contract —
//! a failed batch fsync rolls the batch back and tells every op — is witnessed below
//! through the log's documented fault-injection seam.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{Broker, BrokerLog, Client, InjectedFaults};
use std::collections::HashSet;
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

#[test]
fn concurrent_producers_are_durable_distinct_and_exactly_once() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asgc_t_{pid}_{n}.log");
    let sock = format!("/tmp/asgc_t_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    const PRODUCERS: u64 = 16;
    const PER: u64 = 50;
    let total = (PRODUCERS * PER) as usize;

    {
        let b = Broker::open(&log).unwrap();
        let _h = b.serve(&sock).unwrap();

        // Many producers publish concurrently; their appends share group-commit fsyncs.
        let handles: Vec<_> = (0..PRODUCERS)
            .map(|p| {
                let sock = sock.clone();
                std::thread::spawn(move || {
                    let mut c = Client::connect(&sock).unwrap();
                    let producer_id = p + 1; // a distinct exactly-once identity per thread
                    let mut offsets = Vec::with_capacity(PER as usize);
                    for i in 1..=PER {
                        let body = format!("p{p}-{i}");
                        let (off, deduped) = c
                            .publish(producer_id, i, "/a/gc/x", body.as_bytes())
                            .unwrap();
                        assert!(!deduped, "a first send is never a duplicate");
                        offsets.push(off);
                        // Re-send the SAME (producer_id, seq) with a different body:
                        // exactly-once ingest must return the ORIGINAL offset, deduped,
                        // and append nothing — even under concurrent batching.
                        let (off2, deduped2) = c
                            .publish(producer_id, i, "/a/gc/x", b"ignored-dup")
                            .unwrap();
                        assert_eq!(
                            (off2, deduped2),
                            (off, true),
                            "dedup returns the original offset and appends nothing"
                        );
                    }
                    offsets
                })
            })
            .collect();

        let mut all: Vec<u64> = Vec::with_capacity(total);
        for h in handles {
            all.extend(h.join().unwrap());
        }

        // Every acked offset is distinct, and there are exactly PRODUCERS*PER of them
        // over a gap-free [0, total) spine — nothing lost, nothing double-appended,
        // despite the concurrent group-committed appends.
        assert_eq!(all.len(), total, "every first send was acked");
        let distinct: HashSet<u64> = all.iter().copied().collect();
        assert_eq!(distinct.len(), total, "all acked offsets are distinct");
        assert_eq!(
            *distinct.iter().max().unwrap(),
            (total - 1) as u64,
            "offset spine is dense [0, total)"
        );
    } // drop the handle → shutdown (joins the writer thread, last batch flushed)

    // Reopen the SAME log: every durable record survived the batched fsyncs + restart.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/gc/>")
        .unwrap();
    let mut seen: HashSet<u64> = HashSet::new();
    for _ in 0..total {
        let (off, _s, _body) = sub.recv().unwrap().unwrap();
        assert!(seen.insert(off), "no duplicate delivery on replay");
    }
    assert_eq!(
        seen.len(),
        total,
        "all {total} concurrently-published records recovered after restart"
    );
}

/// The failed-fsync path, witnessed through the log's documented fault-injection seam
/// (`InjectedFaults`; integration tests cannot make a real disk fail): while the fsync
/// fails, EVERY op in EVERY batch — a pipelined batch of four publishes, a single
/// publish, a pure commit — is told it is NOT durable ("commit failed"), nothing is
/// promoted (the head does not move, a live subscriber never sees the records), and the
/// file is rolled back to the durable prefix. Once the fault clears, the same keys are
/// appended ANEW at the next offset — not deduped, so no phantom dedup entry survived
/// the rollback — and a reopen recovers exactly the durable records.
#[test]
fn failed_fsync_rolls_the_batch_back_and_tells_every_op() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asgc_ff_{pid}_{n}.log");
    let sock = format!("/tmp/asgc_ff_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut p = Client::connect(&sock).unwrap();
    for i in 1..=3u64 {
        assert_eq!(
            p.publish(1, i, "/a/gc/x", format!("d{i}").as_bytes())
                .unwrap(),
            (i - 1, false)
        );
    }
    let durable_len = std::fs::metadata(&log).unwrap().len();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/gc/>")
        .unwrap();
    for i in 0..3 {
        assert_eq!(sub.recv().unwrap().unwrap().0, i);
    }

    b.inject_faults(InjectedFaults {
        sync: true,
        truncate: false,
    });
    // A pipelined batch on one connection: every op in it is refused.
    let mut q = Client::connect(&sock).unwrap();
    for s in 1..=4u64 {
        q.send_publish(2, s, "/a/gc/x", b"lost").unwrap();
    }
    for s in 1..=4u64 {
        let err = q.recv_publish_ack().unwrap_err();
        assert!(
            err.to_string().contains("commit failed"),
            "pipelined op {s} was not told it is not durable: {err}"
        );
    }
    let err = p.publish(1, 4, "/a/gc/x", b"lost").unwrap_err();
    assert!(err.to_string().contains("commit failed"), "{err}");
    let err = Client::connect(&sock).unwrap().commit("G", 1).unwrap_err();
    assert!(err.to_string().contains("commit failed"), "{err}");
    assert_eq!(b.head(), 3, "nothing promoted while the fsync fails");
    assert_eq!(
        std::fs::metadata(&log).unwrap().len(),
        durable_len,
        "the staged suffix was rolled back off the file"
    );

    b.inject_faults(InjectedFaults::default());
    // The failed keys were never entered into dedup: they append anew, at the next
    // offsets, as first sends.
    assert_eq!(p.publish(1, 4, "/a/gc/x", b"retry").unwrap(), (3, false));
    assert_eq!(q.publish(2, 1, "/a/gc/x", b"retry2").unwrap(), (4, false));
    // The subscriber never saw the rolled-back records: its next deliveries are the
    // retries at 3 and 4.
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (3, "/a/gc/x".to_string(), b"retry".to_vec())
    );
    assert_eq!(sub.recv().unwrap().unwrap().0, 4);
    drop(sub);
    drop(p);
    drop(q);
    h.shutdown();

    // Reopen: exactly the five durable records, none of the rolled-back ones.
    let recovered = BrokerLog::open(&log).unwrap();
    assert_eq!(recovered.head().0, 5);
    let bodies: Vec<Vec<u8>> = recovered
        .read_from(astream_wire::Offset::ZERO)
        .iter()
        .map(|r| r.body.clone())
        .collect();
    assert_eq!(
        bodies,
        vec![
            b"d1".to_vec(),
            b"d2".to_vec(),
            b"d3".to_vec(),
            b"retry".to_vec(),
            b"retry2".to_vec()
        ]
    );
    drop(recovered);
}

/// If the rollback truncate itself fails after a failed fsync, the on-disk suffix is
/// unknown, so the log POISONS itself: every later op is refused ("log poisoned") until
/// the log is reopened — it never appends records with the same offsets after an
/// orphaned suffix (which recovery would then resurrect in place of acked data).
#[test]
fn failed_rollback_poisons_the_log_until_reopen() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asgc_poison_{pid}_{n}.log");
    let sock = format!("/tmp/asgc_poison_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut p = Client::connect(&sock).unwrap();
    assert_eq!(p.publish(1, 1, "/a/gc/x", b"d1").unwrap(), (0, false));
    b.inject_faults(InjectedFaults {
        sync: true,
        truncate: true,
    });
    let err = p.publish(1, 2, "/a/gc/x", b"orphan").unwrap_err();
    assert!(err.to_string().contains("commit failed"), "{err}");
    b.inject_faults(InjectedFaults::default());
    // Faults cleared, but the log stays poisoned: refused, not appended.
    let err = p.publish(1, 3, "/a/gc/x", b"after").unwrap_err();
    assert!(err.to_string().contains("poisoned"), "{err}");
    let err = Client::connect(&sock).unwrap().commit("G", 0).unwrap_err();
    assert!(err.to_string().contains("poisoned"), "{err}");
    assert_eq!(b.head(), 1);
    drop(p);
    h.shutdown();

    // Reopen re-establishes the prefix from what is actually on disk; the log serves again.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock).unwrap();
    let head = b2.head();
    assert!(
        head == 1 || head == 2,
        "durable prefix, plus at most the orphaned frame"
    );
    let (off, dup) = Client::connect(&sock)
        .unwrap()
        .publish(1, 9, "/a/gc/x", b"again")
        .unwrap();
    assert_eq!(
        (off, dup),
        (head, false),
        "the reopened log appends past its prefix"
    );
}
