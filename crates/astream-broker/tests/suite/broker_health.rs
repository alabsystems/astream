// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.hello-health` and `broker.health-sidecar`: a broker says, from
//! itself, whether its log is POISONED and what its flushes did — in-band, in the answer
//! to every `Hello` (the extension block's tag 0x04, `Client::broker_health`), and on
//! disk, in `<log>.health`, which another process reads with `read_health` and is told
//! whether the broker that wrote it still serves the log.
//!
//! The sequence the facts must follow is the one a failing disk walks a log through:
//! healthy, then a full flush fails (`InjectedFaults::sync`), then the log is poisoned,
//! served Strict (`LatchedAfterFlushFailure`), and has counted one failed flush. Its
//! negative control is the write that merely FAILED: a Strict batch rolled back counts a
//! failed flush and poisons nothing, and both faces say exactly that.
//!
//! What is asserted is what the broker decides and answers, over a real socket and real
//! files. The fault seam stands in for the device.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{
    read_health, Broker, Client, Durability, Escalate, Escalation, HealthWriter, InjectedFaults,
    OpenOptions, Prepared, ServedReason, Tier,
};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A period no test waits out: what the sidecar shows was written at the open, at the
/// poison, by `write_health`, or at the close — never by the period.
const NEVER: Duration = Duration::from_secs(3600);

/// A one-minute HANG DETECTOR for something that must happen, never a latency budget.
const MINUTE: Duration = Duration::from_secs(60);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it.
struct Cleanup(Vec<String>);

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let path = std::path::Path::new(path);
            let _ = std::fs::remove_file(path);
            let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
                continue;
            };
            let prefix = format!("{}.", name.to_string_lossy());
            for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                if entry.file_name().to_string_lossy().starts_with(&prefix) {
                    let _ = std::fs::remove_file(entry.path());
                }
            }
        }
    }
}

/// A fresh log and socket path, and their cleanup.
fn paths(tag: &str) -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ashl_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/ashl_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// Wait until `cond` holds, under the hang detector.
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + MINUTE;
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::yield_now();
    }
}

/// The sidecar beside `log`, which must be there.
fn sidecar(log: &str) -> astream_broker::HealthRead {
    read_health(log).unwrap().expect("a health sidecar")
}

/// HEALTHY, THEN A FULL FLUSH FAILS: the log is poisoned, served Strict, one flush
/// failed — said by both faces, which agree with the broker's own reads. On Relaxed
/// with `/e/>` escalated (the table holds an escalated record for its full flush on
/// every platform), the sidecar kept on an hour's period:
///
/// - healthy: `Hello` carries the entry, no poison and no failed flush, the tier served
///   Relaxed; the sidecar the open wrote reads the same, written by this process and
///   `Serving`;
/// - `inject_faults` sync, an escalated publish: refused, and the log POISONED;
/// - the sidecar names the poison WITHOUT its period — the poison itself wakes the
///   writer — with `served = Strict` (`LatchedAfterFlushFailure`) and `flush_failed = 1`;
///   a fresh `Hello` says the same, the reason word for word the broker's;
/// - the stop writes the last snapshot and lets it go: `Gone`, the poison its last word;
///   a stopped broker publishes nothing more;
/// - the reopen (the cure) is healthy again on both faces, its counts back at zero.
#[test]
fn both_faces_say_healthy_then_poisoned_served_strict_and_one_failed_flush() {
    let (_tmp, log, sock) = paths("seq");
    let open = || {
        let mut o = OpenOptions::new(Durability::Relaxed);
        o.escalation = Escalation::new([Escalate::Subject("/e/>".into())]);
        o.health_every = Some(NEVER);
        Broker::open_opts(&log, o, || Ok(Prepared::Nothing)).unwrap()
    };
    let b = open();
    let mut h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"before").unwrap();

    c.hello().unwrap();
    let told = c.broker_health().cloned().expect("the entry rides Hello");
    assert_eq!(told.poisoned, None, "healthy");
    assert_eq!(told.flushes.failed, 0);
    assert_eq!(
        told.flushes,
        b.flush_counts(),
        "Hello tells the broker's counts"
    );
    assert_eq!(c.served_durability().map(|s| s.served), Some(Tier::Relaxed));
    let read = sidecar(&log);
    assert_eq!(read.writer, HealthWriter::Serving);
    assert_eq!(read.health.pid, std::process::id());
    assert_eq!(read.health.identity, b.log_identity());
    assert_eq!(read.health.poisoned, None);
    assert_eq!(read.health.flushes.failed, 0);
    assert_eq!(read.health.served.served, Tier::Relaxed);

    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    c.publish(1, 2, "/e/a", b"a person's word").unwrap_err();
    b.inject_faults(InjectedFaults::default());
    let why = b
        .poisoned()
        .expect("the failed full flush poisoned the open");

    until(
        "the sidecar names the poison, an hour before its period",
        || sidecar(&log).health.poisoned.is_some(),
    );
    let read = sidecar(&log);
    assert_eq!(read.writer, HealthWriter::Serving);
    assert_eq!(read.health.poisoned.as_deref(), Some(why.as_str()));
    assert_eq!(
        (read.health.served.served, read.health.served.reason),
        (Tier::Strict, ServedReason::LatchedAfterFlushFailure),
        "served Strict"
    );
    assert_eq!(read.health.served.requested, Tier::Relaxed);
    assert_eq!(read.health.flushes.failed, 1, "failed = 1");

    c.hello().unwrap();
    let told = c.broker_health().cloned().unwrap();
    assert_eq!(told.poisoned.as_deref(), Some(why.as_str()));
    assert_eq!(told.flushes.failed, 1);
    assert_eq!(
        c.served_durability().map(|s| (s.served, s.reason)),
        Some((Tier::Strict, ServedReason::LatchedAfterFlushFailure))
    );

    h.shutdown();
    let read = sidecar(&log);
    assert_eq!(read.writer, HealthWriter::Gone, "the stop let it go");
    assert_eq!(read.health.poisoned.as_deref(), Some(why.as_str()));
    assert!(
        b.write_health().is_err(),
        "a stopped broker publishes nothing"
    );
    assert_eq!(sidecar(&log).writer, HealthWriter::Gone);
    drop(b);

    let b = open();
    let _h = b.serve(&sock).unwrap();
    let read = sidecar(&log);
    assert_eq!(
        (
            read.writer,
            read.health.poisoned,
            read.health.flushes.failed
        ),
        (HealthWriter::Serving, None, 0),
        "the reopen is healthy"
    );
    let mut c = Client::connect(&sock).unwrap();
    c.hello().unwrap();
    assert_eq!(c.broker_health().unwrap().poisoned, None);
}

/// NEGATIVE CONTROL: a write that merely FAILED. A Strict batch whose flush fails is
/// rolled back with every earlier record covered, so the log counts the failed flush
/// and is NOT poisoned: `Hello` and the sidecar both say `failed = 1` and no poison,
/// the tier served is still the Strict asked for, and the same connection's next write
/// lands. A face that read "a flush failed" as "poisoned" fails here.
#[test]
fn a_rolled_back_write_counts_a_failed_flush_and_poisons_nothing() {
    let (_tmp, log, sock) = paths("rolled");
    let mut o = OpenOptions::new(Durability::Strict);
    o.health_every = Some(NEVER);
    let b = Broker::open_opts(&log, o, || Ok(Prepared::Nothing)).unwrap();
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"before").unwrap();
    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    c.publish(1, 2, "/o/a", b"rolled back").unwrap_err();
    b.inject_faults(InjectedFaults::default());
    assert_eq!(b.poisoned(), None);

    c.hello().unwrap();
    let told = c.broker_health().cloned().unwrap();
    assert_eq!((told.poisoned, told.flushes.failed), (None, 1));
    b.write_health().unwrap();
    let read = sidecar(&log);
    assert_eq!(read.writer, HealthWriter::Serving);
    assert_eq!(
        (read.health.poisoned, read.health.flushes.failed),
        (None, 1)
    );
    assert_eq!(
        (read.health.served.served, read.health.served.reason),
        (Tier::Strict, ServedReason::None)
    );
    c.publish(1, 2, "/o/a", b"rolled back").unwrap();
}

/// THE SIDECAR'S COUNTS ARE THE BROKER'S: retained records, subjects, a pending will,
/// a group commit, an open connection and a parked tail, the heads — what
/// `Broker::health` takes, `write_health` publishes and another reader reads back.
#[test]
fn the_sidecar_carries_what_the_log_holds_and_who_is_attached() {
    let (_tmp, log, sock) = paths("counts");
    let b = Broker::open(&log).unwrap();
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"one").unwrap();
    c.publish(1, 2, "/o/b", b"two").unwrap();
    c.commit("/g/one", 1).unwrap();
    c.will(9, 1, "/w/gone", b"bye").unwrap();
    let _tail = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/nothing/>")
        .unwrap();
    until("the tail parks", || b.stats().parked_tails == 1);

    let want = b.health();
    let (before, times_before) = (astream_sys::flush_tally(), astream_sys::flush_times());
    b.write_health().unwrap();
    let (after, times_after) = (astream_sys::flush_tally(), astream_sys::flush_times());
    let read = sidecar(&log);
    // The process's flush times the same way: each kind's total no less than before the
    // write and no more than after it, on this build's clock, the slow count with them, and
    // every slow flush it names one this process's ring held. The Strict publishes above
    // took time in full flushes, so a snapshot whose times were not the process's (none,
    // or zeros) fails here.
    let times = read
        .health
        .process_flush_times
        .clone()
        .expect("a sidecar this build's broker wrote carries its process's flush times");
    assert_eq!(times.clock, astream_sys::FLUSH_CLOCK);
    assert!(times_before.full_ns > 0, "{times_before:?}");
    for kind in astream_sys::FlushKind::ALL {
        let (low, got, high) = (
            times_before.total_ns(kind),
            times.total_ns(kind),
            times_after.total_ns(kind),
        );
        assert!(
            (low..=high).contains(&got),
            "the sidecar's {} time {got} ns, outside this process's {low}..={high}",
            kind.word()
        );
    }
    assert!(
        (times_before.slow_count..=times_after.slow_count).contains(&times.slow_count),
        "{times:?}"
    );
    assert!(
        times
            .slow
            .iter()
            .all(|f| times_before.slow.contains(f) || times_after.slow.contains(f)),
        "a slow flush this process's ring never held: {times:?}"
    );
    // The process's tally as the write took it: no fewer flushes of any kind than this
    // process had asked for before the write, no more than after it. The Strict
    // publishes above flushed in full, so a snapshot that carried no tally fails here.
    let tally = read
        .health
        .process_flushes
        .expect("a sidecar this build's broker wrote carries its process's tally");
    assert!(
        before.full > 0,
        "the Strict publishes flushed in full: {before:?}"
    );
    for (kind, low, got, high) in [
        ("full", before.full, tally.full, after.full),
        ("barrier", before.barrier, tally.barrier, after.barrier),
        ("plain", before.plain, tally.plain, after.plain),
    ] {
        assert!(
            (low..=high).contains(&got),
            "the sidecar's {kind} flushes {got}, outside this process's {low}..={high}"
        );
    }
    assert_eq!(read.writer, HealthWriter::Serving);
    let got = read.health;
    assert_eq!(got.retained_records, 4, "two publishes, a commit, a will");
    assert_eq!(got.distinct_subjects, 2);
    assert_eq!(got.pending_wills, 1);
    assert_eq!(got.group_commits, 1);
    assert_eq!(got.active_conns, 2);
    assert_eq!(got.parked_tails, 1);
    assert_eq!((got.head, got.visible_head, got.durable_head), (4, 4, 4));
    assert_eq!(got.retained_records, want.retained_records);
    assert_eq!(got.retained_bytes, want.retained_bytes);
    assert!(got.retained_bytes > 0);
    // With no residency budget every retained record is resident, and the sidecar says so.
    let resident = got
        .resident
        .expect("a sidecar this build's broker wrote carries its residency");
    assert_eq!(
        resident.records, 4,
        "no budget: every retained record resident"
    );
    assert!(resident.bytes > 0);
    assert_eq!(got.resident, want.resident);
    // NEGATIVE CONTROL: under a zero budget the log keeps only its newest record decoded,
    // and the next snapshot carries that, the retained count unmoved.
    b.set_resident_budget(0);
    b.write_health().unwrap();
    let bounded = sidecar(&log).health;
    assert_eq!(bounded.retained_records, 4);
    let resident = bounded.resident.expect("its residency");
    assert_eq!(
        resident.records, 1,
        "a zero budget keeps the newest record alone"
    );
    assert!(resident.bytes > 0);
    assert_eq!(
        b.residency(),
        (1, usize::try_from(resident.bytes).unwrap(), 4),
        "the broker's own residency"
    );
}

/// THE LAST WORD IS THE LOG'S FINAL STATE. A Relaxed broker's records ride the page
/// cache (the durable head stays 0) until its clean stop flushes them: the stop closes
/// the log FIRST, then writes the last snapshot and lets it go, so the `Gone` sidecar
/// says every record is durable — what the reopen finds. Before, the last word was
/// taken before the close and told `durable_head = 0` of three records the close had
/// flushed. NEGATIVE CONTROL: the snapshot written while it served says
/// `durable_head = 0`, so a stop that wrote no last word, or wrote it before the close,
/// leaves exactly that and fails here.
#[test]
fn the_stop_writes_its_last_word_after_the_log_closes() {
    let (_tmp, log, sock) = paths("last");
    let mut o = OpenOptions::new(Durability::Relaxed);
    o.health_every = Some(NEVER);
    let b = Broker::open_opts(&log, o, || Ok(Prepared::Nothing)).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    for seq in 1..=3 {
        c.publish(1, seq, "/o/a", b"page cache").unwrap();
    }
    b.write_health().unwrap();
    let serving = sidecar(&log);
    assert_eq!(
        (
            serving.writer,
            serving.health.head,
            serving.health.durable_head
        ),
        (HealthWriter::Serving, 3, 0),
        "Relaxed: nothing is durable while it serves"
    );
    drop(c);
    h.shutdown();
    let last = sidecar(&log);
    assert_eq!(
        (last.writer, last.health.head, last.health.durable_head),
        (HealthWriter::Gone, 3, 3),
        "the clean close made every record durable, and the last word says so"
    );
    assert_eq!(last.health.poisoned, None);
    drop(b);
    assert_eq!(
        Broker::open(&log).unwrap().head(),
        3,
        "the reopen finds all three"
    );
}
