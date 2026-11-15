// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.poisoned-refusal`: a POISONED log says so, to the embedder and
//! to every producer, in words astream owns.
//!
//! A log poisons itself when a full flush fails with acked or held records no full flush
//! covers (on the weaker tiers, `InjectedFaults::sync` failing an escalated record's
//! flush) or when a rollback cannot put the file back (`sync` and `truncate` together,
//! on any tier). From then on it refuses every write until it is REOPENED, and only the
//! embedder can reopen it. So the embedder must be able to see it (`Broker::poisoned`,
//! with the reason), and a producer must be able to tell that refusal from a write that
//! merely failed (`BrokerRefusal::is_poisoned`): it is code 5 like any transient
//! refusal, and a producer that retries it on the same connection waits for ever.
//!
//! What is asserted is what the broker decides and answers, over a real socket and real
//! files. The fault seam stands in for the device.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{
    broker_refusal, Broker, BrokerRefusal, Client, Durability, Escalate, Escalation,
    InjectedFaults, OpenOptions, Prepared,
};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it, so a
/// test leaves nothing behind whether it passes or panics. Bound before whatever uses
/// the paths, so it drops after that.
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
    let log = format!("/tmp/aspsn_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/aspsn_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// A Relaxed broker whose table escalates `/e/>`: Relaxed holds an escalated record for
/// its full flush on every platform, so a failed flush poisons the open everywhere.
fn open_relaxed(log: &str) -> Broker {
    let mut o = OpenOptions::new(Durability::Relaxed);
    o.escalation = Escalation::new([Escalate::Subject("/e/>".into())]);
    Broker::open_opts(log, o, || Ok(Prepared::Nothing)).unwrap()
}

/// The broker refusal `e` carries.
fn refusal(e: &std::io::Error) -> &BrokerRefusal {
    broker_refusal(e).unwrap_or_else(|| panic!("not a broker refusal: {e}"))
}

/// Wait until `cond` holds — a one-minute HANG DETECTOR for something that must happen,
/// never a latency budget.
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(60);
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::yield_now();
    }
}

/// A full flush that fails POISONS the open, and from then on: the embedder reads why
/// (`Broker::poisoned`); EVERY op of a batch on the poisoned log — not only the first —
/// is refused `is_poisoned`, whichever connection sent it; so is the embedder's own
/// `flush_durable`. The op whose flush poisoned the log is answered with what happened
/// to IT (outcome unknown, resend) and is not `is_poisoned`. Before the failure nothing
/// says poisoned. After the reopen that resend lands exactly once — it dedups to the
/// record the failed flush held back — while another body under the same key dedups
/// too and a fresh seq appends (the negative control).
///
/// Two ops in ONE batch, race-free: the writer is parked inside a batch
/// (`pause_next_batch`, the log lock held) while two connections each register a will,
/// a WAITED write that `writer_round_trips` counts before the connection thread hands
/// it to the writer — so once the count has moved by two, both are queued behind the
/// parked batch and the writer takes them together. A broker that answered only the
/// first op of a batch with the poisoned words told the second "batch aborted (prior
/// append I/O error)", which this test refuses.
#[test]
fn every_write_a_poisoned_log_refuses_says_so_and_the_broker_names_why() {
    let (_tmp, log, sock) = paths("flush");
    let b = open_relaxed(&log);
    let mut h = b.serve(&sock).unwrap();
    let mut a = Client::connect(&sock).unwrap();
    a.publish(1, 1, "/o/a", b"before").unwrap();
    assert_eq!(b.poisoned(), None, "a healthy log names no poison");
    assert!(!b.stats().log.poisoned);

    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let err = a.publish(1, 2, "/e/a", b"a person's word").unwrap_err();
    let first = refusal(&err);
    assert_eq!(first.code, astream_broker::proto::ERR_REFUSED);
    assert!(
        !first.is_poisoned(),
        "the op whose flush failed is told its own outcome, not the poison: {first}"
    );
    let why = b.poisoned().expect("the failed flush poisoned the open");
    assert!(why.contains("a flush failed"), "{why}");
    assert!(b.stats().log.poisoned, "stats agrees");
    b.inject_faults(InjectedFaults::default());

    // Two waited writes from two connections, queued behind one parked batch.
    let pause = b.pause_next_batch();
    a.send_publish(1, 3, "/o/b", b"parks the writer").unwrap();
    assert!(pause.wait(), "the writer reached the parked batch");
    let queued = b.writer_round_trips();
    let wills: Vec<_> = (0..2u64)
        .map(|i| {
            let sock = sock.clone();
            thread::spawn(move || {
                let mut c = Client::connect(&sock).unwrap();
                c.will(10 + i, 100, &format!("/o/will/{i}"), b"gone")
                    .unwrap_err()
            })
        })
        .collect();
    until("both wills queued behind the parked batch", || {
        b.writer_round_trips() >= queued + 2
    });
    pause.resume();
    let parked = a.recv_publish_ack().unwrap_err();
    assert!(refusal(&parked).is_poisoned(), "{parked}");
    for will in wills {
        let err = will.join().unwrap();
        let r = refusal(&err);
        assert!(
            r.is_poisoned() && r.msg.contains(&why),
            "every op of the batch is told the log is poisoned, and why: {r}"
        );
    }

    // A resend, a fresh publish, a commit and the embedder's own flush: all refused so.
    for err in [
        a.publish(1, 2, "/e/a", b"a person's word").unwrap_err(),
        a.publish(1, 4, "/o/c", b"after").unwrap_err(),
        a.commit("G", 0).unwrap_err(),
        b.flush_durable().unwrap_err(),
    ] {
        assert!(refusal(&err).is_poisoned(), "{err}");
    }
    let generation = b.log_identity().generation;
    h.shutdown();
    drop(b);

    // The cure is the reopen: no poison, a moved generation (the run was recorded
    // Lossy), and writes land again.
    let b = open_relaxed(&log);
    assert_eq!(b.poisoned(), None, "a reopened log is not poisoned");
    assert_eq!(b.log_identity().generation, generation + 1);
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    // The op whose outcome was unknown, resent under its pinned seq, lands EXACTLY ONCE:
    // a same-boot reopen reads the held record back from the page cache, so the resend
    // dedups to it and writes no second copy. (The device dropping it — the resend then
    // appends it once, at the cut — is the crash simulation's
    // `the_outcome_unknown_resend_after_a_poison_lands_exactly_once`.)
    let held = (1, "/e/a".to_string(), b"a person's word".to_vec());
    assert_eq!(
        c.publish(1, 2, "/e/a", b"a person's word").unwrap(),
        (1, true),
        "the resend dedups to the record the failed flush held back"
    );
    assert_eq!((b.head(), b.visible_head()), (2, 2), "no second copy");
    assert_eq!(
        c.fetch(0, "/e/>", 16).unwrap().0,
        std::slice::from_ref(&held),
        "once"
    );
    // NEGATIVE CONTROL: dedup is by key, not by body — another body under the same key
    // still dedups to offset 1 and writes nothing — and a fresh seq appends.
    assert_eq!(c.publish(1, 2, "/e/a", b"another body").unwrap(), (1, true));
    assert_eq!(c.fetch(0, "/e/>", 16).unwrap().0, [held], "the first body");
    assert_eq!(
        c.publish(1, 5, "/o/d", b"after the reopen").unwrap(),
        (2, false),
        "a fresh seq is no resend"
    );
}

/// NEGATIVE CONTROL: a write that merely FAILED is code 5 too, and is not
/// `is_poisoned`. A Strict batch whose flush fails is rolled back with every earlier
/// record covered — nothing acked is at risk — so the log is not poisoned, the
/// embedder reads no poison, and once the fault clears the same connection's next
/// write lands.
#[test]
fn a_rolled_back_write_is_not_a_poisoned_log() {
    let (_tmp, log, sock) = paths("rolled");
    let b = Broker::open(&log).unwrap();
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"before").unwrap();
    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let err = c.publish(1, 2, "/o/a", b"rolled back").unwrap_err();
    let r = refusal(&err);
    assert_eq!(r.code, astream_broker::proto::ERR_REFUSED);
    assert!(!r.is_poisoned(), "a rolled-back write is not poison: {r}");
    assert_eq!(b.poisoned(), None);
    assert!(!b.stats().log.poisoned);
    b.inject_faults(InjectedFaults::default());
    c.publish(1, 2, "/o/a", b"rolled back").unwrap();
}

/// A ROLLBACK THAT FAILS poisons the log on any tier — Strict here, astream's default —
/// and says so the same way: the embedder reads the rollback named, and the next write
/// is refused `is_poisoned` until the reopen.
#[test]
fn a_failed_rollback_poisons_strict_and_says_so() {
    let (_tmp, log, sock) = paths("rollback");
    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"before").unwrap();
    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: true,
    });
    let err = c.publish(1, 2, "/o/a", b"orphan").unwrap_err();
    assert!(!refusal(&err).is_poisoned(), "{err}");
    b.inject_faults(InjectedFaults::default());
    let why = b.poisoned().expect("the failed rollback poisoned the log");
    assert!(why.contains("roll the staged suffix back"), "{why}");
    let err = c.publish(1, 3, "/o/a", b"after").unwrap_err();
    assert!(refusal(&err).is_poisoned(), "{err}");
    h.shutdown();
    drop(b);
    let b = Broker::open(&log).unwrap();
    assert_eq!(b.poisoned(), None);
}

/// The words alone, or the code alone, are not the test: a code-8 refusal that happens
/// to start with the prefix, and the wording an older broker used (`append failed: log
/// poisoned (…)`, which starts otherwise), are both `false` — the fail-safe reading.
#[test]
fn is_poisoned_needs_both_the_code_and_the_prefix() {
    let words = format!(
        "{} (a flush failed); reopen it to recover",
        astream_broker::proto::LOG_POISONED_PREFIX
    );
    let yes = BrokerRefusal {
        code: astream_broker::proto::ERR_REFUSED,
        msg: words.clone(),
    };
    assert!(yes.is_poisoned());
    assert!(!yes.is_permanent(), "a reopened log takes the same record");
    let other_code = BrokerRefusal {
        code: astream_broker::proto::ERR_UNAUTHORIZED,
        msg: words,
    };
    assert!(!other_code.is_poisoned());
    let older = BrokerRefusal {
        code: astream_broker::proto::ERR_REFUSED,
        msg: "append failed: log poisoned (x); reopen it to recover".into(),
    };
    assert!(!older.is_poisoned());
}
