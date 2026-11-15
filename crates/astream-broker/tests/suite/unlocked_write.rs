// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.unlocked-batch-write`: the writer writes and flushes each batch
//! with the log lock RELEASED, and that moves nothing a reader or a producer can see.
//!
//! The writer used to hold the log lock from staging through `write` and `F_FULLFSYNC`
//! to promotion, so every reader beside a busy Strict writer — a `Fetch` page, a `Last`
//! round, a tail copying the record it was just woken for — waited out most of an
//! fsync (cost study B2). Now a batch commits in three halves: a locked begin (seal,
//! flush chosen, bytes taken), the write and flush with the lock free, and a locked end
//! (promote, or roll back). What has to stay true across the free window:
//!
//! 1. readers answer in it, and see the log as it was before the batch — the batch's
//!    records are promoted only at the end, after the flush returned;
//! 2. the batch's fault-injection seam is the one armed when it began, and a failed
//!    flush in the free window still rolls the batch back whole;
//! 3. retention, which rewrites the file, waits for the batch instead of running beside
//!    it or being refused — a compaction, and the rules `set_retention` writes into the
//!    held store.
//!
//! Counts and outcomes, never durations. The seam is [`Broker::pause_next_write`],
//! which parks the writer at the start of a batch's write with the log lock released,
//! so "answers while the batch is written" is a fact a test can observe: the read
//! returns, or it hangs. Every wait for something that must happen is a one-minute
//! HANG DETECTOR. The negative control is not in this file: it is the unit test
//! `the_log_lock_is_held_while_staging_and_free_for_the_write` in `src/broker.rs`, a
//! `try_lock` of the log mutex that fails with the writer parked at
//! [`Broker::pause_next_batch`] (staged, the lock still held) and succeeds at
//! [`Broker::pause_next_write`]. A `Fetch` sent at `pause_next_batch` is no control:
//! once the writer is resumed it releases the lock for the write, so that `Fetch` may
//! answer in the window, at the head before the batch, without the batch's record.

#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, Client, InjectedFaults};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Duration;

static NEXT: AtomicU64 = AtomicU64::new(0);

/// An exclusive scratch directory under `/tmp` (a Darwin `TMPDIR` is long enough to
/// push a socket path past `SUN_LEN`), removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asbw-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn log(&self) -> PathBuf {
        self.0.join("b.log")
    }

    fn sock(&self) -> PathBuf {
        self.0.join("b.sock")
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A Strict broker (one full flush per batch) served on the scratch socket.
fn serve(s: &Scratch) -> (Arc<Broker>, BrokerHandle) {
    let b = Broker::open(s.log()).unwrap();
    let h = b.serve(s.sock()).unwrap();
    (Arc::new(b), h)
}

/// Run `f` on its own thread and wait for it — a one-minute HANG DETECTOR, never a
/// latency budget: a read that waits on the log lock while the writer is parked
/// holding it fails here instead of hanging the suite.
fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(Duration::from_secs(60))
        .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
}

/// Wait until `cond` holds — a one-minute HANG DETECTOR for something that must
/// happen, never a latency budget.
#[cfg(feature = "retention")]
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    use std::time::Instant;
    let deadline = Instant::now() + Duration::from_secs(60);
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::sleep(Duration::from_millis(5));
    }
}

/// Three records on `/t/0`..`/t/2` (producer 1, sequences 1..=3), at offsets 0..=2.
fn three(sock: &PathBuf) -> Client {
    let mut w = Client::connect(sock).unwrap();
    for i in 0..3u64 {
        assert_eq!(
            w.publish(1, i + 1, &format!("/t/{i}"), b"old").unwrap(),
            (i, false)
        );
    }
    w
}

/// The offsets of a page.
fn offsets(page: &[(u64, String, Vec<u8>)]) -> Vec<u64> {
    page.iter().map(|(off, _, _)| *off).collect()
}

/// READERS ANSWER WHILE A BATCH IS WRITTEN, AND SEE NONE OF IT. With the writer parked
/// at the start of a Strict batch's write (staged, sealed, the log lock released): a
/// `Fetch` page, a `Last` page and `stats` all answer, and a NEW subscription catches
/// up from offset 0 — every one of them takes the log lock — and each sees the log as
/// it stood before the batch: three records, head 3. The batch's record is promoted
/// only at its end: once resumed, its ack names offset 3, the same `Fetch` returns four
/// records, and the subscription is delivered the fourth. The parked publish is exactly
/// one writer batch.
///
/// NEGATIVE CONTROL: that these reads answered because the lock was free, and not
/// because they never needed it, is the unit test
/// `the_log_lock_is_held_while_staging_and_free_for_the_write` in `src/broker.rs`: at
/// [`Broker::pause_next_batch`], where the writer still holds the log lock, a
/// `try_lock` of it fails; at [`Broker::pause_next_write`] it succeeds. (A `Fetch` sent
/// at the first point and resumed is no control any more: once resumed, the writer
/// releases the lock for the write, and the `Fetch` may answer in that window.)
#[test]
fn readers_answer_while_a_batch_is_written_and_see_none_of_it() {
    let s = Scratch::new("readers");
    let (b, _h) = serve(&s);
    let sock = s.sock();
    let mut w = three(&sock);
    let mut r = Client::connect(&sock).unwrap();
    let batches = b.stats().writer_batches;

    let pause = b.pause_next_write();
    let parked = thread::spawn(move || w.publish(1, 4, "/t/3", b"new"));
    let pause = within_a_minute("the writer to reach the paused write", move || {
        assert!(pause.wait(), "the writer stopped before the paused write");
        pause
    });

    // The writer is parked between its locked begin and its write: the log lock is free.
    let b2 = Arc::clone(&b);
    let stats = within_a_minute("Broker::stats in the write window", move || b2.stats());
    assert_eq!(stats.log.head.0, 3, "the batch is not promoted yet");
    assert_eq!(stats.visible_head, 3, "nor visible");
    let (mut r, page) = within_a_minute("a Fetch in the write window", move || {
        let page = r.fetch(0, "/t/>", 16).unwrap();
        (r, page)
    });
    assert_eq!(
        offsets(&page.0),
        [0, 1, 2],
        "the batch's record is not readable"
    );
    assert_eq!(page.1, (3, 3), "read at the head before the batch");
    let (mut r, last) = within_a_minute("a Last page in the write window", move || {
        let page = r.last("/t/>", "", 16).unwrap();
        (r, page)
    });
    assert_eq!(
        last.0
            .iter()
            .map(|(_, s, _)| s.as_str())
            .collect::<Vec<_>>(),
        ["/t/0", "/t/1", "/t/2"],
        "the last-value index does not hold the batch's subject"
    );
    assert_eq!(last.1 .1, 3, "the Last page was read at head 3");
    let sock2 = sock.clone();
    let mut sub = within_a_minute(
        "a new subscription's catch-up in the write window",
        move || {
            let mut sub = Client::connect(&sock2)
                .unwrap()
                .subscribe(0, "/t/>")
                .unwrap();
            let caught_up: Vec<u64> = (0..3)
                .map(|_| sub.recv().unwrap().expect("a delivery").0)
                .collect();
            assert_eq!(
                caught_up,
                [0, 1, 2],
                "the tail copied the committed records"
            );
            sub
        },
    );

    pause.resume();
    assert_eq!(
        within_a_minute("the parked publish's ack", move || parked.join().unwrap()).unwrap(),
        (3, false),
        "acked once its batch committed"
    );
    let page = r.fetch(0, "/t/>", 16).unwrap();
    assert_eq!(
        offsets(&page.0),
        [0, 1, 2, 3],
        "promoted at the batch's end"
    );
    let fourth = within_a_minute("the subscription's delivery of the batch", move || {
        sub.recv().unwrap().expect("a delivery")
    });
    assert_eq!((fourth.0, fourth.1.as_str()), (3, "/t/3"));
    assert_eq!(
        b.stats().writer_batches - batches,
        1,
        "the parked publish was one batch"
    );
}

/// THE FAILED FLUSH OUTSIDE THE LOCK IS STILL THE BATCH'S. The injected fsync fault
/// travels with the batch from its begin: armed before the batch, then cleared in the
/// write window (the log lock is free there, and `inject_faults` takes it), the batch's
/// flush still fails, nothing is promoted — the head stays at 3, a `Fetch` reads three
/// records — and every op of it is told; the same record resent then lands at offset 3.
/// A fault armed only IN the window is the next batch's, not this one's: the batch
/// commits, and the next one fails.
#[test]
fn a_flush_failed_outside_the_lock_rolls_the_batch_back_whole() {
    let s = Scratch::new("fault");
    let (b, _h) = serve(&s);
    let sock = s.sock();
    let mut w = three(&sock);
    let mut r = Client::connect(&sock).unwrap();
    let fault = InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    };

    // Armed before the batch, cleared in its write window: the batch fails.
    b.inject_faults(fault);
    let pause = b.pause_next_write();
    let parked = thread::spawn(move || {
        let res = w.publish(1, 4, "/t/3", b"lost");
        (w, res)
    });
    let pause = within_a_minute("the writer to reach the paused write", move || {
        assert!(pause.wait(), "the writer stopped before the paused write");
        pause
    });
    let b2 = Arc::clone(&b);
    within_a_minute("inject_faults in the write window", move || {
        b2.inject_faults(InjectedFaults::default());
    });
    pause.resume();
    let (mut w, res) = within_a_minute("the failed batch's answer", move || parked.join().unwrap());
    let err = res.expect_err("the batch's flush failed");
    assert!(err.to_string().contains("injected fsync fault"), "{err}");
    assert_eq!(b.stats().log.head.0, 3, "nothing promoted");
    assert_eq!(offsets(&r.fetch(0, "/t/>", 16).unwrap().0), [0, 1, 2]);
    assert_eq!(
        w.publish(1, 4, "/t/3", b"resent").unwrap(),
        (3, false),
        "the resend lands where the failed batch would have"
    );

    // Armed only in the write window: the batch in flight commits, the next one fails.
    let pause = b.pause_next_write();
    let parked = thread::spawn(move || {
        let res = w.publish(1, 5, "/t/4", b"kept");
        (w, res)
    });
    let pause = within_a_minute("the writer to reach the paused write", move || {
        assert!(pause.wait(), "the writer stopped before the paused write");
        pause
    });
    let b2 = Arc::clone(&b);
    within_a_minute("inject_faults in the write window", move || {
        b2.inject_faults(fault)
    });
    pause.resume();
    let (mut w, res) = within_a_minute("the batch's answer", move || parked.join().unwrap());
    assert_eq!(
        res.unwrap(),
        (4, false),
        "its fault was armed after it began"
    );
    let err = w
        .publish(1, 6, "/t/5", b"next")
        .expect_err("the next batch takes the fault");
    assert!(err.to_string().contains("injected fsync fault"), "{err}");
    b.inject_faults(InjectedFaults::default());
    assert_eq!(offsets(&r.fetch(0, "/t/>", 16).unwrap().0), [0, 1, 2, 3, 4]);
}

/// RETENTION WAITS FOR A BATCH BEING WRITTEN. With the writer parked in a batch's write
/// window, `retain_before(4)` neither runs beside the batch nor is refused: it waits on
/// the writer's batch lock (counted, `retention_waits` 0 → 1), and once the batch has
/// committed it compacts the log the batch extended — offsets 1..=3 dropped, the
/// batch's own record at 3 among them, which a retention run in the window could not
/// have reached (the head was 3 there, and retention clamps to the head: it would have
/// dropped two). Between batches retention takes the lock at once and counts no wait.
///
/// What a retention in the window would have met instead — the log refusing it while
/// the batch is staged — is the unit test
/// `in_the_write_window_the_log_refuses_every_other_mutation` in `src/broker.rs`.
#[cfg(feature = "retention")]
#[test]
fn retention_waits_for_a_batch_being_written() {
    let s = Scratch::new("retain");
    let (b, _h) = serve(&s);
    let sock = s.sock();
    let mut w = three(&sock);

    assert_eq!(b.retain_before(1).unwrap(), 1, "between batches");
    assert_eq!(b.stats().retention_waits, 0, "no batch to wait for");

    let pause = b.pause_next_write();
    let parked = thread::spawn(move || w.publish(1, 4, "/t/3", b"new"));
    let pause = within_a_minute("the writer to reach the paused write", move || {
        assert!(pause.wait(), "the writer stopped before the paused write");
        pause
    });
    let b2 = Arc::clone(&b);
    let retention = thread::spawn(move || b2.retain_before(4));
    until("retention to wait for the batch in flight", || {
        b.stats().retention_waits == 1
    });
    assert!(
        !retention.is_finished(),
        "retention returned while the batch it waited for was still parked"
    );
    pause.resume();
    assert_eq!(
        within_a_minute("the parked publish's ack", move || parked.join().unwrap()).unwrap(),
        (3, false)
    );
    assert_eq!(
        within_a_minute("retention after the batch", move || retention
            .join()
            .unwrap())
        .unwrap(),
        3,
        "offsets 1..=3 dropped: the batch's record at 3 among them"
    );
    assert_eq!(b.stats().log.base.0, 4);
    assert_eq!(b.stats().retention_waits, 1);
}

/// THE RULES ARE SET PAST A BATCH BEING WRITTEN. With the writer parked in a batch's write
/// window, `set_retention` neither writes its rules beside the batch nor is refused: it
/// waits on the writer's batch lock (counted, `retention_waits` 0 → 1), and once the batch
/// has committed it sets them, so the next `Hello` advertises them. This is where a
/// broker's open puts the wills it fires, and where `asb serve --retain-file` (and aterm's
/// open) sets the rules, with no flush first. The broker has had no rules and no cap
/// before, so it has no retention tick that could be the one waiting. Set again between
/// batches, the rules take the lock at once and count no wait.
///
/// NEGATIVE CONTROL (a planted break, scratch-reverted): `set_retention` without the batch
/// lock meets the batch staged and is refused "a batch is being written outside the log
/// lock; mutate once it commits", and the first assertion after the wait fails.
#[cfg(feature = "retention")]
#[test]
fn set_retention_waits_for_a_batch_being_written() {
    use astream_broker::{Retention, Rule};
    let rules = |n: u64| {
        Retention::new(
            vec![Rule::prefix("/t/>").unwrap().max_bytes(n << 20)],
            Rule::default_keeping_all(),
        )
        .unwrap()
    };
    let s = Scratch::new("rules");
    let (b, _h) = serve(&s);
    let sock = s.sock();
    let mut w = three(&sock);

    let pause = b.pause_next_write();
    let parked = thread::spawn(move || w.publish(1, 4, "/t/3", b"new"));
    let pause = within_a_minute("the writer to reach the paused write", move || {
        assert!(pause.wait(), "the writer stopped before the paused write");
        pause
    });
    let b2 = Arc::clone(&b);
    let setting = thread::spawn(move || b2.set_retention(rules(1)));
    until("set_retention to wait for the batch in flight", || {
        setting.is_finished() || b.stats().retention_waits == 1
    });
    assert!(
        !setting.is_finished(),
        "set_retention returned while the batch it should wait for was still parked: {:?}",
        setting.join()
    );
    pause.resume();
    assert_eq!(
        within_a_minute("the parked publish's ack", move || parked.join().unwrap()).unwrap(),
        (3, false)
    );
    within_a_minute("set_retention after the batch", move || {
        setting.join().unwrap()
    })
    .expect("the rules are set once the batch has committed");
    assert_eq!(b.stats().retention_waits, 1);
    assert_eq!(b.retention(), Some(rules(1)));
    let mut c = Client::connect(&sock).unwrap();
    c.hello().unwrap();
    assert_eq!(
        c.retention_rules(),
        Some(rules(1)),
        "the next Hello says them"
    );

    // Between batches: no batch to wait for. The tick the rules asked for may still be
    // running; it waits for no batch either (none is being written).
    b.set_retention(rules(2)).unwrap();
    assert_eq!(b.stats().retention_waits, 1, "no batch to wait for");
    assert_eq!(b.retention(), Some(rules(2)));
}
