// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.ordered-tier` and `broker.durable-mark`: the Ordered point on
//! the durability dial, over real files and a real socket. An Ordered ack means the batch
//! is ORDERED on the device (`F_BARRIERFSYNC`); a record the open's escalation table
//! names is flushed in FULL before anyone can see it or be acked for it (the held head),
//! the writer's horizon bounds how long an ack waits for a full flush, and every `Mark`
//! tells a reader the durable head.
//!
//! Durability here depends only on the code under test: the brokers run at
//! `Durability::Ordered { horizon: None }` unless a test is about the horizon, so a full
//! flush happens only where the test causes one. What is asserted is what the broker
//! DECIDES (the durable head, the flush counts, the order of acks and deliveries) — not
//! what the device does with a barrier, which is Apple's fcntl(2) contract and is not
//! tested here (the crash simulation checks the power-loss law against a model of it).
//!
//! WHAT THESE SOCKET TESTS CANNOT CATCH ALONE: an assertion made after an ack or a
//! delivery arrives ("the durable head already covers it") is passed by a broker that
//! answered first and finished the full flush a moment later, whenever this thread is
//! slower than the flush. The order itself — nothing the held head keeps back answered
//! before the flush — is asserted race-free in `broker::tests::held_head`, which stops
//! the writer between its early acks and the flush (`Broker::pause_next_flush`) and reads
//! each op's ack channel there; these tests corroborate it end to end.
//!
//! Ordered is served only on Apple with the log on the boot volume. Elsewhere it is
//! served Strict — never weaker — and each test asserts that instead of the Ordered
//! behaviour, so the file runs everywhere; the tests that need a held head off Apple
//! run on Relaxed too, where the escalation table holds it on every platform.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{
    broker_refusal, Broker, Client, Durability, Escalate, Escalation, Event, InjectedFaults,
    OpenOptions, Prepared, ServedReason, Tier, Volume,
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
    let log = format!("/tmp/asord_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/asord_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// The table every test opens with: a person's lane by subject, a person's producer by
/// principal, a person's inbox commit by group. These brokers are UNGUARDED, and an
/// unguarded broker binds nobody, so the principal rule never matches here
/// (`escalation.rs`). It is exercised on a guarded broker with aterm's own table, at
/// Ordered and Relaxed, in `guarded_durability`.
fn table() -> Escalation {
    Escalation::new([
        Escalate::Subject("/e/>".into()),
        Escalate::PrincipalPrefix("h-".into()),
        Escalate::Group("/cur/p/>".into()),
    ])
}

fn open(log: &str, durability: Durability) -> Broker {
    let mut o = OpenOptions::new(durability);
    o.escalation = table();
    Broker::open_opts(log, o, || Ok(Prepared::Nothing)).unwrap()
}

const ORDERED: Durability = Durability::Ordered { horizon: None };

/// Whether this platform serves Ordered for a log in `/tmp` (Apple: the boot volume).
fn serves_ordered(b: &Broker) -> bool {
    let served = b.served_durability();
    assert_eq!(served.requested, Tier::Ordered);
    if cfg!(target_vendor = "apple") {
        assert_eq!(
            (served.served, served.reason),
            (Tier::Ordered, ServedReason::None)
        );
        true
    } else {
        assert_eq!(
            (served.served, served.reason),
            (Tier::Strict, ServedReason::NotApple)
        );
        false
    }
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

/// An escalated publish is DURABLE at its ack — the durable head already covers it —
/// while an ordinary one is only ordered: the durable head stays where the open left it.
/// The escalated record's full flush covers everything before it too.
#[test]
fn an_escalated_publish_is_durable_at_its_ack_and_an_ordinary_one_is_not() {
    let (_tmp, log, sock) = paths("ack");
    let b = open(&log, ORDERED);
    let ordered = serves_ordered(&b);
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let (plain, _) = c.publish(1, 1, "/o/x", b"machine chatter").unwrap();
    if ordered {
        assert!(b.durable_head() <= plain, "an ordinary ack is only ordered");
    } else {
        assert!(
            b.durable_head() > plain,
            "served Strict: every ack is durable"
        );
    }
    let (esc, _) = c.publish(1, 2, "/e/x", b"a person's word").unwrap();
    assert!(b.durable_head() > esc, "an escalated ack is durable");
    assert!(b.durable_head() > plain, "and so is everything before it");
    // A Fetch head query reports the same durable head, in band.
    c.fetch(0, "/o/>", 0).unwrap();
    assert_eq!(c.seen_durable(), Some(b.durable_head()));
}

/// No subscriber is ever shown an escalated record the durable head does not cover yet:
/// the visible head is held at it until its full flush has succeeded.
#[test]
fn a_subscriber_never_sees_an_escalated_record_before_it_is_durable() {
    let (_tmp, log, sock) = paths("sub");
    let b = open(&log, ORDERED);
    let _ = serves_ordered(&b);
    let _h = b.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/e/>")
        .unwrap();
    sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap(); // a hang detector
    let publisher = {
        let sock = sock.clone();
        thread::spawn(move || {
            let mut c = Client::connect(&sock).unwrap();
            for i in 1..=20u64 {
                c.publish(1, 2 * i, "/o/x", b"before").unwrap();
                c.publish(1, 2 * i + 1, "/e/x", b"escalated").unwrap();
            }
        })
    };
    let mut seen = 0;
    while seen < 20 {
        match sub.recv_event().unwrap().expect("the broker stays up") {
            Event::Delivery { offset, .. } => {
                assert!(
                    b.durable_head() > offset,
                    "escalated record {offset} delivered before the durable head ({}) covered it",
                    b.durable_head()
                );
                seen += 1;
            }
            Event::Mark { .. } => {}
            Event::Gap(g) => panic!("nothing is retained here, yet told {g:?}"),
        }
    }
    publisher.join().unwrap();
}

/// An escalated op costs EXACTLY ONE full flush, outside the lock; so does a resend of
/// an escalated op whose original no full flush covers, though the batch stages
/// nothing. A `flush_durable` with nothing uncovered is skipped, and counted so.
#[test]
fn an_escalation_costs_one_full_flush_and_a_covered_flush_is_skipped() {
    let (_tmp, log, sock) = paths("count");
    let b = open(&log, ORDERED);
    let ordered = serves_ordered(&b);
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let start = b.flush_counts();
    let (orig, _) = c.publish(2, 1, "/o/y", b"an ordinary original").unwrap();
    let after_plain = b.flush_counts();
    if !ordered {
        // Served Strict: every batch is one full flush, and nothing else is ever owed.
        assert_eq!(after_plain.full, start.full + 1);
        assert_eq!(b.flush_durable().unwrap(), b.durable_head());
        assert_eq!(b.flush_counts().skipped, after_plain.skipped + 1);
        return;
    }
    assert_eq!(
        (after_plain.barrier, after_plain.full),
        (start.barrier + 1, start.full),
        "an ordinary Ordered batch is one barrier"
    );
    c.publish(1, 1, "/e/a", b"escalated").unwrap();
    let after_esc = b.flush_counts();
    assert_eq!(
        after_esc.full,
        after_plain.full + 1,
        "exactly one full flush"
    );
    // The original is covered now; a fresh uncovered one, then its escalated resend.
    let (orig2, _) = c.publish(3, 1, "/o/z", b"another original").unwrap();
    assert!(b.durable_head() <= orig2);
    let before_resend = b.flush_counts();
    let (off, deduped) = c.publish(3, 1, "/e/z", b"resent as a person's").unwrap();
    assert_eq!((off, deduped), (orig2, true), "a resend, nothing staged");
    let after_resend = b.flush_counts();
    assert_eq!(
        after_resend.full,
        before_resend.full + 1,
        "one full flush for it"
    );
    assert!(b.durable_head() > orig2, "the resend's ack waited for it");
    assert!(orig < orig2);
    // Nothing uncovered: skipped.
    let durable = b.flush_durable().unwrap();
    assert_eq!(durable, b.durable_head());
    let skipped = b.flush_counts();
    assert_eq!(
        (skipped.full, skipped.skipped),
        (after_resend.full, after_resend.skipped + 1)
    );
    // Something uncovered: flushed, and the answer covers it.
    let (plain, _) = c.publish(1, 2, "/o/w", b"ordinary").unwrap();
    assert!(b.flush_durable().unwrap() > plain);
    assert_eq!(b.flush_counts().full, skipped.full + 1);
}

/// With a ZERO horizon the writer issues the full flush itself, right after the batch's
/// acks: the durable head catches up with no escalation and no `flush_durable`.
#[test]
fn the_writers_horizon_flushes_in_full_on_its_own() {
    let (_tmp, log, sock) = paths("horizon");
    let b = open(
        &log,
        Durability::Ordered {
            horizon: Some(Duration::ZERO),
        },
    );
    let ordered = serves_ordered(&b);
    assert_eq!(b.served_durability().horizon_ms, Some(0), "zero, not none");
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let start = b.flush_counts().full;
    let (off, _) = c.publish(1, 1, "/o/x", b"ordinary").unwrap();
    until("the horizon's full flush", || {
        b.durable_head() > off && b.flush_counts().full > start
    });
    if ordered {
        assert_eq!(
            b.flush_counts().barrier,
            1,
            "the batch itself was only barriered"
        );
    }
}

/// THE HORIZON FLUSHES AN IDLE BROKER ON ITS OWN TIMER. One ordinary record is published
/// at a 250 ms horizon and then nothing is sent at all: no batch follows it to carry the
/// flush, nothing is escalated, nobody calls `flush_durable`. The writer flushes in full
/// when the horizon falls due; a subscriber that asked
/// for idle marks (an hour away, so no idle mark comes) is then sent a DURABLE mark past
/// the record. That mark is the signal an embedder pages on: aterm's notifier holds an
/// ordinary record until one covers it, at aterm's 100 ms horizon.
///
/// The writer may notice the due horizon just after the batch or on a timed wake,
/// depending on when the OS schedules it. Both paths owe the same full flush and mark.
/// The wait for the mark is a one-minute hang detector, never a latency budget.
///
/// NEGATIVE CONTROLS (each a planted break in `writer_loop`, scratch-reverted): an owed
/// horizon that waits with `recv()` instead of its timer leaves the record unflushed, and
/// this test fails at its hang detector. A full flush after every batch, due or not,
/// is rejected by `a_long_horizon_flushes_nothing_early` below.
#[test]
fn the_horizon_flushes_an_idle_broker_on_its_timer() {
    let (_tmp, log, sock) = paths("idle");
    let b = open(
        &log,
        Durability::Ordered {
            horizon: Some(Duration::from_millis(250)),
        },
    );
    let ordered = serves_ordered(&b);
    b.set_idle_mark(Duration::from_secs(3600));
    let _h = b.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/o/>")
        .unwrap();
    sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap(); // a hang detector
    assert!(
        matches!(sub.recv_event().unwrap(), Some(Event::Mark { next: 0, .. })),
        "the catch-up mark"
    );
    let start = b.flush_counts();
    let mut c = Client::connect(&sock).unwrap();
    let (off, _) = c.publish(1, 1, "/o/x", b"ordinary").unwrap();
    if !ordered {
        // Served Strict: the batch was flushed in full before its ack, and nothing is
        // left for a horizon to owe.
        assert!(b.durable_head() > off, "served Strict: durable at its ack");
        assert_eq!(b.flush_counts().full, start.full + 1);
        return;
    }
    // Read the delivery and the durable mark that covers it, in whichever order the
    // tail sends them; nothing else is published.
    let (mut delivered, mut durable) = (false, None);
    while !delivered || durable.is_none() {
        match sub
            .recv_event()
            .expect("the horizon's durable mark, within the one-minute hang detector")
            .expect("the broker stays up")
        {
            Event::Delivery { offset, .. } => {
                assert_eq!(offset, off);
                delivered = true;
            }
            Event::Mark { durable: d, .. } => {
                let d = d.expect("an Ordered broker's mark carries its durable head");
                assert!(
                    d > off,
                    "a mark before the flush: idle marks are an hour away"
                );
                durable = Some(d);
            }
            Event::Gap(g) => panic!("nothing is retained here, yet told {g:?}"),
        }
    }
    assert!(b.durable_head() > off);
    assert_eq!(
        b.flush_counts().full,
        start.full + 1,
        "one full flush, the horizon's"
    );
}

/// A LONG HORIZON FLUSHES NOTHING EARLY — counted, not timed. At a one-hour horizon, A is
/// published, then B, and B's ack is read. The writer is one thread: any full flush it
/// issued for A, after A's batch or on a timer, finished before it answered B. None did —
/// two batches, two barriers, the full flushes where the open left them, and no timed wake
/// — so the first full flush is the one asked for: `flush_durable` adds exactly one, and
/// its answer covers both records.
///
/// NEGATIVE CONTROL (a planted break in `writer_loop`, scratch-reverted): a full flush
/// after every batch, due or not, fails it with two full flushes before B's ack is read.
#[test]
fn a_long_horizon_flushes_nothing_early() {
    let (_tmp, log, sock) = paths("long");
    let b = open(
        &log,
        Durability::Ordered {
            horizon: Some(Duration::from_secs(3600)),
        },
    );
    let ordered = serves_ordered(&b);
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let (start, woken) = (b.flush_counts(), b.stats().writer_wakeups);
    let (a, _) = c.publish(1, 1, "/o/a", b"A").unwrap();
    let (second, _) = c.publish(1, 2, "/o/b", b"B").unwrap();
    assert!(a < second);
    if !ordered {
        // Served Strict: each batch is its own full flush.
        assert_eq!(b.flush_counts().full, start.full + 2);
        assert!(b.durable_head() > second);
        return;
    }
    let after = b.flush_counts();
    assert_eq!(
        (after.barrier, after.full),
        (start.barrier + 2, start.full),
        "two batches, two barriers, no full flush"
    );
    assert_eq!(b.stats().writer_wakeups, woken, "no timed wake");
    assert!(b.durable_head() <= a, "neither record is durable yet");
    assert!(b.flush_durable().unwrap() > second, "the flush covers both");
    assert_eq!(b.flush_counts().full, start.full + 1, "exactly one");
}

/// A subscriber that asked for idle marks gets a DURABLE mark on an Ordered broker when
/// a full flush covers records it was delivered — and none on a Strict broker, where the
/// durable head is the visible head after every batch: there the event after one
/// delivery is the next delivery.
#[test]
fn a_durable_mark_reaches_an_idle_marks_subscriber_on_ordered_never_on_strict() {
    for durability in [ORDERED, Durability::Strict] {
        let (_tmp, log, sock) = paths("dmark");
        let b = open(&log, durability);
        // Idle marks only after an hour: every Mark below the catch-up one is a durable
        // mark.
        b.set_idle_mark(Duration::from_secs(3600));
        let ordered = b.served_durability().served == Tier::Ordered;
        let _h = b.serve(&sock).unwrap();
        let mut sub = Client::connect(&sock)
            .unwrap()
            .subscribe(0, "/o/>")
            .unwrap();
        sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap(); // a hang detector
        assert!(
            matches!(sub.recv_event().unwrap(), Some(Event::Mark { next: 0, .. })),
            "the catch-up mark"
        );
        let mut c = Client::connect(&sock).unwrap();
        let (first, _) = c.publish(1, 1, "/o/a", b"one").unwrap();
        assert!(matches!(
            sub.recv_event().unwrap(),
            Some(Event::Delivery { offset, .. }) if offset == first
        ));
        b.flush_durable().unwrap();
        let (second, _) = c.publish(1, 2, "/o/b", b"two").unwrap();
        // Read until the second delivery has come, and (Ordered) a durable mark that
        // covers the first — it may come before the second delivery or after it.
        let mut marked = None;
        let mut delivered = false;
        while !delivered || (ordered && marked.is_none()) {
            match sub.recv_event().unwrap().expect("the broker stays up") {
                Event::Delivery { offset, .. } => {
                    assert_eq!(offset, second);
                    delivered = true;
                }
                Event::Mark { durable, .. } => {
                    assert!(ordered, "{durability:?}: a durable mark on a Strict broker");
                    assert!(durable.is_some_and(|d| d > first), "it covers the first");
                    marked = durable;
                }
                Event::Gap(g) => panic!("nothing is retained here, yet told {g:?}"),
            }
        }
        assert!(
            sub.seen_durable().is_some(),
            "the stream kept what its marks said"
        );
    }
}

/// The tier served, as `Hello` reports it, for every tier — and Ordered asked for off
/// the boot volume is served Strict, with the reason.
#[test]
fn hello_reports_the_tier_served_for_every_tier() {
    for (durability, served, horizon_ms) in [
        (Durability::Strict, Tier::Strict, None),
        (Durability::Relaxed, Tier::Relaxed, None),
        (Durability::ordered(), Tier::Ordered, Some(1000)),
        (ORDERED, Tier::Ordered, None),
    ] {
        let (_tmp, log, sock) = paths("hello");
        let b = open(&log, durability);
        let _h = b.serve(&sock).unwrap();
        let mut c = Client::connect(&sock).unwrap();
        c.hello().unwrap();
        let told = c
            .served_durability()
            .expect("the Hello block carries the tier");
        assert_eq!(told, b.served_durability());
        assert_eq!((told.horizon_ms, told.rules), (horizon_ms, 3));
        if served == Tier::Ordered && !cfg!(target_vendor = "apple") {
            assert_eq!(told.served, Tier::Strict);
        } else {
            assert_eq!(told.served, served);
        }
    }
    let (_tmp, log, _sock) = paths("other");
    let mut o = OpenOptions::new(ORDERED);
    o.volume = Volume::Other;
    let b = Broker::open_opts(&log, o, || Ok(Prepared::Nothing)).unwrap();
    let told = b.served_durability();
    let reason = if cfg!(target_vendor = "apple") {
        ServedReason::NotBootVolume
    } else {
        ServedReason::NotApple
    };
    assert_eq!(
        (told.requested, told.served, told.reason),
        (Tier::Ordered, Tier::Strict, reason)
    );
}

/// THE BOOT-VOLUME PREDICATE IS PUBLIC (`astream_broker::on_boot_volume`), so that an
/// embedder which trusts its own unflushed writes within one boot draws that line where
/// the log does. aterm's incarnation lease is such a write. The lease lives in a
/// directory, and a directory opened as a `File` answers for the files written inside
/// it. Where Ordered is served at all (Apple), the predicate is the log's own decision:
/// a log in `/tmp` is served Ordered exactly when its directory is on the boot volume.
/// Negative control: devfs's `/dev` is a device of its own and is never on the boot
/// volume.
#[test]
fn the_boot_volume_predicate_is_public_and_a_directory_answers_for_its_files() {
    use astream_broker::on_boot_volume;
    use std::fs::File;
    let (_tmp, log, _sock) = paths("bootvol");
    let b = Broker::open_opts(&log, OpenOptions::new(ORDERED), || Ok(Prepared::Nothing)).unwrap();
    let dir = std::path::Path::new(&log)
        .parent()
        .expect("the log has a directory");
    let of_dir = on_boot_volume(&File::open(dir).unwrap());
    assert_eq!(
        of_dir,
        on_boot_volume(&File::open(&log).unwrap()),
        "the directory answers for the log written inside it"
    );
    if cfg!(target_vendor = "apple") {
        assert!(
            of_dir,
            "/tmp is on the data volume, which is the boot volume"
        );
        assert_eq!(b.served_durability().served == Tier::Ordered, of_dir);
    }
    assert!(!on_boot_volume(&File::open("/dev").unwrap()));
}

/// Retention refuses to prune above the visible head: while a batch is HELD for the
/// full flush its escalated record owes, the records at and above that record are
/// committed but shown to nobody.
#[cfg(feature = "retention")]
#[test]
fn retention_above_the_held_head_is_refused() {
    let (_tmp, log, sock) = paths("retain");
    let b = open(&log, ORDERED);
    if !serves_ordered(&b) {
        return; // served Strict: no head is ever held (the guard is the same code)
    }
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"visible").unwrap();
    let pause = b.pause_next_acks();
    let (tx, rx) = std::sync::mpsc::channel();
    let publisher = {
        let sock = sock.clone();
        thread::spawn(move || {
            let mut c = Client::connect(&sock).unwrap();
            let _ = tx.send(c.publish(1, 2, "/e/a", b"held").map(|(off, _)| off));
        })
    };
    assert!(pause.wait(), "the writer reached the acks");
    // Committed, the visible head held at the escalated record (offset 1), log head 2.
    assert_eq!(b.visible_head(), 1);
    assert_eq!(b.head(), 2);
    let err = b.retain_before(2).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{err}");
    assert!(err.to_string().contains("visible head"), "{err}");
    pause.resume();
    let off = rx
        .recv_timeout(Duration::from_secs(60))
        .expect("the held publish was acked")
        .unwrap();
    assert_eq!(off, 1);
    publisher.join().unwrap();
    assert_eq!(b.visible_head(), 2, "the full flush released the head");
}

/// A FAILED full flush — the fault seam armed so every full flush fails, while the
/// Ordered batch's barrier still succeeds — answers the waiting escalated op
/// `ERR_REFUSED` ("the outcome is unknown"), keeps its record unseen, reports Strict in
/// `Hello`, records the run `Lossy` (so the next open moves the generation even in the
/// same boot) and POISONS the open: the producer's resend, which would dedup to the held
/// record, is refused rather than acked on the strength of a later flush that succeeds —
/// which on a real device has nothing dirty left to rewrite for that record and returns
/// 0 whether or not it is on media. The REOPEN cures it: the same resend then lands
/// exactly once ([`resend_lands_once_on_the_reopened_log`]). Run on Relaxed too, where
/// the escalation table holds the head the same way on every platform.
#[test]
fn a_failed_full_flush_refuses_the_waiting_op_and_poisons_the_open() {
    for durability in [ORDERED, Durability::Relaxed] {
        let (_tmp, log, sock) = paths("lossy");
        let generation;
        {
            let b = open(&log, durability);
            let holds = b.served_durability().served != Tier::Strict;
            let mut h = b.serve(&sock).unwrap();
            let mut c = Client::connect(&sock).unwrap();
            c.publish(1, 1, "/o/a", b"before").unwrap();
            generation = b.log_identity().generation;
            let durable = b.durable_head();
            b.inject_faults(InjectedFaults {
                write: false,
                sync: true,
                truncate: false,
            });
            let err = c.publish(1, 2, "/e/a", b"a person's word").unwrap_err();
            let refusal = broker_refusal(&err).expect("a broker refusal");
            assert_eq!(refusal.code, astream_broker::proto::ERR_REFUSED);
            if !holds {
                // Ordered served Strict: the batch's own full flush fails and is rolled
                // back, with every earlier record already covered — no poison.
                assert!(refusal.msg.contains("commit failed"), "{}", refusal.msg);
                continue;
            }
            assert!(
                refusal.msg.contains("durability flush failed") && refusal.msg.contains("resend"),
                "{durability:?}: {}",
                refusal.msg
            );
            assert_eq!(b.visible_head(), 1, "the escalated record stays unseen");
            let served = b.served_durability();
            assert_eq!(
                (served.served, served.reason),
                (Tier::Strict, ServedReason::LatchedAfterFlushFailure)
            );
            c.hello().unwrap();
            assert_eq!(c.served_durability(), Some(served), "Hello says so too");
            assert_eq!(b.flush_counts().failed, 1);
            b.inject_faults(InjectedFaults::default());
            // The resend, the faults lifted: refused, the held record still unseen and
            // no durable head past it.
            let err = c.publish(1, 2, "/e/a", b"a person's word").unwrap_err();
            let refusal = broker_refusal(&err).expect("a broker refusal");
            assert!(refusal.msg.contains("poisoned"), "{}", refusal.msg);
            assert!(c.publish(1, 3, "/o/b", b"after").is_err(), "no write lands");
            assert!(b.flush_durable().is_err(), "no flush is asked for");
            assert_eq!(
                (b.visible_head(), b.durable_head()),
                (1, durable),
                "{durability:?}: nothing a later flush reports releases the held record"
            );
            h.shutdown();
        }
        let b = open(&log, durability);
        assert_eq!(
            b.log_identity().generation,
            generation + 1,
            "{durability:?}: Lossy moves the generation in the same boot"
        );
        resend_lands_once_on_the_reopened_log(&b, &sock, durability);
    }
}

/// THE CURE an embedder relies on, after a failed full flush poisoned the open and the
/// log was REOPENED in the same boot: the producer resends the op whose outcome was
/// unknown under the same pinned `(producer_id, producer_seq)`, and it lands EXACTLY
/// ONCE. A same-boot reopen reads back what the page cache kept, so the held record is
/// in the reopened log and the resend DEDUPS to it — offset 1, `deduped` — and no second
/// copy is written: the head and the visible head stay 2, and a Fetch holds that record
/// once, with the body the failed op sent. (The branch in which the device DROPPED the
/// record — the resend then appends it once, at the cut — cannot be reached over a socket,
/// which never drops the page cache: it is the crash simulation's
/// `the_outcome_unknown_resend_after_a_poison_lands_exactly_once`. Nor can a real device's
/// failed flush that left the record's pages clean but unwritten, which the injected
/// fault never does: there the reopen's flush has nothing to rewrite, and a later power
/// loss that takes the record is refused at the next open — `BrokerLog::flush_failed_lossy`'s
/// HONEST BOUNDARY.)
///
/// NEGATIVE CONTROL: the dedup is by key, not by body — a different body under the same
/// key still dedups to offset 1 and writes nothing, the record keeping the first body —
/// and a FRESH seq, 4, never sent (3 was, and the poisoned log refused it), is no resend:
/// it appends at offset 2, `deduped` false.
fn resend_lands_once_on_the_reopened_log(b: &Broker, sock: &str, durability: Durability) {
    let mut h = b.serve(sock).unwrap();
    let mut c = Client::connect(sock).unwrap();
    let held = (1, "/e/a".to_string(), b"a person's word".to_vec());
    assert_eq!(
        c.publish(1, 2, "/e/a", b"a person's word").unwrap(),
        (1, true),
        "{durability:?}: the resend dedups to the record the failed flush held back"
    );
    assert_eq!(
        (b.head(), b.visible_head()),
        (2, 2),
        "{durability:?}: no second copy, and the reopen shows the record"
    );
    let (rows, _) = c.fetch(0, "/e/>", 16).unwrap();
    assert_eq!(
        rows,
        std::slice::from_ref(&held),
        "{durability:?}: one record, once"
    );
    // Negative control: same key, another body — still the original's offset.
    assert_eq!(
        c.publish(1, 2, "/e/a", b"another body").unwrap(),
        (1, true),
        "{durability:?}: dedup is by (producer_id, producer_seq), not by body"
    );
    let (rows, _) = c.fetch(0, "/e/>", 16).unwrap();
    assert_eq!(
        rows,
        [held],
        "{durability:?}: still one record, the first body"
    );
    // Seq 4: never sent before (3 was, and the poisoned log refused it).
    assert_eq!(
        c.publish(1, 4, "/o/b", b"after").unwrap(),
        (2, false),
        "{durability:?}: a fresh seq is no resend and appends"
    );
    assert_eq!(b.head(), 3);
    h.shutdown();
}

/// A group commit the `Group` rule escalates (a person's inbox read mark) does not steer
/// a second reader of the group while it is HELD for its full flush: that reader resumes
/// below it, from the commit the durable head covers, and is delivered the mail the held
/// commit would mark read. Once the flush releases it, a new reader resumes past it.
/// Relaxed, where the escalation table holds the head the same way on every platform.
#[test]
fn a_held_group_commit_steers_no_reader_until_its_flush() {
    let (_tmp, log, sock) = paths("group");
    let b = open(&log, Durability::Relaxed);
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    for seq in 1..=6 {
        c.publish(1, seq, "/o/m", b"mail").unwrap();
    }
    let pause = b.pause_next_acks();
    let committer = {
        let sock = sock.clone();
        thread::spawn(move || {
            Client::connect(&sock)
                .unwrap()
                .commit("/cur/p/alice/inbox", 2)
        })
    };
    assert!(pause.wait(), "the writer reached the commit's acks");
    // Committed at offset 6, held for its full flush: the visible head stops at it.
    assert_eq!((b.visible_head(), b.head()), (6, 7));
    let first = |sock: &str| {
        let mut sub = Client::connect(sock)
            .unwrap()
            .subscribe_group("/cur/p/alice/inbox", "/o/>")
            .unwrap();
        sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap(); // a hang detector
        loop {
            match sub.recv_event().unwrap().expect("the broker stays up") {
                Event::Delivery { offset, .. } => return offset,
                Event::Mark { .. } => {}
                Event::Gap(g) => panic!("nothing is retained here, yet told {g:?}"),
            }
        }
    };
    assert_eq!(
        first(&sock),
        0,
        "a held read mark must not make a second reader skip mail"
    );
    pause.resume();
    assert_eq!(committer.join().unwrap().unwrap(), 6, "the commit lands");
    assert_eq!(first(&sock), 3, "released, the read mark steers the group");
}
