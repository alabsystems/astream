// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The broker's RETENTION TICK (`broker.rs`: `ticker_loop`, `retention_tick`): what asks
//! for one, what it waits for and what it skips, that no publish's ack waits for its copy,
//! that a subscriber reads the held records the tick carried, and that it starts only on a
//! broker something retains and stops before the writer at shutdown.
//!
//! Every wait for something that must happen is a one-minute hang detector, never a
//! budget; nothing sleeps. A tick's clock is the wall clock only where no rule reads an
//! age; the hand-clock ticks are `Broker::retention_tick_at`'s.
//!
//! NEGATIVE CONTROLS (each a planted break, scratch-reverted, that fails the test named): a
//! writer that never asks for a tick, so the oldest stays 0
//! (`a_batch_past_the_rules_bytes_asks_for_a_tick_and_the_cut_follows`); no publish of the
//! wake after a tick that began nothing
//! (`a_tick_that_changes_nothing_still_moves_the_writers_wake`); a tick's thread
//! that waits for a retention call's compaction instead of skipping it
//! (`a_tick_skips_while_a_retention_call_compacts`); the batch lock held across the tick's
//! copy (`a_publish_acks_while_a_ticks_compaction_copies`); a tail that clamps to the base
//! (`a_subscriber_from_zero_reads_the_held_records_then_the_retained_in_offset_order`); a
//! tick started on every broker, and one never joined
//! (`a_tick_starts_only_on_a_broker_something_retains_and_stops_before_the_writer`);
//! the writer's caps never asking for a tick
//! (`automatic_state_carrying_compaction_caps_retained_records_and_preserves_state`);
//! `set_retention` without the compaction lock
//! (`rules_set_while_a_tick_compacts_wait_for_it_and_keep_what_it_carried`,
//! `rules_set_while_the_caps_compact_hold_from_the_base_that_compaction_lands`); and a caps
//! compaction on read-back rules that writes no held-store job
//! (`the_caps_on_read_back_rules_keep_what_they_dropped_unnamed_across_a_restart`).
//!
//! The wire's half of R4 (`retained-from=`, the oldest, Hello's rules, and the gap notice a
//! tail is told: addendum A9) is `wire`'s (`retention_wire_tests.rs`), on these helpers.

use super::*;
use crate::test_scratch::Scratch;
use crate::{Retention, Rule};

const MINUTE: Duration = Duration::from_secs(60); // a hang detector, never a budget
const HOUR: Duration = Duration::from_secs(3600);
const EV: &str = "/f/F/pub/n1/s1/ev";
const MAIL: &str = "/f/F/in/n1/from/a";
const BODY: &[u8] = b"0123456789abcdef";

fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(MINUTE)
        .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
}

/// Publish one record as producer 1 at `seq`, straight to the writer; its offset.
fn publish(b: &Broker, seq: u64, subject: &str) -> u64 {
    let shared = Arc::clone(&b.shared);
    let subject = subject.to_string();
    let acked = within_a_minute("a publish's ack", move || {
        submit_blocking(
            &shared,
            WriteKind::Publish {
                producer_id: 1,
                producer_seq: seq,
                subject,
                body: BODY.to_vec(),
            },
        )
    });
    match acked {
        Ok((off, false)) => off,
        other => panic!("publish {seq}: {other:?}"),
    }
}

/// The bytes one test record of `subject` takes.
fn rb(subject: &str) -> u64 {
    crate::record_bytes(&BrokerRecord {
        seq: Offset(0),
        producer_id: 1,
        producer_seq: 1,
        subject: subject.to_string(),
        body: BODY.to_vec(),
        commit: None,
    })
}

/// The bulk stream the prefix, keeping its newest `ev` records by their bytes; mail held
/// until its node's inbox group reads it or for 7 days; presence and the rest by their
/// last value.
fn rules(ev: u64) -> Retention {
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev")
                .unwrap()
                .max_bytes(ev * rb(EV)),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_age(Duration::from_secs(7 * 86_400))
                .until_read("/f/{2}/cur/{4}/node/inbox")
                .unwrap(),
            Rule::hold("/f/F/pub/*/*/presence").unwrap().last_only(),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// Wait until `done` holds of `b`, checked at once and after every retention tick, run or
/// skipped: a one-minute hang detector, never a budget. `done` runs with no lock held.
fn await_ticks(b: &Broker, what: &str, done: impl Fn(&Broker) -> bool) {
    let deadline = Instant::now() + MINUTE;
    loop {
        let seen = {
            let t = b.shared.tick.lock().unwrap();
            (t.ticks, t.skips)
        };
        if done(b) {
            return;
        }
        let left = deadline.saturating_duration_since(Instant::now());
        assert!(
            !left.is_zero(),
            "{what}: not within a minute of retention ticks"
        );
        let t = b.shared.tick.lock().unwrap();
        let _ = b
            .shared
            .tick_done
            .wait_timeout_while(t, left, |t| (t.ticks, t.skips) == seen)
            .unwrap();
    }
}

/// The next delivery on `sub`, before `deadline`: a hang detector, never a budget. The
/// broker's idle marks between deliveries are skipped, each a chance to see the minute is
/// up (a `recv` skips them itself, so a stream kept alive by them would never time out),
/// and the subscription's read timeout of a minute catches a stream with none.
#[cfg(unix)]
fn next_delivery(sub: &mut crate::client::Subscription, deadline: Instant) -> (u64, String) {
    loop {
        assert!(
            Instant::now() < deadline,
            "no delivery within a minute of the subscribe"
        );
        match sub.recv_event().unwrap() {
            Some(crate::client::Event::Delivery {
                offset, subject, ..
            }) => return (offset, subject),
            // The marks, and the notice of what the cut gave up below the cursor: the
            // tests of what a tail is told read those themselves (`wire`).
            Some(crate::client::Event::Mark { .. } | crate::client::Event::Gap(_)) => {}
            None => panic!("the broker closed the subscription"),
        }
    }
}

fn arm_gate(b: &Broker) -> crate::compact::GateHandle {
    let (gate, held) = crate::compact::gate();
    b.shared
        .log
        .lock()
        .unwrap()
        .arm_compact_seam(crate::compact::Seam {
            gate: Some(gate),
            ..crate::compact::Seam::default()
        });
    held
}

fn disarm(b: &Broker) {
    b.shared
        .log
        .lock()
        .unwrap()
        .arm_compact_seam(crate::compact::Seam::default());
}

/// THE TRIGGER: a broker given rules cuts when a batch takes a class past its bytes — the
/// writer asks its tick, which takes the prefix rule's cut off the ack path — with no
/// interval due inside the test (an hour) and no caller asking. Each cut gives up at least
/// a quarter of the stream's 20 records, so once the 50 are in the log keeps between 16 and
/// 20 of them. NC (the plan's "no trigger"): a writer that never asks leaves the oldest at
/// 0, and the wait fails.
#[test]
fn a_batch_past_the_rules_bytes_asks_for_a_tick_and_the_cut_follows() {
    let root = Scratch::new("tick-trigger");
    let path = root.path().join("log");
    let b = Broker::open(&path).unwrap();
    b.set_retention_interval(HOUR);
    b.set_retention(rules(20)).unwrap();
    await_ticks(&b, "the tick set_retention asks for", |b| {
        b.stats().retention_ticks >= 1
    });
    for seq in 0..50u64 {
        assert_eq!(publish(&b, seq, EV), seq);
    }
    let ev = Filter::new("/f/F/pub/*/*/ev").unwrap();
    await_ticks(&b, "the cut to at most the newest 20 records", |b| {
        b.oldest(&ev) >= 30
    });
    let base = b.base();
    assert!((30..=34).contains(&base), "base {base}");
    let stats = b.stats();
    assert_eq!(stats.log.retained_records as u64, 50 - base);
    assert!(stats.retention_ticks >= 2, "{stats:?}");
    drop(b);
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!((log.base(), log.head()), (Offset(base), Offset(50)));
}

/// THE WAKE FOLLOWS EVERY PLANNING: after the tick `set_retention` asks for, which changes
/// nothing on an empty log, the writer's wake (`Shared::retain_due`) is what the planning
/// left, not due; and thirty batches under every class's bytes ask for no tick (an hour's
/// interval: no tick but an asked one runs). The one tick is exact: `set_retention` asks for
/// it before it starts the tick's thread, so the thread never takes the interval's earlier
/// ask and then this one. NCs: no publish after a tick that began nothing leaves the wake due
/// as `set_retention` published it, before any planning; and the thread started before the
/// ask, with a pause between them, ticks twice.
#[test]
fn a_tick_that_changes_nothing_still_moves_the_writers_wake() {
    let root = Scratch::new("tick-wake");
    let b = Broker::open(root.path().join("log")).unwrap();
    b.set_retention_interval(HOUR);
    b.set_retention(rules(1000)).unwrap();
    await_ticks(&b, "the first tick", |b| b.stats().retention_ticks >= 1);
    assert!(
        !b.shared.retain_due.load(Ordering::Relaxed),
        "the planning's room is the writer's"
    );
    for seq in 0..30u64 {
        publish(&b, seq, EV);
    }
    assert!(!b.shared.retain_due.load(Ordering::Relaxed));
    let stats = b.stats();
    assert_eq!(
        (
            stats.retention_ticks,
            stats.retention_skips,
            stats.log.base.0
        ),
        (1, 0, 0),
        "no batch asked for a tick"
    );
}

/// ONE COMPACTION AT A TIME, the tick's way: while a retention call's copy holds the
/// compaction lock, the tick its cap asks for SKIPS — counted, the base where it was, the
/// call unharmed — and once the call is done the next batch over the cap is cut by a tick.
/// NC: a tick's thread that waits for the lock never answers while the call is held.
#[test]
fn a_tick_skips_while_a_retention_call_compacts() {
    let root = Scratch::new("tick-skips");
    let path = root.path().join("log");
    let b = Arc::new(Broker::open(&path).unwrap());
    for seq in 0..10u64 {
        publish(&b, seq, "/t/x");
    }
    let held = arm_gate(&b);
    let b1 = Arc::clone(&b);
    let call = thread::spawn(move || b1.retain_before_carrying_state(4));
    assert!(held.wait(), "the call's copy did not reach the gate");
    b.set_max_retained_records(2);
    publish(&b, 10, "/t/x");
    await_ticks(&b, "a tick skipped while the call compacts", |b| {
        b.stats().retention_skips >= 1
    });
    assert_eq!(b.base(), 0, "a tick compacted under a retention call");
    assert_eq!(b.stats().retention_ticks, 0);
    disarm(&b);
    held.resume();
    let called = within_a_minute("the retention call", move || call.join().unwrap());
    assert_eq!(called.unwrap(), 4, "the call finished unharmed");
    publish(&b, 11, "/t/x");
    await_ticks(&b, "the cap's cut by a tick", |b| {
        let s = b.stats();
        s.log.base.0 > 4 && s.log.retained_records <= 2
    });
    let base = b.base();
    drop(b);
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!((log.base(), log.head()), (Offset(base), Offset(12)));
}

/// OFF THE ACK PATH: while the tick's compaction copies (held at the seam's gate), the
/// writer commits and acks publishes; the tick finishes with them in the kept log, and a
/// later tick cuts to the rules again. NC: the batch lock held across the tick's copy hangs
/// those acks.
#[test]
fn a_publish_acks_while_a_ticks_compaction_copies() {
    let root = Scratch::new("tick-off-ack");
    let path = root.path().join("log");
    let b = Arc::new(Broker::open(&path).unwrap());
    b.set_retention_interval(HOUR);
    b.set_retention(rules(3)).unwrap();
    await_ticks(&b, "the first tick", |b| b.stats().retention_ticks >= 1);
    let held = arm_gate(&b);
    for seq in 0..6u64 {
        publish(&b, seq, EV);
    }
    assert!(held.wait(), "the tick's copy did not reach the gate");
    for seq in 6..9u64 {
        assert_eq!(publish(&b, seq, EV), seq, "acked while the tick copies");
    }
    disarm(&b);
    held.resume();
    await_ticks(&b, "the cut to the newest 3", |b| b.base() == 6);
    drop(b);
    let log = BrokerLog::open(&path).unwrap();
    let kept: Vec<u64> = log
        .read_from(Offset::ZERO)
        .iter()
        .map(|r| r.seq.0)
        .collect();
    assert_eq!(kept, vec![6, 7, 8]);
}

/// SUBSCRIBE MERGES THE HELD RECORDS: a subscriber from 0, after a tick cut past an unread
/// mail it carried, is delivered the mail at its own offset and then the retained suffix,
/// in offset order, and tails on. NC: a tail that clamps its cursor to the base starts at
/// the cut and never sees the mail.
#[cfg(unix)]
#[test]
fn a_subscriber_from_zero_reads_the_held_records_then_the_retained_in_offset_order() {
    let root = Scratch::new("tick-subscribe");
    let path = root.path().join("log");
    let sock = root.path().join("sock");
    let b = Broker::open(&path).unwrap();
    b.set_retention_interval(HOUR);
    b.set_retention(rules(3)).unwrap();
    for (seq, subject) in [EV, MAIL, EV, EV, EV, EV, EV].into_iter().enumerate() {
        publish(&b, seq as u64, subject);
    }
    // Whatever the tick's thread cut meanwhile, this tick leaves the newest 3 ev records
    // and the mail held. The broker's own clock, as the thread's: the mail's age is read
    // from the stamps both take.
    b.retention_tick_at(b.now_ms()).unwrap();
    assert_eq!(b.base(), 4);
    assert_eq!(b.stats().log.held_records, 1);
    let mut h = b.serve(&sock).unwrap();
    let c = crate::Client::connect(&sock).unwrap();
    let mut sub = c.subscribe(0, "/f/F/>").unwrap();
    sub.set_read_timeout(Some(MINUTE)).unwrap();
    let deadline = Instant::now() + MINUTE;
    let mut got = Vec::new();
    for _ in 0..4 {
        got.push(next_delivery(&mut sub, deadline));
    }
    assert_eq!(
        got,
        vec![
            (1, MAIL.to_string()),
            (4, EV.to_string()),
            (5, EV.to_string()),
            (6, EV.to_string()),
        ]
    );
    publish(&b, 7, EV);
    let deadline = Instant::now() + MINUTE;
    assert_eq!(next_delivery(&mut sub, deadline).0, 7, "and tails on");
    drop(sub);
    h.shutdown();
}

#[cfg(unix)]
#[path = "retention_wire_tests.rs"]
mod wire;

/// `b.set_retention(rules)` on a thread of its own, handed back once that call has either
/// returned or is waiting for the compaction under way (`Shared::compaction_waits`): a
/// one-minute hang detector, never a budget.
fn rules_set_meanwhile(b: &Arc<Broker>, rules: Retention) -> thread::JoinHandle<io::Result<()>> {
    let waits = b.shared.compaction_waits.load(Ordering::Relaxed);
    let b1 = Arc::clone(b);
    let call = thread::spawn(move || b1.set_retention(rules));
    let deadline = Instant::now() + MINUTE;
    while !call.is_finished() && b.shared.compaction_waits.load(Ordering::Relaxed) == waits {
        assert!(
            Instant::now() < deadline,
            "set_retention neither returned nor waited within a minute"
        );
        thread::yield_now();
    }
    call
}

/// THE RULES CHANGE BETWEEN COMPACTIONS, NEVER INSIDE ONE: rules set while a tick's
/// compaction is in its unlocked half (its held frames written, its copy held at the seam's
/// gate) wait for it to land, and only then append their own frame, after the job's. So the
/// unread mail the tick carried below its cut is held whole across a restart, at its own
/// offset. NC: `set_retention` without the compaction lock appends its rules frame where
/// the job's frames are, the store's length runs past its file, and after the restart the
/// carried mail is gone.
#[test]
fn rules_set_while_a_tick_compacts_wait_for_it_and_keep_what_it_carried() {
    let root = Scratch::new("tick-rules-race");
    let path = root.path().join("log");
    let b = Arc::new(Broker::open(&path).unwrap());
    b.set_retention_interval(HOUR);
    publish(&b, 0, MAIL);
    for seq in 1..60u64 {
        publish(&b, seq, EV);
    }
    let held = arm_gate(&b);
    b.set_retention(rules(20)).unwrap();
    assert!(held.wait(), "the tick's copy did not reach the gate");
    let set = rules_set_meanwhile(&b, rules(21));
    disarm(&b);
    held.resume();
    within_a_minute("the rules set meanwhile", move || set.join().unwrap()).unwrap();
    await_ticks(&b, "the gated tick's cut", |b| b.base() == 40);
    assert_eq!(b.stats().log.held_records, 1);
    drop(b);
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!(log.base(), Offset(40));
    assert_eq!(
        log.stats().held_records,
        1,
        "the carried mail survived the restart"
    );
    let mut cursor = 0u64;
    let read: Vec<(u64, String)> = log
        .read_chunk(&mut cursor, log.head().0, 10)
        .iter()
        .map(|r| (r.seq.0, r.subject.clone()))
        .collect();
    assert_eq!(
        read,
        vec![(0, MAIL.to_string())],
        "a subscriber from 0 reads it"
    );
}

/// RULES SET WHILE THE CAPS' TICK COPIES hold from the base that compaction lands, since
/// what its cut dropped no rule carried: a read of the mail below that base is told
/// `retained-from=` it. NC: `set_retention` without the compaction lock holds the rules from
/// the base before the cut, and a fetch of the mail from 0 answers an empty page, silently.
#[test]
fn rules_set_while_the_caps_compact_hold_from_the_base_that_compaction_lands() {
    let root = Scratch::new("tick-rules-caps");
    let path = root.path().join("log");
    let b = Arc::new(Broker::open(&path).unwrap());
    b.set_retention_interval(HOUR);
    publish(&b, 0, MAIL);
    for seq in 1..40u64 {
        publish(&b, seq, EV);
    }
    let held = arm_gate(&b);
    b.set_max_retained_records(10);
    assert!(held.wait(), "the caps' copy did not reach the gate");
    let set = rules_set_meanwhile(&b, rules(1000));
    disarm(&b);
    held.resume();
    within_a_minute("the rules set meanwhile", move || set.join().unwrap()).unwrap();
    // The caps' cut: half the record cap kept of the 40.
    await_ticks(&b, "the caps' cut", |b| b.base() == 35);
    let base = b.base();
    let mail = Filter::new("/f/F/in/>").unwrap();
    assert_eq!(
        b.oldest(&mail),
        base,
        "the rules hold from the base the cut landed"
    );
    let log = b.shared.log.lock().unwrap();
    let head = log.head().0;
    assert_eq!(
        log.fetch_checked(0, &mail, 10, 1000, head)
            .map(|(p, _)| p.len()),
        Err(Offset(base)),
        "a read of the mail below it is told"
    );
}

/// THE CAPS RUN THROUGH THE TICK: over `set_max_retained_records`, the writer asks for a
/// tick, which compacts carrying state off the ack path, so the log comes back within the
/// cap and a quiet subject's `Last` still answers from `<log>.state`. NC: a writer whose caps
/// never ask for a tick leaves the log uncut, and the wait fails.
#[cfg(unix)]
#[test]
fn automatic_state_carrying_compaction_caps_retained_records_and_preserves_state() {
    let root = Scratch::new("auto-retain");
    let log_path = root.path().join("auto.log");
    let sock_path = root.path().join("auto.sock");

    let b = Broker::open_with(&log_path, Durability::Relaxed).unwrap();
    // No interval inside the test: only the batches over the cap ask.
    b.set_retention_interval(HOUR);
    b.set_max_retained_records(20);
    assert_eq!(b.max_retained_records(), 20);
    let mut h = b.serve(&sock_path).unwrap();

    let mut c = crate::Client::connect(&sock_path).unwrap();
    // Publish a quiet subject at offset 0 that will fall below the compaction cut.
    c.publish(1, 1, "/t/quiet", b"sticky-state").unwrap();
    // Publish 40 noisy records so automatic compaction triggers repeatedly.
    for seq in 2..=41 {
        c.publish(1, seq, "/t/noisy", b"payload").unwrap();
    }
    c.commit("/g/consumers", 35).unwrap();

    await_ticks(&b, "the cap's cut", |b| {
        let s = b.stats();
        s.log.base.0 > 0 && s.log.retained_records <= 20
    });
    assert_eq!(b.stats().log.base.0, b.base());

    // Verify quiet subject's Last record survived compaction via `<log>.state`.
    let (rows, _) = c.last("/t/quiet", "", 10).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].1, "/t/quiet");
    assert_eq!(rows[0].2, b"sticky-state");

    h.shutdown();
}

/// THE CAPS ON A LOG WHOSE RULES WERE READ BACK (a broker given none since its open, which
/// compacts by its caps alone, planning nothing) keep what they dropped unnamed across a
/// restart: the mail at 0 goes with the cut to 2, and the cut's own held-store frame raises
/// the spill, so after a reopen a read of the mail answers from the cut, and a tail from 0
/// is still told the range (`HeldStore::unplanned_job`). NC: a caps compaction that writes
/// no held-store job reads the mail from 0 after the reopen.
#[test]
fn the_caps_on_read_back_rules_keep_what_they_dropped_unnamed_across_a_restart() {
    let root = Scratch::new("caps-read-back");
    let path = root.path().join("log");
    let mail = Filter::new("/f/F/in/>").unwrap();
    {
        let mut log = BrokerLog::open(&path).unwrap();
        log.set_retention(rules(100)).unwrap();
        for (seq, subject) in [MAIL, EV, EV].into_iter().enumerate() {
            log.publish(1, seq as u64 + 1, subject.into(), BODY.to_vec())
                .unwrap();
        }
    }
    let b = Broker::open(&path).unwrap();
    b.set_retention_interval(HOUR);
    assert_eq!(b.retention(), None, "read back, not retained by");
    b.set_max_retained_records(1);
    b.retention_tick_at(b.now_ms()).unwrap();
    assert_eq!(b.base(), 2, "the caps cut to the newest record");
    assert_eq!(b.oldest(&mail), 2);
    drop(b);
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!(
        log.oldest(&mail),
        Offset(2),
        "the spill the cut's frame raised, read back"
    );
    assert_eq!(
        log.gap_notice(&mail, 0, &mut crate::store::Told::at(0)),
        Some(crate::proto::Gap {
            from: 0,
            to: 2,
            records: None
        })
    );
}

/// THE TICK'S LIFE: a broker nothing retains starts no tick and never ticks, however much
/// it takes; the first rules start one; and shutdown joins it before the writer, so
/// nothing of the broker outlives it — unserved (`Broker`'s drop) or served (the last
/// listener's shutdown). NC: a tick started at every open, or one stop never joins.
#[test]
fn a_tick_starts_only_on_a_broker_something_retains_and_stops_before_the_writer() {
    let root = Scratch::new("tick-life");
    let b = Broker::open(root.path().join("plain")).unwrap();
    for seq in 0..20u64 {
        publish(&b, seq, EV);
    }
    assert!(
        b.shared.ticker.lock().unwrap().is_none(),
        "no rules, no tick"
    );
    let s = b.stats();
    assert_eq!(
        (s.retention_ticks, s.retention_skips, s.log.base.0),
        (0, 0, 0)
    );
    b.set_retention(rules(3)).unwrap();
    assert!(b.shared.ticker.lock().unwrap().is_some());
    let shared = Arc::clone(&b.shared);
    drop(b);
    assert_eq!(
        Arc::strong_count(&shared),
        1,
        "the tick's thread outlived the broker"
    );
    #[cfg(unix)]
    {
        let b = Broker::open(root.path().join("served")).unwrap();
        let mut h = b.serve(root.path().join("sock")).unwrap();
        b.set_max_retained_records(5);
        let shared = Arc::clone(&b.shared);
        drop(b);
        h.shutdown();
        drop(h);
        assert_eq!(
            Arc::strong_count(&shared),
            1,
            "the tick's thread outlived the last listener"
        );
    }
}
