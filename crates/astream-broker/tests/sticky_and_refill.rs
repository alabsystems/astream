// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Integration tests for opt-in sticky producer gap fencing on refused batches
//! (`DESIGN-aterm-fabric` §14 Open Question 7 & §15; `Astream.Broker.TlaStickyBatchFence`)
//! and multi-lane coalesced refill planning & cost-bounded handoff
//! (`aterm-link` B09 `inbox-delivery-accounting`; `Astream.Broker.TlaSharedRefill`).

#![cfg(unix)]

use std::sync::atomic::{AtomicU64, Ordering};

use astream_broker::{
    broker_refusal, parse_gap_fenced_seq, Broker, Client, Durability, InjectedFaults, OpenOptions,
    Pipelined, Prepared, RateLimit, RefillStep, SharedRefillMeter, SharedRefillPlan,
    DEFAULT_REFILL_SPLIT_SLACK, GAP_FENCED_PREFIX, REFILL_ROW_COST,
};

static NEXT_ID: AtomicU64 = AtomicU64::new(1);

fn temp_paths(tag: &str) -> (std::path::PathBuf, std::path::PathBuf, std::path::PathBuf) {
    let n = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::path::PathBuf::from(format!("/tmp/asb-sr-{tag}-{pid}-{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let log = dir.join("b.log");
    let sock = dir.join("b.sock");
    (dir, log, sock)
}

#[test]
fn sticky_batch_refusal_blocks_pipelined_successors_after_rate_limit_and_clears_on_retry() {
    let (dir, log, sock) = temp_paths("rl");
    // Rate limit: burst of 1 record (1 record/sec) so seq=1 commits and seq=2 is refused
    // inside the same 3-frame pipelined burst (`PreRefused` path).
    let limit = RateLimit::records(1, 1).unwrap();
    let opts = OpenOptions::new(Durability::Relaxed)
        .with_rate_limit(limit)
        .with_sticky_batch_refusal(true);
    let broker = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
    assert!(broker.sticky_batch_refusal());
    let mut handle = broker.serve(&sock).unwrap();

    let mut c = Client::connect(&sock).unwrap();
    assert!(c.fence_gaps().unwrap(), "the connection asks to be fenced");
    c.send_pipelined(&[
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 1,
            subject: "/f/f1/pub/n-1/ev/1",
            body: b"m1",
        },
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 2,
            subject: "/f/f1/pub/n-1/ev/2",
            body: b"m2",
        },
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 3,
            subject: "/f/f1/pub/n-1/ev/3",
            body: b"m3",
        },
    ])
    .unwrap();

    // seq=1 lands at offset 0.
    assert_eq!(c.recv_publish_ack().unwrap(), (0, false));
    // seq=2 is throttled (`rate-limited`), latching `fence_seq = 2`.
    let e2 = c.recv_publish_ack().unwrap_err();
    let r2 = broker_refusal(&e2).expect("seq=2 broker refusal");
    assert!(r2.is_rate_limited(), "expected rate-limited, got {r2:?}");
    // seq=3 in the same burst is refused with `gap-fenced=2:`!
    let e3 = c.recv_publish_ack().unwrap_err();
    let r3 = broker_refusal(&e3).expect("seq=3 broker refusal");
    assert!(
        r3.msg.starts_with(GAP_FENCED_PREFIX),
        "expected gap-fenced prefix, got {:?}",
        r3.msg
    );
    assert_eq!(parse_gap_fenced_seq(&r3.msg), Some(2));
    assert_eq!(broker.head(), 1);

    // Clear the rate limit so a later batch could otherwise commit: seq=4 MUST STILL be
    // refused by the sticky fence because seq=2 has not been retried yet!
    broker.set_rate_limit(None).unwrap();
    let e4 = c.publish(77, 4, "/f/f1/pub/n-1/ev/4", b"m4").unwrap_err();
    let r4 = broker_refusal(&e4).expect("seq=4 broker refusal");
    assert_eq!(parse_gap_fenced_seq(&r4.msg), Some(2));
    assert_eq!(broker.head(), 1);

    // Another producer on the SAME connection is NOT fenced!
    assert_eq!(
        c.publish(88, 9, "/f/f1/pub/n-2/ev/9", b"other").unwrap(),
        (1, false)
    );

    // Now producer 77 retries from seq=2 (`[2, 3, 4]` pipelined together): seq=2 clears
    // the fence and all three land in strict send order at offsets `2, 3, 4`!
    c.send_pipelined(&[
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 2,
            subject: "/f/f1/pub/n-1/ev/2",
            body: b"m2",
        },
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 3,
            subject: "/f/f1/pub/n-1/ev/3",
            body: b"m3",
        },
        Pipelined::Publish {
            producer_id: 77,
            producer_seq: 4,
            subject: "/f/f1/pub/n-1/ev/4",
            body: b"m4",
        },
    ])
    .unwrap();
    assert_eq!(c.recv_publish_ack().unwrap(), (2, false));
    assert_eq!(c.recv_publish_ack().unwrap(), (3, false));
    assert_eq!(c.recv_publish_ack().unwrap(), (4, false));

    drop(c);
    handle.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn sticky_batch_refusal_fences_after_fsync_rollback_while_default_mode_stays_non_sticky() {
    // 1. Sticky mode (`true`): a Strict batch commit failure on seq=10 fences seq=11 on the
    //    following healthy batch until seq=10 is retried.
    let (dir, log, sock) = temp_paths("sync");
    let opts = OpenOptions::new(Durability::Strict).with_sticky_batch_refusal(true);
    let broker = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();

    let mut c = Client::connect(&sock).unwrap();
    assert!(c.fence_gaps().unwrap(), "the connection asks to be fenced");
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let e10 = c.publish(5, 10, "/f/f1/s/10", b"ten").unwrap_err();
    assert!(broker_refusal(&e10).is_some());
    broker.inject_faults(InjectedFaults::default());

    // Even with the disk healthy again, sending seq=11 before retrying seq=10 is gap-fenced!
    let e11 = c.publish(5, 11, "/f/f1/s/11", b"eleven").unwrap_err();
    let r11 = broker_refusal(&e11).unwrap();
    assert_eq!(parse_gap_fenced_seq(&r11.msg), Some(10));
    assert_eq!(broker.head(), 0);

    // Retrying seq=10 then seq=11 commits both cleanly in order!
    assert_eq!(c.publish(5, 10, "/f/f1/s/10", b"ten").unwrap(), (0, false));
    assert_eq!(
        c.publish(5, 11, "/f/f1/s/11", b"eleven").unwrap(),
        (1, false)
    );
    drop(c);
    handle.shutdown();
    let _ = std::fs::remove_dir_all(&dir);

    // 2. Default mode (`sticky_batch_refusal == false`): preserves existing non-sticky
    //    contract (`a_refused_batch_lands_the_publish_sent_after_it`).
    let (dir2, log2, sock2) = temp_paths("nonsticky");
    let broker2 = Broker::open(&log2).unwrap();
    assert!(!broker2.sticky_batch_refusal());
    let mut handle2 = broker2.serve(&sock2).unwrap();
    let mut c2 = Client::connect(&sock2).unwrap();
    assert!(
        !c2.fence_gaps().unwrap(),
        "a broker opened without the option keeps no fence, asked or not"
    );
    broker2.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let _ = c2.publish(5, 10, "/f/f1/s/10", b"ten").unwrap_err();
    broker2.inject_faults(InjectedFaults::default());
    assert_eq!(
        c2.publish(5, 11, "/f/f1/s/11", b"eleven").unwrap(),
        (0, false)
    );
    drop(c2);
    handle2.shutdown();
    let _ = std::fs::remove_dir_all(&dir2);
}

#[test]
fn shared_refill_executes_three_phase_coalesced_fetch_and_hands_on_under_unowed_load() {
    let (dir, log, sock) = temp_paths("refill");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    // Populate a realistic mixed node log:
    // - Offsets 0..10: early mail to s-1 (`< inbox_oldest = 10`).
    // - Offsets 10..420: 410 unowed mail rows to departed session `s-departed`!
    // - Offsets 420..425: 5 mail rows to active sessions `s-1` and `s-2`.
    let mut seq = 1u64;
    for i in 0..10u64 {
        c.publish(
            1,
            seq,
            "/f/f1/in/n-1/s-1/p-a/ask",
            format!("early-{i}").as_bytes(),
        )
        .unwrap();
        seq += 1;
    }
    let inbox_oldest = 10u64;
    for i in 0..410u64 {
        c.publish(
            1,
            seq,
            "/f/f1/in/n-1/s-departed/p-a/note",
            format!("unowed-{i}").as_bytes(),
        )
        .unwrap();
        seq += 1;
    }
    for i in 0..5u64 {
        let sess = if i % 2 == 0 { "s-1" } else { "s-2" };
        c.publish(
            1,
            seq,
            &format!("/f/f1/in/n-1/{sess}/p-a/task"),
            format!("live-{i}").as_bytes(),
        )
        .unwrap();
        seq += 1;
    }

    // Build 3-phase plan for (`s-1` at 3, `s-2` at 10) with `inbox_oldest = 10`.
    let plan = SharedRefillPlan::build(inbox_oldest, &[("s-1", 3), ("s-2", 10)]).unwrap();
    assert_eq!(plan.shared_from, Some(10));
    assert_eq!(plan.lanes[0].catch_up_until, Some(10));
    assert_eq!(plan.lanes[0].join_shared_at, 10);
    assert_eq!(plan.lanes[1].catch_up_until, None);

    // Phase 1: `s-1` catches up `[3..10)` on its own narrow filter.
    let mut s1_delivered: Vec<u64> = Vec::new();
    let (early_records, _) = c.fetch(3, "/f/f1/in/n-1/s-1/>", 64).unwrap();
    for (offset, _, _) in &early_records {
        if *offset < inbox_oldest {
            s1_delivered.push(*offset);
        }
    }
    assert_eq!(s1_delivered, vec![3, 4, 5, 6, 7, 8, 9]);

    // Phase 2: Shared coalesced read over `/f/f1/in/n-1/>` starting at `shared_from = 10`
    // with `max = 200` per page, metered by `SharedRefillMeter`.
    let mut meter = SharedRefillMeter::new(inbox_oldest, plan.shared_from.unwrap(), 65_536);
    let mut s2_delivered: Vec<u64> = Vec::new();
    let mut handoff_at: Option<u64> = None;
    loop {
        let (records, (next, head)) = c.fetch(meter.cursor(), "/f/f1/in/n-1/>", 200).unwrap();
        let mut unowed = 0u64;
        for (offset, subject, _) in &records {
            if subject.starts_with("/f/f1/in/n-1/s-1/") {
                s1_delivered.push(*offset);
            } else if subject.starts_with("/f/f1/in/n-1/s-2/") {
                s2_delivered.push(*offset);
            } else {
                unowed += 1;
            }
        }
        match meter.observe_page(next, head, unowed, 2) {
            RefillStep::Complete { .. } => break,
            RefillStep::Continue { .. } => {}
            RefillStep::HandOn { handoff_offset } => {
                handoff_at = Some(handoff_offset);
                break;
            }
        }
    }

    // 400 unowed rows (`400 * 192 = 76,800` minus `1 * 400` saved = `76,400 > 65,536`)
    // triggers `HandOn` at offset 410 (bounded within `DEFAULT_REFILL_SPLIT_SLACK / REFILL_ROW_COST + 200`)!
    let ho = handoff_at.expect("shared refill must hand on after 2 dense unowed pages");
    assert_eq!(ho, 410);
    assert!(meter.total_carried() <= DEFAULT_REFILL_SPLIT_SLACK / REFILL_ROW_COST + 200);

    // Phase 3: Remaining active lanes finish `[ho..head)` on their own narrow filters
    // without carrying the remaining `s-departed` rows!
    let (p_s1_records, _) = c.fetch(ho, "/f/f1/in/n-1/s-1/>", 64).unwrap();
    for (offset, _, _) in &p_s1_records {
        s1_delivered.push(*offset);
    }
    let (p_s2_records, _) = c.fetch(ho, "/f/f1/in/n-1/s-2/>", 64).unwrap();
    for (offset, _, _) in &p_s2_records {
        s2_delivered.push(*offset);
    }

    // Zero missed records and zero duplicates across all 3 phases!
    assert_eq!(s1_delivered, vec![3, 4, 5, 6, 7, 8, 9, 420, 422, 424]);
    assert_eq!(s2_delivered, vec![421, 423]);

    drop(c);
    handle.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}

/// Two publishes' answers, in send order.
type TwoAnswers = (std::io::Result<(u64, bool)>, std::io::Result<(u64, bool)>);

/// Write A on `c` with the broker's next batch failing its fsync and its answer held, then
/// B pipelined behind it with the disk healthy again, and read both answers: what a
/// producer that keeps two writes in flight meets when the first one's batch is refused
/// (aterm's `pipeline.rs` `a_refused_batch_lands_the_publish_sent_after_it`).
fn a_then_b_behind_a_refused_batch(broker: &Broker, c: &mut Client) -> TwoAnswers {
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let held = broker.pause_next_acks();
    c.send_pipelined(&[Pipelined::Publish {
        producer_id: 7,
        producer_seq: 1,
        subject: "/f/f1/order/a",
        body: b"a",
    }])
    .unwrap();
    assert!(held.wait(), "A's batch was tried and its answer is held");
    broker.inject_faults(InjectedFaults::default());
    c.send_pipelined(&[Pipelined::Publish {
        producer_id: 7,
        producer_seq: 2,
        subject: "/f/f1/order/b",
        body: b"b",
    }])
    .unwrap();
    held.resume();
    let a = c.recv_publish_ack();
    let b = c.recv_publish_ack();
    (a, b)
}

/// THE FENCE IS ANNOUNCED, AND ITS PRODUCER LIFTS IT (`broker.sticky-batch-refusal`'s
/// `Hello` half, `DESIGN-aterm-fabric` §14 Q7): a broker opened with
/// `sticky_batch_refusal` says so in `Hello`'s request set (`REQUEST_GAP_FENCES`), so a
/// producer knows before it keeps two ordered writes in flight that a refused one lets
/// nothing sent after it land; and once it has read every answer, `ClearGapFences` lifts the
/// fence on the connection without a reconnect, where a retry of the refused write is not
/// what comes next. The negative control is a broker opened without the option: no bit,
/// and B lands ahead of A's retry.
#[test]
fn sticky_batch_refusal_is_announced_in_hello_and_lifted_by_its_producer() {
    let (dir, log, sock) = temp_paths("hello");
    let opts = OpenOptions::new(Durability::Strict).with_sticky_batch_refusal(true);
    let broker = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    assert!(!c.supports_gap_fences(), "nothing is known before a Hello");
    c.log_identity().unwrap();
    assert!(c.supports_gap_fences(), "a fencing broker says so");
    assert!(c.fence_gaps().unwrap(), "and fences a connection that asks");

    let (a, b) = a_then_b_behind_a_refused_batch(&broker, &mut c);
    assert!(
        broker_refusal(&a.unwrap_err()).is_some(),
        "A's batch failed"
    );
    let b = b.unwrap_err();
    assert_eq!(
        broker_refusal(&b).map(|r| parse_gap_fenced_seq(&r.msg)),
        Some(Some(1)),
        "B, sent behind A, is fenced at A's sequence: {b}"
    );
    assert_eq!(broker.head(), 0, "nothing landed");

    // Every answer read: the producer lifts the fence, and B lands though A is not retried.
    assert!(c.clear_gap_fences().unwrap());
    assert_eq!(c.publish(7, 2, "/f/f1/order/b", b"b").unwrap(), (0, false));
    // A fence a later refusal sets is lifted the same way, and a lift with none standing
    // answers the same.
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    assert!(c.publish(7, 3, "/f/f1/order/c", b"c").is_err());
    broker.inject_faults(InjectedFaults::default());
    let fenced = c.publish(7, 4, "/f/f1/order/d", b"d").unwrap_err();
    assert_eq!(
        broker_refusal(&fenced).map(|r| parse_gap_fenced_seq(&r.msg)),
        Some(Some(3))
    );
    assert!(c.clear_gap_fences().unwrap());
    assert!(c.clear_gap_fences().unwrap());
    assert_eq!(c.publish(7, 4, "/f/f1/order/d", b"d").unwrap(), (1, false));

    // The offer holds for the broker's life: every later connection is told it.
    let mut later = Client::connect(&sock).unwrap();
    later.log_identity().unwrap();
    assert!(later.supports_gap_fences());
    drop((c, later));
    handle.shutdown();
    let _ = std::fs::remove_dir_all(&dir);

    // NEGATIVE CONTROL: opened without the option, the broker announces no fence, and B,
    // pipelined behind A's refused batch, lands; A's retry lands after it.
    // It refuses the ask, and the connection stays framed and unfenced.
    let (dir2, log2, sock2) = temp_paths("hello-off");
    let broker2 = Broker::open_opts(&log2, OpenOptions::new(Durability::Strict), || {
        Ok(Prepared::Nothing)
    })
    .unwrap();
    let mut handle2 = broker2.serve(&sock2).unwrap();
    let mut c2 = Client::connect(&sock2).unwrap();
    c2.log_identity().unwrap();
    assert!(
        !c2.supports_gap_fences(),
        "an unfenced broker announces none"
    );
    assert!(!c2.fence_gaps().unwrap(), "and refuses the ask");
    let (a, b) = a_then_b_behind_a_refused_batch(&broker2, &mut c2);
    assert!(
        broker_refusal(&a.unwrap_err()).is_some(),
        "A's batch failed"
    );
    let (b_at, _) = b.expect("B lands behind A's refused batch");
    let (a_at, _) = c2.publish(7, 1, "/f/f1/order/a", b"a").unwrap();
    assert!(a_at > b_at, "A was sent first and is on the log after B");
    assert!(c2.clear_gap_fences().unwrap(), "answered, clearing nothing");
    drop(c2);
    handle2.shutdown();
    let _ = std::fs::remove_dir_all(&dir2);
}

/// THE FENCE IS THE CONNECTION'S TO ASK FOR (`Request::FenceGaps`): on a broker opened with
/// `sticky_batch_refusal`, a connection that never asks is served as an unfenced broker
/// serves it. A client that predates the ask never lifts a fence either, so one refused
/// write it does not send again at its own sequence (a record it drops, or sends again at a
/// fresh one) would otherwise fence everything it writes after it on that connection, for
/// the connection's life (aterm's C12 review). Here B, pipelined behind A's refused batch on
/// an unasked connection, lands; A's retry lands after it; and a write the producer sends
/// next at a fresh sequence lands too, with no lift asked. The control is the same pair on a
/// connection of the same broker that asked: B is fenced at A's sequence.
#[test]
fn sticky_batch_refusal_fences_only_a_connection_that_asks() {
    let (dir, log, sock) = temp_paths("unasked");
    let opts = OpenOptions::new(Durability::Strict).with_sticky_batch_refusal(true);
    let broker = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.log_identity().unwrap();
    assert!(c.supports_gap_fences(), "the broker offers the fence");

    let (a, b) = a_then_b_behind_a_refused_batch(&broker, &mut c);
    assert!(
        broker_refusal(&a.unwrap_err()).is_some(),
        "A's batch failed"
    );
    let (b_at, _) = b.expect("B lands behind A's refused batch: the connection never asked");
    assert_eq!(
        c.publish(7, 3, "/f/f1/order/c", b"c").unwrap(),
        (b_at + 1, false),
        "a write at a fresh sequence lands with no lift asked"
    );
    let (a_at, _) = c.publish(7, 1, "/f/f1/order/a", b"a").unwrap();
    assert!(a_at > b_at, "A was sent first and is on the log after B");
    drop(c);

    // CONTROL: the same pair on a connection that asked, under another producer.
    let mut asked = Client::connect(&sock).unwrap();
    asked.log_identity().unwrap();
    assert!(asked.fence_gaps().unwrap());
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let held = broker.pause_next_acks();
    asked
        .send_pipelined(&[Pipelined::Publish {
            producer_id: 8,
            producer_seq: 1,
            subject: "/f/f1/order/x",
            body: b"x",
        }])
        .unwrap();
    assert!(held.wait(), "X's batch was tried and its answer is held");
    broker.inject_faults(InjectedFaults::default());
    asked
        .send_pipelined(&[Pipelined::Publish {
            producer_id: 8,
            producer_seq: 2,
            subject: "/f/f1/order/y",
            body: b"y",
        }])
        .unwrap();
    held.resume();
    assert!(broker_refusal(&asked.recv_publish_ack().unwrap_err()).is_some());
    let y = asked.recv_publish_ack().unwrap_err();
    assert_eq!(
        broker_refusal(&y).map(|r| parse_gap_fenced_seq(&r.msg)),
        Some(Some(1)),
        "Y, sent behind X on the connection that asked, is fenced at X's sequence: {y}"
    );
    drop(asked);
    handle.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}
