// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Empty held-tail steps release the log lock without ending a live tail or a
//! fork snapshot. All waits are hang detectors; cursor and delivery assertions
//! establish progress without a timing budget.

use super::*;
use crate::test_scratch::Scratch;
use crate::{Client, Event, Retention, Rule};

const HANG: Duration = Duration::from_secs(60);
const NOISE: usize = 2 * TAIL_CHUNK + 17;
const HELD_BODY: &[u8] = b"held match";
const RETAINED_BODY: &[u8] = b"retained match";
const LIVE_BODY: &[u8] = b"published while the empty chunk is paused";

struct Fixture {
    broker: Broker,
    handle: BrokerHandle,
    socket: std::path::PathBuf,
    held_match: u64,
    base: u64,
    _scratch: Scratch,
}

impl Fixture {
    fn new(selective: bool) -> Self {
        let scratch = Scratch::new("htw");
        let socket = scratch.path().join("sock");
        let broker = Broker::open_with(scratch.path().join("log"), Durability::Relaxed).unwrap();
        broker.set_retention_interval(Duration::from_secs(3600));
        broker.set_selective_tail_wake(selective);
        let handle = broker.serve(&socket).unwrap();
        let mut writer = client(&socket);
        let bodies = vec![&b"noise"[..]; NOISE];
        let acks = writer
            .publish_pipelined(1, "/held/other", &bodies, 64)
            .unwrap();
        assert_eq!(acks.len(), NOISE);
        for (offset, ack) in acks.into_iter().enumerate() {
            assert_eq!(ack, (offset as u64, false));
        }
        let held_match = NOISE as u64;
        assert_eq!(
            writer.publish(2, 1, "/held/mine", HELD_BODY).unwrap(),
            (held_match, false)
        );
        assert_eq!(
            writer.publish(2, 2, "/stream/mine", b"given up").unwrap(),
            (held_match + 1, false)
        );
        broker
            .set_retention(
                Retention::new(
                    vec![
                        Rule::prefix("/stream/>").unwrap().max_bytes(1),
                        Rule::hold("/held/>").unwrap().max_bytes(1 << 30),
                    ],
                    Rule::default_hold(),
                )
                .unwrap(),
            )
            .unwrap();
        broker.retention_tick_at(broker.now_ms()).unwrap();
        let base = held_match + 2;
        assert_eq!(broker.base(), base);
        assert_eq!(broker.stats().log.held_records, NOISE + 1);
        assert_eq!(
            writer.publish(2, 3, "/held/mine", RETAINED_BODY).unwrap(),
            (base, false)
        );
        Self {
            broker,
            handle,
            socket,
            held_match,
            base,
            _scratch: scratch,
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        self.handle.shutdown();
    }
}

fn client(socket: &std::path::Path) -> Client {
    let stream = std::os::unix::net::UnixStream::connect(socket).unwrap();
    stream.set_read_timeout(Some(HANG)).unwrap();
    stream.set_write_timeout(Some(HANG)).unwrap();
    Client::from_stream(stream)
}

#[test]
fn an_empty_held_tail_step_releases_the_lock_and_delivers_the_whole_tail() {
    for selective in [false, true] {
        let fixture = Fixture::new(selective);
        let (reached_tx, reached) = mpsc::channel();
        let (resume, resume_rx) = mpsc::channel();
        *fixture.broker.shared.tail_pause.lock().unwrap() = Some(TailPause {
            chunk: 64,
            at: PauseAt::FirstChunk,
            reached: reached_tx,
            resume: resume_rx,
        });
        // The wider filter includes the dropped prefix-rule record. Its range
        // is owed once, before delivery; the narrow filter has lost nothing.
        let filter = if selective { "/*/mine" } else { "/held/mine" };
        let mut sub = client(&fixture.socket).subscribe(0, filter).unwrap();
        assert_eq!(
            reached.recv_timeout(HANG).unwrap(),
            64,
            "the first chunk inspected only nonmatching held entries"
        );

        // This ack needs the broker's log lock. The tail is still paused until
        // after it arrives, proving that an empty advancing step releases it.
        let socket = fixture.socket.clone();
        let (acked_tx, acked) = mpsc::channel();
        let publisher = thread::spawn(move || {
            let result = client(&socket).publish(3, 1, "/held/mine", LIVE_BODY);
            let _ = acked_tx.send(result);
        });
        assert_eq!(
            acked.recv_timeout(HANG).unwrap().unwrap(),
            (fixture.base + 1, false)
        );
        publisher.join().unwrap();
        resume.send(()).unwrap();

        let expected = [
            (fixture.held_match, HELD_BODY),
            (fixture.base, RETAINED_BODY),
            (fixture.base + 1, LIVE_BODY),
        ];
        let mut delivered = 0usize;
        let mut gaps = 0usize;
        let mut last_mark = 0u64;
        loop {
            match sub.recv_event().unwrap().expect("live tail ended") {
                Event::Delivery {
                    offset,
                    subject,
                    body,
                } => {
                    assert!(delivered < expected.len(), "extra delivery at {offset}");
                    assert_eq!(subject, "/held/mine");
                    assert_eq!((offset, body.as_slice()), expected[delivered]);
                    assert_eq!(gaps, usize::from(selective), "gap must precede delivery");
                    delivered += 1;
                }
                Event::Gap(gap) => {
                    assert!(selective, "the narrow filter lost no records");
                    assert_eq!(delivered, 0, "gap must precede held delivery");
                    assert_eq!(gaps, 0, "the unchanged retention epoch is told once");
                    assert_eq!(
                        gap,
                        crate::proto::Gap {
                            from: 0,
                            to: fixture.base,
                            records: None,
                        }
                    );
                    gaps += 1;
                }
                Event::Mark {
                    next,
                    head,
                    durable,
                } => {
                    assert!(last_mark <= next && next <= head);
                    assert!(durable.is_some_and(|durable| durable <= head));
                    last_mark = next;
                    if next == fixture.base + 2 {
                        assert_eq!(head, next);
                        break;
                    }
                }
            }
        }
        assert_eq!(delivered, expected.len());
        assert_eq!(gaps, usize::from(selective));
        assert_eq!(fixture.broker.visible_head(), fixture.base + 2);
    }
}

#[test]
fn a_fork_crosses_empty_held_chunks_and_replaces_a_nonmatching_held_record() {
    let fixture = Fixture::new(false);
    let fork_at = 2 * TAIL_CHUNK as u64;
    assert!(fork_at < fixture.held_match);
    let replacement = &b"counterfactual held match"[..];
    let mut fork = client(&fixture.socket)
        .fork_subscribe(fork_at, "/held/mine", replacement, "/held/mine")
        .unwrap();
    let expected = [
        (fork_at, replacement),
        (fixture.held_match, HELD_BODY),
        (fixture.base, RETAINED_BODY),
    ];
    let mut delivered = 0usize;
    loop {
        match fork
            .recv_event()
            .unwrap()
            .expect("fork ended before its mark")
        {
            Event::Delivery {
                offset,
                subject,
                body,
            } => {
                assert!(
                    delivered < expected.len(),
                    "extra fork delivery at {offset}"
                );
                assert_eq!(subject, "/held/mine");
                assert_eq!((offset, body.as_slice()), expected[delivered]);
                delivered += 1;
            }
            Event::Mark {
                next,
                head,
                durable,
            } => {
                assert_eq!((next, head), (fixture.base + 1, fixture.base + 1));
                assert!(durable.is_some_and(|durable| durable <= head));
                break;
            }
            Event::Gap(gap) => panic!("a fork asks for no gap notices: {gap:?}"),
        }
    }
    assert_eq!(delivered, expected.len());
    assert_eq!(fixture.broker.visible_head(), fixture.base + 1);
}

#[test]
fn an_absent_exact_held_subject_skips_to_the_reopened_suffix_without_losing_its_gap() {
    use crate::BrokerLog;

    let scratch = Scratch::new("hte");
    let path = scratch.path().join("log");
    let socket = scratch.path().join("sock");
    let base;
    {
        let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
        log.set_retention(
            Retention::new(
                vec![
                    Rule::prefix("/stream/>").unwrap().max_bytes(1),
                    Rule::hold("/held/>").unwrap().max_bytes(1 << 30),
                ],
                Rule::default_hold(),
            )
            .unwrap(),
        )
        .unwrap();
        for seq in 0..257 {
            log.stage_publish(1, seq + 1, "/held/other".into(), b"noise".to_vec())
                .unwrap();
        }
        // The exact subject existed, then its prefix rule gave it up along
        // with later stream rows. Unrelated held rows remain below the base.
        for (seq, subject) in [
            (258, "/stream/mine"),
            (259, "/stream/later"),
            (260, "/stream/later"),
        ] {
            log.stage_publish(1, seq, subject.into(), b"given up".to_vec())
                .unwrap();
        }
        log.commit_batch().unwrap();
        log.retain_by_rules(1).unwrap();
        base = log.base().0;
        assert_eq!(base, 260);
        assert_eq!(log.stats().held_records, 257);
        assert_eq!(
            log.stage_publish(2, 1, "/stream/mine".into(), RETAINED_BODY.to_vec())
                .unwrap(),
            (Offset(base), false)
        );
        log.commit_batch().unwrap();
    }
    // Read-back rules are inactive, so no background rule tick can move this
    // exact retained suffix while the public subscription is being checked.
    let broker = Broker::open_with(&path, Durability::Relaxed).unwrap();
    let handle = broker.serve(&socket).unwrap();
    let fixture = Fixture {
        broker,
        handle,
        socket,
        held_match: 257,
        base,
        _scratch: scratch,
    };
    assert_eq!(fixture.broker.base(), base);
    assert_eq!(fixture.broker.stats().log.held_records, 257);
    let head = base + 1;
    assert_eq!(fixture.broker.visible_head(), head);
    let (reached_tx, reached) = mpsc::channel();
    let (resume, resume_rx) = mpsc::channel();
    *fixture.broker.shared.tail_pause.lock().unwrap() = Some(TailPause {
        chunk: 64,
        at: PauseAt::FirstChunk,
        reached: reached_tx,
        resume: resume_rx,
    });
    let mut sub = client(&fixture.socket)
        .subscribe(0, "/stream/mine")
        .unwrap();
    assert_eq!(
        reached.recv_timeout(HANG).unwrap(),
        head,
        "exact absence skips the unrelated held interval in the first step"
    );
    assert_eq!(
        sub.recv_event().unwrap(),
        Some(Event::Gap(crate::proto::Gap {
            from: 0,
            to: base,
            records: None,
        }))
    );
    assert_eq!(
        sub.recv_event().unwrap(),
        Some(Event::Delivery {
            offset: base,
            subject: "/stream/mine".into(),
            body: RETAINED_BODY.to_vec(),
        })
    );
    resume.send(()).unwrap();
    match sub
        .recv_event()
        .unwrap()
        .expect("tail ended before its mark")
    {
        Event::Mark {
            next,
            head: marked_head,
            durable,
        } => {
            assert_eq!((next, marked_head), (head, head));
            assert!(durable.is_some_and(|durable| durable <= marked_head));
        }
        other => panic!("expected a caught-up mark, got {other:?}"),
    }
    assert_eq!(fixture.broker.visible_head(), head);
}
