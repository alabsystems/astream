// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh publication stops a source-ordered run at its first refusal. The old
//! Publish contract remains idempotent and independent of this opt-in fence.

use super::*;
use crate::test_scratch::Scratch;
use crate::{Client, FreshPublish};

const HANG: Duration = Duration::from_secs(60);

fn fresh(seq: u64, body: &'static [u8]) -> WriteKind {
    WriteKind::FreshPublish {
        producer_id: 9,
        producer_seq: seq,
        subject: "/fresh/rows".into(),
        body: body.to_vec(),
    }
}

fn op(kind: WriteKind, fence: &Arc<AtomicBool>) -> (WriteOp, Receiver<AckResult>) {
    let (sender, receiver) = mpsc::channel();
    (
        WriteOp {
            kind,
            ack: AckSender {
                sender,
                fresh: Some(Arc::clone(fence)),
            },
            conn_id: None,
        },
        receiver,
    )
}

fn run(broker: &Broker, fence: &Arc<AtomicBool>, kinds: Vec<WriteKind>) -> Vec<AckResult> {
    let (ops, receivers): (Vec<_>, Vec<_>) = kinds.into_iter().map(|kind| op(kind, fence)).unzip();
    process_batch(&broker.shared, ops);
    receivers
        .into_iter()
        .map(|r| r.recv_timeout(HANG).unwrap())
        .collect()
}

fn code(result: &AckResult) -> u8 {
    result.as_ref().unwrap_err().0
}

fn bodies(broker: &Broker) -> Vec<Vec<u8>> {
    broker
        .shared
        .log
        .lock()
        .unwrap()
        .read_range(Offset::ZERO, 64)
        .into_iter()
        .filter(|r| r.subject == "/fresh/rows")
        .map(|r| r.body.clone())
        .collect()
}

#[test]
fn a_middle_collision_stops_the_suffix_in_the_same_and_later_runs() {
    let root = Scratch::new("fresh-middle");
    let path = root.path().join("log");
    let broker = Broker::open(&path).unwrap();
    assert_eq!(
        submit_blocking(&broker.shared, fresh(2, b"old B")),
        Ok((0, false))
    );
    let fence = Arc::new(AtomicBool::new(false));
    let got = run(
        &broker,
        &fence,
        vec![fresh(1, b"A"), fresh(2, b"B"), fresh(3, b"C")],
    );
    assert_eq!(got[0], Ok((1, false)));
    assert_eq!(code(&got[1]), crate::proto::ERR_FRESH_HELD);
    assert_eq!(code(&got[2]), crate::proto::ERR_FRESH_FENCED);
    assert_eq!(bodies(&broker), [b"old B".to_vec(), b"A".to_vec()]);
    assert_eq!(broker.head(), broker.durable_head());
    assert_eq!(
        code(&run(&broker, &fence, vec![fresh(4, b"later")])[0]),
        crate::proto::ERR_FRESH_FENCED
    );

    // A new connection can roll B and then publish C; an old connection's
    // already queued Arc remains fenced even after every reader drops its copy.
    let reconnected = Arc::new(AtomicBool::new(false));
    assert_eq!(
        run(
            &broker,
            &reconnected,
            vec![fresh(100, b"B"), fresh(101, b"C")]
        ),
        [Ok((2, false)), Ok((3, false))]
    );
    assert_eq!(
        bodies(&broker),
        [
            b"old B".to_vec(),
            b"A".to_vec(),
            b"B".to_vec(),
            b"C".to_vec()
        ]
    );
    broker.shutdown();
    drop(broker);
    let reopened = Broker::open(&path).unwrap();
    assert_eq!(
        bodies(&reopened),
        [
            b"old B".to_vec(),
            b"A".to_vec(),
            b"B".to_vec(),
            b"C".to_vec()
        ]
    );
    let after_reopen = Arc::new(AtomicBool::new(false));
    assert_eq!(
        code(&run(&reopened, &after_reopen, vec![fresh(2, b"old B")])[0]),
        crate::proto::ERR_FRESH_HELD
    );
    // Ordinary Publish still deduplicates the original key even with different bytes.
    assert_eq!(
        submit_blocking(
            &reopened.shared,
            WriteKind::Publish {
                producer_id: 9,
                producer_seq: 2,
                subject: "/fresh/rows".into(),
                body: b"different".to_vec(),
            }
        ),
        Ok((0, true))
    );
}

#[test]
fn queued_fresh_operations_keep_the_fence_after_the_connection_owner_drops() {
    let root = Scratch::new("fresh-owner-drop");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let fence = Arc::new(AtomicBool::new(false));
    let (a, a_result) = op(fresh(1, b"A"), &fence);
    let (b, b_result) = op(
        WriteKind::PreRefused {
            producer_id: 0,
            producer_seq: 0,
            err: refusal(ERR_BAD_SUBJECT, "bad B"),
        },
        &fence,
    );
    let (c, c_result) = op(fresh(3, b"C"), &fence);
    drop(fence); // exactly the ownership released when the connection ends
    process_batch(&broker.shared, vec![a, b, c]);
    assert_eq!(a_result.recv_timeout(HANG).unwrap(), Ok((0, false)));
    assert_eq!(code(&b_result.recv_timeout(HANG).unwrap()), ERR_BAD_SUBJECT);
    assert_eq!(
        code(&c_result.recv_timeout(HANG).unwrap()),
        crate::proto::ERR_FRESH_FENCED
    );
    assert_eq!(bodies(&broker), [b"A".to_vec()]);
}

#[test]
fn fresh_collisions_include_staged_and_predecessor_keys() {
    let root = Scratch::new("fresh-lineage");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let fence = Arc::new(AtomicBool::new(false));
    let got = run(
        &broker,
        &fence,
        vec![fresh(1, b"A"), fresh(1, b"A"), fresh(2, b"B")],
    );
    assert_eq!(got[0], Ok((0, false)));
    assert_eq!(code(&got[1]), crate::proto::ERR_FRESH_HELD);
    assert_eq!(code(&got[2]), crate::proto::ERR_FRESH_FENCED);

    broker.set_producer_lineage([(10, vec![9])]);
    let new = Arc::new(AtomicBool::new(false));
    let got = run(
        &broker,
        &new,
        vec![
            WriteKind::FreshPublish {
                producer_id: 10,
                producer_seq: 1,
                subject: "/fresh/rows".into(),
                body: b"inherited".to_vec(),
            },
            fresh(3, b"never"),
        ],
    );
    assert_eq!(code(&got[0]), crate::proto::ERR_FRESH_HELD);
    assert_eq!(code(&got[1]), crate::proto::ERR_FRESH_FENCED);
    assert_eq!(bodies(&broker), [b"A".to_vec()]);
}

#[test]
fn a_relay_admitted_before_fresh_staging_cannot_be_overlooked() {
    let root = Scratch::new("fresh-relay-order");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let fence = Arc::new(AtomicBool::new(false));
    let got = run(
        &broker,
        &fence,
        vec![
            WriteKind::Relay {
                producer_id: 9,
                producer_seq: 2,
                subject: "/fresh/rows".into(),
                body: b"old B".to_vec(),
            },
            fresh(1, b"A"),
            fresh(2, b"B"),
            fresh(3, b"C"),
        ],
    );
    assert!(got[0].is_ok());
    assert!(got[1].is_ok());
    assert_eq!(code(&got[2]), crate::proto::ERR_FRESH_HELD);
    assert_eq!(code(&got[3]), crate::proto::ERR_FRESH_FENCED);
    assert_eq!(bodies(&broker), [b"old B".to_vec(), b"A".to_vec()]);
}

#[test]
fn early_refusals_are_ordered_and_a_failed_flush_fences_the_next_run() {
    let root = Scratch::new("fresh-errors");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let fence = Arc::new(AtomicBool::new(false));
    let got = run(
        &broker,
        &fence,
        vec![
            fresh(1, b"A"),
            WriteKind::PreRefused {
                producer_id: 0,
                producer_seq: 0,
                err: refusal(ERR_UNAUTHORIZED, "test authority refused"),
            },
            fresh(2, b"B"),
        ],
    );
    assert_eq!(
        got[0],
        Ok((0, false)),
        "the later reader refusal must not overtake A"
    );
    assert_eq!(code(&got[1]), ERR_UNAUTHORIZED);
    assert_eq!(code(&got[2]), crate::proto::ERR_FRESH_FENCED);
    assert_eq!(bodies(&broker), [b"A".to_vec()]);

    let fresh_connection = Arc::new(AtomicBool::new(false));
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    assert!(run(&broker, &fresh_connection, vec![fresh(3, b"failed")])[0].is_err());
    assert!(fresh_connection.load(Ordering::Relaxed));
    let later = run(&broker, &fresh_connection, vec![fresh(4, b"later")]);
    assert!(later[0].is_err());
    if broker.shared.log.lock().unwrap().poisoned().is_some() {
        assert!(later[0]
            .as_ref()
            .unwrap_err()
            .1
            .starts_with(LOG_POISONED_PREFIX));
    } else {
        assert_eq!(code(&later[0]), crate::proto::ERR_FRESH_FENCED);
    }
    assert_eq!(broker.visible_head(), 1);
}

#[cfg(unix)]
fn client(socket: &Path) -> Client {
    let stream = UnixStream::connect(socket).unwrap();
    stream.set_read_timeout(Some(HANG)).unwrap();
    stream.set_write_timeout(Some(HANG)).unwrap();
    let mut client = Client::from_stream(stream);
    client.hello().unwrap();
    client
}

#[cfg(unix)]
fn item(seq: u64, body: &'static [u8]) -> FreshPublish<'static> {
    FreshPublish {
        producer_id: 9,
        producer_seq: seq,
        subject: "/fresh/rows",
        body,
    }
}

#[cfg(unix)]
#[test]
fn wire_fresh_collision_has_fifo_partial_success_and_ordinary_publish_is_unchanged() {
    let root = Scratch::new("fresh-wire");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut writer = client(&socket);
    assert!(writer.supports_fresh_publish());
    assert_eq!(
        writer.publish(9, 2, "/fresh/rows", b"old B").unwrap(),
        (0, false)
    );
    writer
        .send_fresh_pipelined(&[item(1, b"A"), item(2, b"B"), item(3, b"C")])
        .unwrap();
    assert_eq!(writer.recv_publish_ack().unwrap(), (1, false));
    let error = writer.recv_publish_ack().unwrap_err();
    assert!(error
        .get_ref()
        .and_then(|e| e.downcast_ref::<crate::BrokerRefusal>())
        .unwrap()
        .is_fresh_held());
    let error = writer.recv_publish_ack().unwrap_err();
    assert!(error
        .get_ref()
        .and_then(|e| e.downcast_ref::<crate::BrokerRefusal>())
        .unwrap()
        .is_fresh_fenced());
    assert_eq!(writer.owed_acks(), 0);
    assert_eq!(
        writer.publish(9, 2, "/fresh/rows", b"ignored").unwrap(),
        (0, true)
    );
    assert_eq!(bodies(&broker), [b"old B".to_vec(), b"A".to_vec()]);
    drop(writer);
    handle.shutdown();
}

#[cfg(unix)]
#[test]
fn malformed_and_invalid_subject_fresh_requests_fence_the_wire_suffix() {
    for malformed in [false, true] {
        let root = Scratch::new("fresh-wire-invalid");
        let socket = root.path().join("sock");
        let broker = Broker::open(root.path().join("log")).unwrap();
        let mut handle = broker.serve(&socket).unwrap();
        let mut wire = UnixStream::connect(&socket).unwrap();
        wire.set_read_timeout(Some(HANG)).unwrap();
        wire.set_write_timeout(Some(HANG)).unwrap();
        let request = |seq, subject: &str, body: &[u8]| Request::FreshPublish {
            producer_id: 9,
            producer_seq: seq,
            subject: subject.into(),
            body: body.to_vec(),
        };
        let mut bytes = Vec::new();
        crate::proto::append_frame(
            &mut bytes,
            &crate::proto::encode_request(&request(1, "/fresh/rows", b"A")),
        )
        .unwrap();
        let bad = if malformed {
            vec![PROTO_VERSION, 0x1A]
        } else {
            crate::proto::encode_request(&request(2, "not/a/subject", b"bad"))
        };
        crate::proto::append_frame(&mut bytes, &bad).unwrap();
        crate::proto::append_frame(
            &mut bytes,
            &crate::proto::encode_request(&request(3, "/fresh/rows", b"C")),
        )
        .unwrap();
        wire.write_all(&bytes).unwrap();
        let read = |wire: &mut UnixStream| {
            crate::proto::decode_response(&crate::proto::read_frame(wire).unwrap().unwrap())
                .unwrap()
        };
        assert!(matches!(
            read(&mut wire),
            Response::PublishAck {
                offset: 0,
                deduped: false
            }
        ));
        assert!(matches!(read(&mut wire), Response::Error { .. }));
        assert!(matches!(
            read(&mut wire),
            Response::Error {
                code: crate::proto::ERR_FRESH_FENCED,
                ..
            }
        ));
        assert_eq!(bodies(&broker), [b"A".to_vec()]);
        drop(wire);
        handle.shutdown();
    }
}

#[cfg(all(unix, feature = "cap"))]
#[test]
fn fresh_authorization_refusal_cannot_be_overtaken_by_an_authorized_successor() {
    let root = Scratch::new("fresh-cap");
    let socket = root.path().join("sock");
    let secret = b"fresh capability regression";
    let broker = Broker::open_guarded(root.path().join("log"), secret.to_vec()).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut writer = client(&socket);
    let grant = astream_cap::mint(secret, "rw:/fresh/rows").unwrap();
    writer.attach(&grant.filter, &grant.tag).unwrap();
    let denied = FreshPublish {
        subject: "/elsewhere",
        ..item(2, b"denied")
    };
    writer
        .send_fresh_pipelined(&[item(1, b"A"), denied, item(3, b"C")])
        .unwrap();
    assert_eq!(writer.recv_publish_ack().unwrap(), (0, false));
    let denied = writer.recv_publish_ack().unwrap_err();
    assert_eq!(
        crate::broker_refusal(&denied).unwrap().code,
        ERR_UNAUTHORIZED
    );
    let fenced = writer.recv_publish_ack().unwrap_err();
    assert!(crate::broker_refusal(&fenced).unwrap().is_fresh_fenced());
    assert_eq!(bodies(&broker), [b"A".to_vec()]);
    drop(writer);
    handle.shutdown();
}

#[cfg(unix)]
#[test]
fn a_rate_limited_fresh_row_fences_its_other_producers_successor() {
    let root = Scratch::new("fresh-rate");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut writer = client(&socket);
    // Every producer's burst is smaller than this record's byte charge, so
    // the refusal is deterministic and independent of the wall clock.
    broker
        .set_rate_limit(Some(
            RateLimit::records(1, 1).unwrap().with_bytes(1, 3).unwrap(),
        ))
        .unwrap();
    writer
        .send_fresh_pipelined(&[
            item(1, b"denied"),
            FreshPublish {
                producer_id: 10,
                producer_seq: 1,
                subject: "/x",
                body: b"",
            },
        ])
        .unwrap();
    assert!(
        crate::broker_refusal(&writer.recv_publish_ack().unwrap_err())
            .unwrap()
            .is_rate_limited()
    );
    assert!(
        crate::broker_refusal(&writer.recv_publish_ack().unwrap_err())
            .unwrap()
            .is_fresh_fenced()
    );
    assert_eq!(broker.head(), 0);
    drop(writer);
    handle.shutdown();
}

#[cfg(unix)]
#[test]
fn lost_success_replies_allow_only_the_documented_digest_replay() {
    let root = Scratch::new("fresh-lost-replies");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut writer = client(&socket);
    let gate = broker.pause_next_acks();
    writer
        .send_fresh_pipelined(&[item(1, b"A"), item(2, b"B")])
        .unwrap();
    assert!(
        gate.wait_at_most(HANG),
        "the broker committed before replying"
    );
    assert_eq!(bodies(&broker), [b"A".to_vec(), b"B".to_vec()]);
    drop(writer); // neither success was observed, so no source cursor can advance
    gate.resume();
    let mut retry = client(&socket);
    retry
        .send_fresh_pipelined(&[item(3, b"A"), item(4, b"B")])
        .unwrap();
    assert_eq!(retry.recv_publish_ack().unwrap(), (2, false));
    assert_eq!(retry.recv_publish_ack().unwrap(), (3, false));
    assert_eq!(
        bodies(&broker),
        [b"A".to_vec(), b"B".to_vec(), b"A".to_vec(), b"B".to_vec()]
    );
    drop(retry);
    handle.shutdown();
}

#[cfg(unix)]
#[test]
fn losing_the_collision_reply_still_cannot_publish_the_suffix_first() {
    let root = Scratch::new("fresh-lost-collision");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut writer = client(&socket);
    writer.publish(9, 2, "/fresh/rows", b"old B").unwrap();
    let gate = broker.pause_next_acks();
    writer
        .send_fresh_pipelined(&[item(1, b"A"), item(2, b"B"), item(3, b"C")])
        .unwrap();
    assert!(gate.wait_at_most(HANG));
    assert_eq!(bodies(&broker), [b"old B".to_vec(), b"A".to_vec()]);
    drop(writer);
    gate.resume();

    // The collision was never observed. As in scalar Mesh::publish, recovery
    // allocates new keys rather than inferring whether the old call succeeded.
    let mut retry = client(&socket);
    retry
        .send_fresh_pipelined(&[item(4, b"A"), item(5, b"B"), item(6, b"C")])
        .unwrap();
    assert_eq!(retry.recv_publish_ack().unwrap(), (2, false));
    assert_eq!(retry.recv_publish_ack().unwrap(), (3, false));
    assert_eq!(retry.recv_publish_ack().unwrap(), (4, false));
    assert_eq!(
        bodies(&broker),
        [
            b"old B".to_vec(),
            b"A".to_vec(),
            b"A".to_vec(),
            b"B".to_vec(),
            b"C".to_vec()
        ]
    );
    drop(retry);
    handle.shutdown();
}

/// A late quorum failure is distinct from a staging collision: B already exists
/// locally, but no success was observed. Its connection must still refuse a later
/// Fresh C after replication recovers, without poisoning ordinary publication.
#[cfg(unix)]
#[test]
fn a_fresh_quorum_refusal_fences_later_batches_while_the_log_remains_writable() {
    let root = Scratch::new("fresh-quorum-late");
    let socket = root.path().join("sock");
    let follower =
        Broker::open_replica_with(root.path().join("follower"), Durability::Relaxed).unwrap();
    let mut follower_handle = follower.serve_tcp("127.0.0.1:0").unwrap();
    let address = follower_handle.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated_with(
        root.path().join("leader"),
        &[address],
        1,
        Duration::from_millis(500),
    )
    .unwrap();
    let mut leader_handle = leader.serve(&socket).unwrap();
    let mut writer = client(&socket);

    writer.send_fresh_pipelined(&[item(1, b"A")]).unwrap();
    assert_eq!(writer.recv_publish_ack().unwrap(), (0, false));
    assert_eq!(leader.visible_head(), 1);

    // This holds the follower's actual append, not an invented NACK. The
    // leader's configured transport timeout makes this batch miss its quorum.
    let held = follower.pause_next_batch();
    writer.send_fresh_pipelined(&[item(2, b"B")]).unwrap();
    assert!(held.wait_at_most(HANG), "the follower reached B's batch");
    let failed = writer.recv_publish_ack().unwrap_err();
    let refused = crate::broker_refusal(&failed).unwrap();
    assert_eq!(refused.code, ERR_REFUSED);
    assert!(refused.msg.contains("quorum"), "{refused:?}");
    assert_eq!(writer.owed_acks(), 0);
    assert_eq!(leader.head(), 2, "B exists locally despite its failed ACK");
    assert_eq!(leader.visible_head(), 1, "B is not quorum-confirmed yet");
    held.resume();

    // C is in a later writer batch, after B's error was observed. The same
    // request also gives replication a chance to confirm its old backlog.
    writer.send_fresh_pipelined(&[item(3, b"C")]).unwrap();
    let fenced = writer.recv_publish_ack().unwrap_err();
    assert!(crate::broker_refusal(&fenced).unwrap().is_fresh_fenced());
    assert_eq!(leader.head(), 2, "the fenced batch must not append C");
    assert_eq!(bodies(&leader), [b"A".to_vec(), b"B".to_vec()]);

    // The failure did not poison the log, and Fresh's connection fence does
    // not alter ordinary Publish. A real success proves the quorum recovered.
    assert_eq!(
        writer.publish(9, 4, "/fresh/rows", b"D").unwrap(),
        (2, false)
    );
    assert_eq!(leader.visible_head(), 3);
    writer
        .send_fresh_pipelined(&[item(5, b"still fenced")])
        .unwrap();
    let fenced = writer.recv_publish_ack().unwrap_err();
    assert!(crate::broker_refusal(&fenced).unwrap().is_fresh_fenced());
    assert_eq!(leader.head(), 3);

    let mut reconnected = client(&socket);
    reconnected.send_fresh_pipelined(&[item(5, b"E")]).unwrap();
    assert_eq!(reconnected.recv_publish_ack().unwrap(), (3, false));
    let expected = [b"A".to_vec(), b"B".to_vec(), b"D".to_vec(), b"E".to_vec()];
    assert_eq!(bodies(&leader), expected);
    assert_eq!(bodies(&follower), expected);
    assert_eq!(leader.visible_head(), 4);
    drop(reconnected);
    drop(writer);
    leader_handle.shutdown();
    follower_handle.shutdown();
}

/// Ordered's full-flush window can acknowledge A while holding B and C. A
/// failure there must not report their success or let the next batch append D.
/// C was already staged beside B; this test does not claim it was never written.
#[cfg(all(unix, target_vendor = "apple"))]
#[test]
fn an_ordered_fresh_flush_failure_keeps_held_acks_and_blocks_the_next_batch() {
    let root = Scratch::new("fresh-ordered-late");
    let mut options = OpenOptions::new(Durability::Ordered { horizon: None });
    options.escalation =
        crate::Escalation::new([crate::Escalate::Subject("/fresh/escalated".into())]);
    let broker =
        Broker::open_opts(root.path().join("log"), options, || Ok(Prepared::Nothing)).unwrap();
    assert_eq!(broker.served_durability().served, crate::Tier::Ordered);
    // The full-flush handle captures this flag when the batch commits. Set it
    // before staging: Ordered's barrier ignores this full-sync-only fault.
    broker.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: false,
    });
    let fence = Arc::new(AtomicBool::new(false));
    let (a, a_ack) = op(fresh(1, b"A"), &fence);
    let (b, b_ack) = op(
        WriteKind::FreshPublish {
            producer_id: 9,
            producer_seq: 2,
            subject: "/fresh/escalated".into(),
            body: b"B".to_vec(),
        },
        &fence,
    );
    let (c, c_ack) = op(fresh(3, b"C"), &fence);
    let flush = broker.pause_next_flush();
    broker
        .shared
        .writes
        .send(Queued::Run(vec![a, b, c]))
        .unwrap();
    assert!(
        flush.wait_at_most(HANG),
        "the escalated batch owes a full flush"
    );
    assert_eq!(a_ack.try_recv(), Ok(Ok((0, false))));
    assert_eq!(b_ack.try_recv(), Err(mpsc::TryRecvError::Empty));
    assert_eq!(c_ack.try_recv(), Err(mpsc::TryRecvError::Empty));
    assert_eq!(broker.head(), 3);
    assert_eq!(broker.visible_head(), 1);
    assert!(broker.durable_head() <= 1);

    // Queue a later batch while the writer is held outside the log lock. The
    // earlier barrier succeeded; resuming now meets the armed full-flush fault.
    let (d, d_ack) = op(fresh(4, b"D"), &fence);
    broker.shared.writes.send(Queued::Op(d)).unwrap();
    flush.resume();
    for ack in [b_ack, c_ack] {
        let refused = ack.recv_timeout(HANG).unwrap().unwrap_err();
        assert_eq!(refused.0, ERR_REFUSED);
        assert!(refused.1.contains("durability flush failed"), "{refused:?}");
    }
    let later = d_ack.recv_timeout(HANG).unwrap().unwrap_err();
    assert_eq!(later.0, ERR_REFUSED);
    assert!(later.1.starts_with(LOG_POISONED_PREFIX), "{later:?}");
    assert_eq!(broker.head(), 3, "the next batch did not append D");
    let rows: Vec<_> = broker
        .shared
        .log
        .lock()
        .unwrap()
        .read_range(Offset::ZERO, 64)
        .into_iter()
        .map(|r| (r.subject.clone(), r.body.clone()))
        .collect();
    assert_eq!(
        rows,
        [
            ("/fresh/rows".to_string(), b"A".to_vec()),
            ("/fresh/escalated".to_string(), b"B".to_vec()),
            ("/fresh/rows".to_string(), b"C".to_vec()),
        ]
    );
    assert_eq!(broker.visible_head(), 1);

    // Ordinary publication keeps the existing poisoned-log contract too: the
    // shared failure is not misreported as a Fresh-only collision or fence.
    let ordinary = submit_blocking(
        &broker.shared,
        WriteKind::Publish {
            producer_id: 9,
            producer_seq: 5,
            subject: "/fresh/rows".into(),
            body: b"ordinary".to_vec(),
        },
    )
    .unwrap_err();
    assert_eq!(ordinary.0, ERR_REFUSED);
    assert!(ordinary.1.starts_with(LOG_POISONED_PREFIX), "{ordinary:?}");
    assert_eq!(broker.head(), 3);
    broker.inject_faults(InjectedFaults::default());
    broker.shutdown();
}
