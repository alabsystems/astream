//! Evidence for `broker.pipelining`: SINGLE-CONNECTION pipelining — one connection with
//! many publishes in flight — preserves ordering, durability, and exactly-once ingest.
//! The broker streams acks back IN ORDER on a cloned write half while it keeps reading,
//! so the in-flight publishes coalesce into group-commit fsyncs (one connection
//! saturates the writer) at the SAME `ack ⟹ fsync'd` guarantee. No sleeps.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{acks_owed, broker_refusal, Broker, Client, Durability, Pipelined, Tier};
use astream_wire::MAX_PAYLOAD_LEN;
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
fn single_connection_pipelined_publishes_ordered_durable_exactly_once() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspipe_t_{pid}_{n}.log");
    let sock = format!("/tmp/aspipe_t_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    const N: usize = 500;
    let owned: Vec<Vec<u8>> = (0..N).map(|i| format!("m{i}").into_bytes()).collect();
    let bodies: Vec<&[u8]> = owned.iter().map(|v| v.as_slice()).collect();

    {
        let b = Broker::open(&log).unwrap();
        let _h = b.serve(&sock).unwrap();

        let mut c = Client::connect(&sock).unwrap();
        // Many publishes in flight on ONE connection (window 128).
        let acks = c.publish_pipelined(1, "/a/p/x", &bodies, 128).unwrap();
        assert_eq!(acks.len(), N, "every pipelined publish acked");
        for (i, (off, deduped)) in acks.iter().enumerate() {
            assert_eq!(*off, i as u64, "acks stream back in request order");
            assert!(!deduped, "a first send is never a dup");
        }
        // Re-pipeline the SAME (producer_id, seqs): exactly-once ingest → every one is
        // deduped to its ORIGINAL offset and nothing is re-appended, even pipelined.
        let acks2 = c.publish_pipelined(1, "/a/p/x", &bodies, 128).unwrap();
        for (i, (off, deduped)) in acks2.iter().enumerate() {
            assert_eq!(
                (*off, *deduped),
                (i as u64, true),
                "pipelined re-send is deduped to the original offset"
            );
        }
        // Subscribe on the SAME connection: drives the finish-pipeline transition (flush
        // all pending acks, reclaim the socket, then stream). Records arrive in dense
        // offset order [0, N).
        let mut sub = c.subscribe(0, "/a/p/>").unwrap();
        for (i, body) in owned.iter().enumerate() {
            let (off, _s, got) = sub.recv().unwrap().unwrap();
            assert_eq!(off, i as u64, "delivered in offset order");
            assert_eq!(&got, body, "body intact");
        }
    } // drop handle → shutdown

    // Restart: every pipelined-and-acked record is durable and re-delivered in order.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/p/>")
        .unwrap();
    for i in 0..N {
        let (off, _s, _b) = sub.recv().unwrap().unwrap();
        assert_eq!(off, i as u64, "all {N} recovered after restart, in order");
    }
}

/// Regression: a producer connection that publishes then sits IDLE (its read half
/// parked in the broker, plus a spawned ack-writer thread) must be force-reaped on
/// broker shutdown — not left hanging until the client happens to act. The client is
/// deliberately kept ALIVE across shutdown; if shutdown failed to close the connection
/// socket, the broker's acceptor/writer join could stall and this test would hang.
#[test]
fn shutdown_reaps_an_idle_pipelined_connection() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspipe_sd_{pid}_{n}.log");
    let sock = format!("/tmp/aspipe_sd_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    // A producer connection that publishes (starting its ack-writer) then idles.
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/a/p/x", b"hello").unwrap();
    // Do NOT drop `c`: the connection stays open and idle. shutdown() must still return
    // promptly by force-closing the socket (reaping the read + ack-writer threads).
    h.shutdown();
    // Reaching here means shutdown did not hang on the live idle connection.
    drop(c);
}

/// A fresh log and socket path under `/tmp`, removed (with their sidecars) when the
/// returned guard drops.
fn scratch(tag: &str) -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspipe_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/aspipe_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&log, &sock]);
    (tmp, log, sock)
}

/// The writer's batches so far, and its flushes as `(barrier, full)`.
fn spent(b: &Broker) -> (u64, (u64, u64)) {
    let f = b.flush_counts();
    (b.stats().writer_batches, (f.barrier, f.full))
}

/// One batch's flush on the tier `b` serves: a barrier on Ordered, a full flush on
/// Strict (and on Ordered asked for where it is served Strict).
fn one_flush(b: &Broker) -> (u64, u64) {
    match b.served_durability().served {
        Tier::Ordered => (1, 0),
        _ => (0, 1),
    }
}

/// A broker at `durability` served on `sock`, and a client connected to it — guarded,
/// with a capability over `/a/>` attached, when `guarded`.
fn served(
    log: &str,
    sock: &str,
    durability: Durability,
    guarded: bool,
) -> (Broker, astream_broker::BrokerHandle, Client) {
    #[cfg(feature = "cap")]
    const SECRET: &[u8] = b"pipeline-one-batch-secret";
    let b = if guarded {
        #[cfg(feature = "cap")]
        {
            Broker::open_guarded_with(log, SECRET.to_vec(), durability).unwrap()
        }
        #[cfg(not(feature = "cap"))]
        unreachable!("a guarded broker needs the `cap` feature")
    } else {
        Broker::open_with(log, durability).unwrap()
    };
    let h = b.serve(sock).unwrap();
    #[cfg_attr(not(feature = "cap"), allow(unused_mut))]
    let mut c = Client::connect(sock).unwrap();
    if guarded {
        #[cfg(feature = "cap")]
        {
            let cap = astream_broker::mint(SECRET, "/a/>").unwrap();
            c.attach(&cap.filter, &cap.tag).unwrap();
        }
    }
    (b, h, c)
}

/// The guarded broker joins the run only where the `cap` feature builds one.
fn guards() -> &'static [bool] {
    if cfg!(feature = "cap") {
        &[false, true]
    } else {
        &[false]
    }
}

/// **WHAT A CLIENT WRITES TOGETHER LANDS IN ONE BATCH, WITH ONE FLUSH.** A publish and a
/// commit sent as one [`Client::send_pipelined`] burst are one group-commit batch and one
/// flush — on Ordered one barrier, on Strict one full flush — every time, on a guarded
/// broker as on an unguarded one: the connection's reader hands the writer the writes it
/// finds already received whole as one run, so the writer never sees the publish alone.
/// The acks come back in burst order, the commit's record right behind the publish's.
///
/// Before the run, the reader queued each op as it decoded it: measured on an idle
/// Ordered broker, such a pair took two batches in 989 of 1,000 tries guarded (the
/// reader checks each request against its keyring while the woken writer takes the
/// publish alone) and 8 of 1,000 unguarded. Twenty rounds of each make a reader that
/// queues op by op fail here, which takes the guarded rounds: they run only under
/// `--features cap` ([`guards`]), as the `broker.pipelining` claim runs this; the
/// negative control below shows the counters tell one batch from two.
#[test]
fn a_publish_and_a_commit_written_together_share_one_batch_and_one_flush() {
    for durability in [Durability::Strict, Durability::Ordered { horizon: None }] {
        for &guarded in guards() {
            let (_tmp, log, sock) = scratch("burst");
            let (b, _h, mut c) = served(&log, &sock, durability, guarded);
            let one = one_flush(&b);
            let mut upto = 0;
            for seq in 1..=20u64 {
                let before = spent(&b);
                c.send_pipelined(&[
                    Pipelined::Publish {
                        producer_id: 7,
                        producer_seq: seq,
                        subject: "/a/p/x",
                        body: b"hello",
                    },
                    Pipelined::Commit {
                        group: "/a/g",
                        upto,
                    },
                ])
                .unwrap();
                assert_eq!(c.owed_acks(), 2, "one ack owed per op of the burst");
                let (published, deduped) = c.recv_publish_ack().unwrap();
                assert!(!deduped);
                let (committed, _) = c.recv_publish_ack().unwrap();
                assert_eq!(committed, published + 1, "acked in burst order");
                let after = spent(&b);
                assert_eq!(
                    (
                        after.0 - before.0,
                        (after.1 .0 - before.1 .0, after.1 .1 - before.1 .1)
                    ),
                    (1, one),
                    "{durability:?} guarded={guarded} round {seq}: one batch and one flush \
                     for the publish and the commit written together"
                );
                upto = published;
            }
        }
    }
}

/// NEGATIVE CONTROL: the same publish and commit written APART, with the writer held
/// inside the publish's batch until the commit is on the wire, are two batches and two
/// flushes — so the counters the test above reads do tell one batch from two.
#[test]
fn a_publish_and_a_commit_written_apart_around_a_batch_are_two() {
    for &guarded in guards() {
        let (_tmp, log, sock) = scratch("apart");
        let (b, _h, mut c) = served(&log, &sock, Durability::Ordered { horizon: None }, guarded);
        let (barrier, full) = one_flush(&b);
        let before = spent(&b);
        let pause = b.pause_next_write();
        c.send_publish(7, 1, "/a/p/x", b"hello").unwrap();
        assert!(pause.wait(), "the publish's batch is held at its write");
        c.send_commit("/a/g", 0).unwrap();
        pause.resume();
        let (published, _) = c.recv_publish_ack().unwrap();
        let (committed, _) = c.recv_publish_ack().unwrap();
        assert_eq!(committed, published + 1);
        let after = spent(&b);
        assert_eq!(
            (
                after.0 - before.0,
                (after.1 .0 - before.1 .0, after.1 .1 - before.1 .1)
            ),
            (2, (2 * barrier, 2 * full)),
            "guarded={guarded}: two batches and two flushes"
        );
    }
}

/// **A BURST OWES ONE ACK PER OP, IN BURST ORDER, AND A REFUSAL PAYS ITS OWN.** A burst of
/// three publishes and a commit, the second publish to a malformed subject: four acks
/// are owed, a request that reads its own reply is refused with `AcksOwed` meanwhile,
/// and the acks read back in burst order — the refusal where the bad publish's ack
/// would be, the client still in step — after which a fetch sees exactly the two
/// records that landed and the commit.
#[test]
fn a_burst_owes_an_ack_per_op_in_order_and_a_refusal_pays_its_own() {
    let (_tmp, log, sock) = scratch("owed");
    let (_b, _h, mut c) = served(&log, &sock, Durability::Strict, false);
    c.send_pipelined(&[
        Pipelined::Publish {
            producer_id: 7,
            producer_seq: 1,
            subject: "/a/p/a",
            body: b"a",
        },
        Pipelined::Publish {
            producer_id: 7,
            producer_seq: 2,
            subject: "/a/p//bad",
            body: b"b",
        },
        Pipelined::Commit {
            group: "/a/g",
            upto: 0,
        },
        Pipelined::Publish {
            producer_id: 7,
            producer_seq: 3,
            subject: "/a/p/c",
            body: b"c",
        },
    ])
    .unwrap();
    assert_eq!(c.owed_acks(), 4);
    let refused = c.fetch(0, "/a/p/*", 16).unwrap_err();
    assert_eq!(
        acks_owed(&refused).map(|o| o.owed),
        Some(4),
        "nothing reads past the burst's acks: {refused}"
    );
    let (a, _) = c.recv_publish_ack().unwrap();
    let bad = c.recv_publish_ack().unwrap_err();
    assert!(
        broker_refusal(&bad).is_some(),
        "the bad publish's own refusal, in its place: {bad}"
    );
    let (commit, _) = c.recv_publish_ack().unwrap();
    let (cc, _) = c.recv_publish_ack().unwrap();
    assert_eq!(
        (a, commit, cc),
        (0, 1, 2),
        "in burst order, the refused one taking no offset"
    );
    assert_eq!(c.owed_acks(), 0);
    let (rows, _) = c.fetch(0, "/a/p/*", 16).unwrap();
    assert_eq!(
        rows.iter()
            .map(|(off, s, _)| (*off, s.as_str()))
            .collect::<Vec<_>>(),
        [(0, "/a/p/a"), (2, "/a/p/c")],
        "in step: the fetch reads records, not a stray ack"
    );
}

/// **A BURST IS BUILT WHOLE BEFORE A BYTE IS WRITTEN.** A burst whose second publish is
/// over the frame cap is refused before anything goes out: nothing is owed, nothing
/// lands — not even the first publish, which fits — and the client is in step for the
/// next request. An empty burst writes nothing and owes nothing.
#[test]
fn a_burst_with_an_op_over_the_cap_is_refused_whole_and_owes_nothing() {
    let (_tmp, log, sock) = scratch("cap");
    let (_b, _h, mut c) = served(&log, &sock, Durability::Strict, false);
    let huge = vec![0u8; MAX_PAYLOAD_LEN + 1];
    c.send_pipelined(&[
        Pipelined::Publish {
            producer_id: 7,
            producer_seq: 1,
            subject: "/a/p/a",
            body: b"fits",
        },
        Pipelined::Publish {
            producer_id: 7,
            producer_seq: 2,
            subject: "/a/p/b",
            body: &huge,
        },
    ])
    .unwrap_err();
    assert_eq!(c.owed_acks(), 0, "refused whole: nothing owed");
    c.send_pipelined(&[]).unwrap();
    assert_eq!(c.owed_acks(), 0, "an empty burst owes nothing");
    let (at, deduped) = c.publish(7, 1, "/a/p/a", b"fits").unwrap();
    assert_eq!(
        (at, deduped),
        (0, false),
        "in step, and the first publish of the refused burst never landed"
    );
}
