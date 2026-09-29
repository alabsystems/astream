//! Evidence for `broker.replicated-tier`: the REPLICATED point on the durability dial.
//! A leader broker (local page-cache write, no fsync) ships every committed record to
//! follower brokers over TCP at its EXACT leader offset, and an `ack` is gated on the
//! quorum watermark — a quorum of followers holding the record — so an acked record
//! survives the loss of the leader node (a follower holds it in memory), though not a
//! full-cluster power loss. The dial's middle setting (Kafka's default posture:
//! durability from replicas, not fsync).
//!
//! Each test here FAILS on an ack-before-replicate or a vacuous-quorum implementation:
//! 1. the ack waited for the replica (the follower's head has already advanced when
//!    the ack returns — read in-process, without blocking), and the follower serves
//!    everything at the same offsets after the leader is gone;
//! 2. a follower that never answers ⟹ the ack is an ERROR, the record is NOT visible to
//!    a leader-side subscriber, and an idempotent RETRY (and a pure commit) are ALSO
//!    errors — a deduped retry is never acked as replicated — until a follower is back,
//!    whereupon the retry is acked (deduped) and the record delivered;
//! 3. commit records and annotations replicate at the SAME offsets, so a consumer group
//!    resumes on the follower;
//! 4. a dropped follower link is re-dialed and the follower caught up automatically;
//! 5. with a follower down (even at open) the leader keeps serving on an honest quorum
//!    count, a quorum that could never be met is refused at open, and a late follower
//!    is caught up from offset 0;
//! 6. a follower that lost its tail is re-shipped from scratch; one whose log DIVERGED
//!    is fenced and never counts toward the quorum, while a TRANSIENT refusal (the
//!    follower at its connection cap, an I/O error, a poisoned log) is NOT a fence —
//!    the next batch ships again and the follower catches up;
//! 7. shutdown does not hang on a follower that never answers;
//! 8. a follower-less "replicated" broker is refused.
//!
//! No sleeps: every step synchronizes on an ack, a delivery, a signal, or the
//! leader's bounded follower I/O timeout.

#![cfg(unix)] // serves the leader on a Unix-domain socket; std has no UDS on Windows

use astream_broker::proto::{
    decode_request, decode_response, encode_request, encode_response, read_frame, write_frame,
};
use astream_broker::{Broker, Client, Request, Response};
use std::collections::VecDeque;
use std::io::Read;
use std::net::{TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

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

/// Unique short paths (/tmp keeps the socket under the sun_path limit), and the guard
/// that removes them.
fn paths(tag: &str) -> (Cleanup, String, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let flog = format!("/tmp/asrep_{tag}_f_{pid}_{n}.log");
    let llog = format!("/tmp/asrep_{tag}_l_{pid}_{n}.log");
    let lsock = format!("/tmp/asrep_{tag}_l_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&flog);
    let _ = std::fs::remove_file(&llog);
    (Cleanup::new(&[&flog, &llog, &lsock]), flog, llog, lsock)
}

/// A loopback address nobody listens on (bound, read, released).
fn free_port_addr() -> String {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    l.local_addr().unwrap().to_string()
}

/// The bound on a single follower round-trip in these tests: long enough that a real
/// follower (an in-process broker, fsync per batch) never trips it, short enough that a
/// follower that never answers fails a batch quickly.
const FOLLOWER_TIMEOUT: Duration = Duration::from_millis(400);

/// A "follower" that is reachable but NEVER answers: a TCP listener that accepts every
/// connection, reads one byte from it (signalling `got_bytes` — the leader's frame has
/// arrived and the leader is now parked waiting for an ack), and then holds the socket
/// open without ever writing. Models a wedged replica / a black-holed path.
struct SilentFollower {
    addr: String,
    stop: Arc<AtomicBool>,
    acceptor: Option<JoinHandle<()>>,
    got_bytes: Receiver<()>,
}

impl SilentFollower {
    fn start() -> SilentFollower {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let stop = Arc::new(AtomicBool::new(false));
        let (tx, got_bytes) = mpsc::channel();
        let flag = stop.clone();
        let acceptor = thread::spawn(move || {
            // Blocking accept; `stop()` unblocks it with one last self-connect.
            while let Ok((mut s, _)) = listener.accept() {
                if flag.load(Ordering::Relaxed) {
                    break;
                }
                let tx = tx.clone();
                thread::spawn(move || {
                    let mut b = [0u8; 1];
                    if matches!(s.read(&mut b), Ok(1)) {
                        let _ = tx.send(());
                    }
                    // Hold the socket open, never answering, until the peer closes.
                    let mut sink = [0u8; 64];
                    while matches!(s.read(&mut sink), Ok(n) if n > 0) {}
                });
            }
        });
        SilentFollower {
            addr,
            stop,
            acceptor: Some(acceptor),
            got_bytes,
        }
    }

    /// Stop listening (the port is released for a real follower to bind). Idempotent.
    fn stop(&mut self) {
        if let Some(a) = self.acceptor.take() {
            self.stop.store(true, Ordering::Relaxed);
            let _ = TcpStream::connect(&self.addr); // unblock accept()
            let _ = a.join();
        }
    }
}

impl Drop for SilentFollower {
    fn drop(&mut self) {
        self.stop();
    }
}

/// A follower that speaks the replication protocol itself, so a test can SCRIPT the
/// refusals a real broker returns. Each `Replicate` is answered with the next queued
/// error message while `script` is non-empty; otherwise it is handled the way a real
/// follower would (in order → acked; already held → acked deduped; beyond its head →
/// `replica gap`). `head` is how many leader records it holds.
struct ScriptedFollower {
    addr: String,
    script: Arc<Mutex<VecDeque<String>>>,
    head: Arc<AtomicU64>,
    stop: Arc<AtomicBool>,
    acceptor: Option<JoinHandle<()>>,
}

impl ScriptedFollower {
    fn start() -> ScriptedFollower {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let script = Arc::new(Mutex::new(VecDeque::new()));
        let head = Arc::new(AtomicU64::new(0));
        let stop = Arc::new(AtomicBool::new(false));
        let (script_a, head_a, stop_a) = (script.clone(), head.clone(), stop.clone());
        let acceptor = thread::spawn(move || {
            // Blocking accept; `Drop` unblocks it with one last self-connect.
            while let Ok((mut sock, _)) = listener.accept() {
                if stop_a.load(Ordering::Relaxed) {
                    break;
                }
                let (script, head) = (script_a.clone(), head_a.clone());
                thread::spawn(move || {
                    while let Ok(Some(payload)) = read_frame(&mut sock) {
                        let resp = match decode_request(&payload) {
                            Some(Request::Replicate { seq, .. }) => {
                                scripted_reply(&script, &head, seq)
                            }
                            _ => Response::Error {
                                code: 1,
                                msg: "unexpected request".to_string(),
                            },
                        };
                        if write_frame(&mut sock, &encode_response(&resp)).is_err() {
                            break;
                        }
                    }
                });
            }
        });
        ScriptedFollower {
            addr,
            script,
            head,
            stop,
            acceptor: Some(acceptor),
        }
    }

    /// Answer the next `Replicate` with this exact error message.
    fn refuse_next_with(&self, msg: &str) {
        self.script.lock().unwrap().push_back(msg.to_string());
    }

    /// How many leader records this follower holds.
    fn held(&self) -> u64 {
        self.head.load(Ordering::Relaxed)
    }
}

/// One scripted (or real) answer to a `Replicate` at leader offset `seq`.
fn scripted_reply(script: &Mutex<VecDeque<String>>, head: &AtomicU64, seq: u64) -> Response {
    if let Some(msg) = script.lock().unwrap().pop_front() {
        return Response::Error { code: 6, msg };
    }
    let at = head.load(Ordering::Relaxed);
    if seq == at {
        head.store(seq + 1, Ordering::Relaxed);
        Response::PublishAck {
            offset: seq,
            deduped: false,
        }
    } else if seq < at {
        Response::PublishAck {
            offset: seq,
            deduped: true,
        }
    } else {
        Response::Error {
            code: 1,
            msg: format!("replica gap: this log's next offset is {at}, the record is {seq}"),
        }
    }
}

impl Drop for ScriptedFollower {
    fn drop(&mut self) {
        if let Some(a) = self.acceptor.take() {
            self.stop.store(true, Ordering::Relaxed);
            let _ = TcpStream::connect(&self.addr); // unblock accept()
            let _ = a.join();
        }
    }
}

fn is_quorum_err(e: &std::io::Error) -> bool {
    e.to_string().contains("not replicated to quorum")
}

/// A replica is a durable property of the LOG, not of the constructor that opened it:
/// the marker beside the file outlives the process, so a follower reopened through
/// plain `Broker::open` is still a follower. `open_replica` is the same statement made
/// up front, for a follower seeded from a copy of the leader's log.
#[test]
fn a_replica_is_a_durable_property_of_the_log() {
    let (_tmp, flog, llog, lsock) = paths("fmark");
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    Client::connect(&lsock)
        .unwrap()
        .publish(1, 1, "/a/r/x", b"m")
        .unwrap();
    drop(follower);
    fh.shutdown();
    lh.shutdown();

    // Read through the store, with no broker in the way.
    let log = astream_broker::store::BrokerLog::open(&flog).unwrap();
    assert!(log.is_replica(), "the marker survived the follower's close");
    drop(log);

    // A log that has NEVER taken a replicated record is its broker's own...
    let own = format!("{flog}.own");
    let _ = std::fs::remove_file(&own);
    assert!(!astream_broker::store::BrokerLog::open(&own)
        .unwrap()
        .is_replica());
    // ...until it is declared one.
    let b = Broker::open_replica(&own).unwrap();
    drop(b);
    assert!(astream_broker::store::BrokerLog::open(&own)
        .unwrap()
        .is_replica());
}

#[test]
fn ack_waits_for_the_replica_and_records_survive_leader_loss() {
    let (_tmp, flog, llog, lsock) = paths("basic");
    const N: u64 = 50;

    // Follower: an ordinary broker, reachable over TCP.
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();

    // Leader: Replicated tier — local Relaxed + a quorum-1 replica on the follower.
    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();

    // A single publish: when its ack returns, the follower ALREADY holds it. The
    // witness is the follower's head, read in-process without blocking — an
    // implementation that acked first and replicated afterwards could not have
    // advanced it yet.
    let (off0, dup0) = p.publish(1, 1, "/a/r/x", b"m1").unwrap();
    assert_eq!((off0, dup0), (0, false));
    assert_eq!(
        follower.head(),
        1,
        "the follower's head had advanced past the record before the ack returned"
    );
    assert_eq!(
        leader.visible_head(),
        1,
        "quorum-confirmed, so visible on the leader"
    );

    for i in 2..=N {
        let (off, dup) = p
            .publish(1, i, "/a/r/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
        assert_eq!(follower.head(), i, "each ack waited for the replica");
    }
    // Exactly-once at the Replicated tier too: a re-send is deduped to its offset (and
    // acked, because that offset is below the quorum watermark).
    assert_eq!(p.publish(1, 1, "/a/r/x", b"dup").unwrap(), (0, true));

    // LEADER LOSS: stop the leader. The acked records survive — the follower has them at
    // the SAME offsets (the leader shipped each at its exact offset).
    lh.shutdown();
    let mut fsub = Client::connect_tcp(&faddr)
        .unwrap()
        .subscribe(0, "/a/r/>")
        .unwrap();
    for i in 0..N {
        let (off, _s, body) = fsub.recv().unwrap().unwrap();
        assert_eq!(off, i, "follower serves acked record {i} after leader loss");
        assert_eq!(body, format!("m{}", i + 1).into_bytes());
    }
    // The follower's dedup map is the leader's too.
    assert_eq!(
        Client::connect_tcp(&faddr)
            .unwrap()
            .publish(1, 3, "/a/r/x", b"dup")
            .unwrap(),
        (2, true)
    );

    fh.shutdown();
}

#[test]
fn unanswered_replication_is_an_error_and_a_deduped_retry_is_not_acked_until_a_follower_holds_it() {
    let (_tmp, flog, llog, lsock) = paths("silent");
    let mut silent = SilentFollower::start();
    let addr = silent.addr.clone();

    let leader =
        Broker::open_replicated_with(&llog, std::slice::from_ref(&addr), 1, FOLLOWER_TIMEOUT)
            .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();

    // A leader-side subscriber, parked before anything is published.
    let mut sub = UnixStream::connect(&lsock).unwrap();
    write_frame(
        &mut sub,
        &encode_request(&Request::Subscribe {
            from_offset: 0,
            filter: "/a/>".into(),
        }),
    )
    .unwrap();

    // The follower accepts the record and never answers: the ack is an ERROR.
    let err = p.publish(1, 1, "/a/r/x", b"m1").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(
        (leader.head(), leader.visible_head()),
        (1, 0),
        "committed locally, but not visible: no follower holds it"
    );
    // Nothing reaches the leader-side subscriber: a bounded read sees no bytes.
    sub.set_read_timeout(Some(FOLLOWER_TIMEOUT)).unwrap();
    let mut probe = [0u8; 1];
    match sub.read(&mut probe) {
        Err(e)
            if matches!(
                e.kind(),
                std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
            ) => {}
        other => panic!("an unconfirmed record was delivered on the leader: {other:?}"),
    }
    // The idempotent RETRY is deduped locally — and is ALSO an error, not a success
    // ack: nothing was ever confirmed. So is a pure commit.
    let err = p.publish(1, 1, "/a/r/x", b"m1").unwrap_err();
    assert!(is_quorum_err(&err), "retry acked without a replica: {err}");
    let err = p.commit("g", 0).unwrap_err();
    assert!(is_quorum_err(&err), "commit acked without a replica: {err}");
    assert_eq!(leader.visible_head(), 0);

    // A real follower comes up at the follower's address: the leader re-dials it, ships
    // the whole unconfirmed prefix, and the SAME retry is now acked — deduped AND held.
    silent.stop();
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp(&addr).unwrap();
    assert_eq!(p.publish(1, 1, "/a/r/x", b"m1").unwrap(), (0, true));
    assert_eq!(
        follower.head(),
        2,
        "the follower holds the record AND the leader's commit record at their offsets"
    );
    assert_eq!(leader.visible_head(), 2);
    // ...and only now does the leader-side subscriber receive it.
    sub.set_read_timeout(None).unwrap();
    let payload = read_frame(&mut sub).unwrap().unwrap();
    assert_eq!(
        decode_response(&payload),
        Some(Response::Delivery {
            offset: 0,
            subject: "/a/r/x".into(),
            body: b"m1".to_vec(),
        })
    );

    lh.shutdown();
    fh.shutdown();
}

#[test]
fn commit_records_and_annotations_replicate_at_the_same_offsets() {
    let (_tmp, flog, llog, lsock) = paths("commits");
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();

    assert_eq!(p.publish(1, 1, "/a/r/x", b"A").unwrap(), (0, false));
    assert_eq!(
        p.commit("g", 0).unwrap(),
        1,
        "the commit record takes offset 1"
    );
    assert_eq!(p.publish(1, 2, "/a/r/x", b"B").unwrap(), (2, false));
    assert_eq!(
        p.process_and_produce(9, 1, "/a/r/out", b"P", "g", 2)
            .unwrap(),
        (3, false)
    );
    assert_eq!(
        follower.head(),
        4,
        "commit records consume the same offsets on the follower"
    );

    // Data lands at the leader's offsets (1 is the commit record, never delivered).
    let mut fsub = Client::connect_tcp(&faddr)
        .unwrap()
        .subscribe(0, "/a/r/>")
        .unwrap();
    let got: Vec<(u64, Vec<u8>)> = (0..3)
        .map(|_| {
            let (o, _s, b) = fsub.recv().unwrap().unwrap();
            (o, b)
        })
        .collect();
    assert_eq!(
        got,
        vec![(0, b"A".to_vec()), (2, b"B".to_vec()), (3, b"P".to_vec())]
    );
    // The group's commits replicated with their records: on the follower, group `g`
    // resumes past offset 2 (the transaction's commit), i.e. at the output record.
    let mut fg = Client::connect_tcp(&faddr)
        .unwrap()
        .subscribe_group("g", "/a/r/>")
        .unwrap();
    assert_eq!(
        fg.recv().unwrap().unwrap().0,
        3,
        "group resumed on the follower"
    );

    lh.shutdown();
    fh.shutdown();
}

#[test]
fn a_dropped_follower_is_redialed_and_caught_up_and_the_quorum_stays_honest() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let f1log = format!("/tmp/asrep_recon_f1_{pid}_{n}.log");
    let f2log = format!("/tmp/asrep_recon_f2_{pid}_{n}.log");
    let llog = format!("/tmp/asrep_recon_l_{pid}_{n}.log");
    let lsock = format!("/tmp/asrep_recon_l_{pid}_{n}.sock");
    for f in [&f1log, &f2log, &llog] {
        let _ = std::fs::remove_file(f);
    }
    let _tmp = Cleanup::new(&[&f1log, &f2log, &llog, &lsock]);
    let f1 = Broker::open(&f1log).unwrap();
    let mut f1h = f1.serve_tcp("127.0.0.1:0").unwrap();
    let a1 = f1h.tcp_addr().unwrap().to_string();
    let f2 = Broker::open(&f2log).unwrap();
    let mut f2h = f2.serve_tcp("127.0.0.1:0").unwrap();
    let a2 = f2h.tcp_addr().unwrap().to_string();

    // Quorum 2 of 2: every ack needs BOTH followers.
    let leader =
        Broker::open_replicated_with(&llog, &[a1.clone(), a2.clone()], 2, FOLLOWER_TIMEOUT)
            .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();
    assert_eq!(p.publish(1, 1, "/a/r/x", b"m1").unwrap(), (0, false));
    assert_eq!((f1.head(), f2.head()), (1, 1));

    // Follower 2 goes down. The quorum is honest: the next publish is refused even
    // though follower 1 received it.
    f2h.shutdown();
    let err = p.publish(1, 2, "/a/r/x", b"m2").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(
        f1.head(),
        2,
        "the surviving follower still received the record"
    );
    assert_eq!(leader.visible_head(), 1);

    // Follower 2 comes back at its address (log intact). The leader re-dials it on the
    // next batch and CATCHES IT UP: the new publish, the earlier refused key (deduped),
    // and the record it missed are all held.
    let f2b = Broker::open(&f2log).unwrap();
    let mut f2bh = f2b.serve_tcp(&a2).unwrap();
    assert_eq!(p.publish(1, 3, "/a/r/x", b"m3").unwrap(), (2, false));
    assert_eq!(p.publish(1, 2, "/a/r/x", b"m2").unwrap(), (1, true));
    assert_eq!((f1.head(), f2b.head()), (3, 3), "follower 2 was caught up");
    assert_eq!(leader.visible_head(), 3);
    let mut fsub = Client::connect_tcp(&a2)
        .unwrap()
        .subscribe(0, "/a/r/>")
        .unwrap();
    for i in 0..3u64 {
        let (off, _s, body) = fsub.recv().unwrap().unwrap();
        assert_eq!((off, body), (i, format!("m{}", i + 1).into_bytes()));
    }
    lh.shutdown();
    f1h.shutdown();
    f2bh.shutdown();
}

#[test]
fn with_a_follower_down_the_leader_keeps_serving_on_an_honest_quorum() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let f1log = format!("/tmp/asrep_down_f1_{pid}_{n}.log");
    let f2log = format!("/tmp/asrep_down_f2_{pid}_{n}.log");
    let llog = format!("/tmp/asrep_down_l_{pid}_{n}.log");
    let lsock = format!("/tmp/asrep_down_l_{pid}_{n}.sock");
    for f in [&f1log, &f2log, &llog] {
        let _ = std::fs::remove_file(f);
    }
    let _tmp = Cleanup::new(&[&f1log, &f2log, &llog, &lsock]);
    let f1 = Broker::open(&f1log).unwrap();
    let mut f1h = f1.serve_tcp("127.0.0.1:0").unwrap();
    let a1 = f1h.tcp_addr().unwrap().to_string();
    let dead = free_port_addr(); // follower 2 is down: nobody listens here

    // A quorum that could never be met (2 of 2 with one follower unreachable) is a
    // configuration error, refused at open rather than a broker that refuses every ack.
    let err = Broker::open_replicated_with(&llog, &[a1.clone(), dead.clone()], 2, FOLLOWER_TIMEOUT)
        .err()
        .expect("quorum 2 with one follower down cannot open");
    assert!(err.to_string().contains("reachable"), "{err}");

    // Quorum 1 of 2: the reachable follower carries the quorum; the down one is a link
    // that is re-dialed on every batch and confirms nothing until it is back.
    let leader =
        Broker::open_replicated_with(&llog, &[a1.clone(), dead.clone()], 1, FOLLOWER_TIMEOUT)
            .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();
    assert_eq!(p.publish(1, 1, "/a/r/x", b"m1").unwrap(), (0, false));
    assert_eq!(p.publish(1, 2, "/a/r/x", b"m2").unwrap(), (1, false));
    assert_eq!(f1.head(), 2, "the live follower holds every acked record");
    assert_eq!(leader.visible_head(), 2);

    // The down follower comes up at its address with a FRESH log: the leader dials it
    // on the next batch and catches it up from offset 0 — not just the new record.
    let f2 = Broker::open(&f2log).unwrap();
    let mut f2h = f2.serve_tcp(&dead).unwrap();
    assert_eq!(p.publish(1, 3, "/a/r/x", b"m3").unwrap(), (2, false));
    assert_eq!(
        (f1.head(), f2.head()),
        (3, 3),
        "the late follower was caught up from offset 0"
    );
    let mut fsub = Client::connect_tcp(&dead)
        .unwrap()
        .subscribe(0, "/a/r/>")
        .unwrap();
    for i in 0..3u64 {
        let (off, _s, body) = fsub.recv().unwrap().unwrap();
        assert_eq!((off, body), (i, format!("m{}", i + 1).into_bytes()));
    }

    lh.shutdown();
    f1h.shutdown();
    f2h.shutdown();
}

#[test]
fn a_follower_that_lost_its_tail_is_reshipped_and_a_diverged_one_is_fenced() {
    let (_tmp, flog, llog, lsock) = paths("spine");
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader =
        Broker::open_replicated_with(&llog, std::slice::from_ref(&faddr), 1, FOLLOWER_TIMEOUT)
            .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();
    for i in 1..=3u64 {
        assert_eq!(
            p.publish(1, i, "/a/r/x", format!("m{i}").as_bytes())
                .unwrap(),
            (i - 1, false)
        );
    }
    assert_eq!(follower.head(), 3);

    // LOST TAIL: the follower restarts with an EMPTY log at the same address, while the
    // leader's link still remembers a confirmed prefix of 3. The first batch after the
    // restart ships from 3, the follower reports a GAP (its next offset is 0), and the
    // ack is an error — nothing is confirmed; the link resets to re-ship from scratch.
    fh.shutdown();
    drop(follower);
    let _ = std::fs::remove_file(&flog);
    let f2 = Broker::open(&flog).unwrap();
    let mut f2h = f2.serve_tcp(&faddr).unwrap();
    let err = p.publish(1, 4, "/a/r/x", b"m4").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(
        f2.head(),
        0,
        "a gap is refused, never appended out of place"
    );
    assert_eq!(leader.visible_head(), 3);
    // The next batch re-ships from offset 0: the follower holds all four records at
    // the leader's offsets and the retried key is acked, deduped.
    assert_eq!(p.publish(1, 4, "/a/r/x", b"m4").unwrap(), (3, true));
    assert_eq!(f2.head(), 4, "the follower was rebuilt from offset 0");
    assert_eq!(leader.visible_head(), 4);
    let mut fsub = Client::connect_tcp(&faddr)
        .unwrap()
        .subscribe(0, "/a/r/>")
        .unwrap();
    for i in 0..4u64 {
        let (off, _s, body) = fsub.recv().unwrap().unwrap();
        assert_eq!((off, body), (i, format!("m{}", i + 1).into_bytes()));
    }

    // DIVERGENCE: the follower takes a record of its OWN at offset 4 (published to it
    // directly). The leader's next record is offset 4 too: the follower refuses it (a
    // different record is already held there — never silently overwritten), and the
    // leader FENCES that follower: nothing more is shipped to it, it never counts
    // toward the quorum, and (it being the only follower) every ack is an error.
    assert_eq!(
        Client::connect_tcp(&faddr)
            .unwrap()
            .publish(9, 9, "/a/r/own", b"own")
            .unwrap(),
        (4, false)
    );
    let err = p.publish(1, 5, "/a/r/x", b"m5").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    let err = p.publish(1, 6, "/a/r/x", b"m6").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(
        f2.head(),
        5,
        "the diverged follower's own record stands; nothing of the leader's landed after it"
    );
    assert_eq!(leader.visible_head(), 4);
    assert_eq!(leader.head(), 6, "committed locally, confirmed by nobody");

    lh.shutdown();
    f2h.shutdown();
}

/// A TRANSIENT follower refusal must NOT fence the link. Fencing is for a refusal
/// shipping can never repair — a DIVERGED log, or an authorization failure. A
/// follower that is at its connection cap, whose disk errored, or whose log is
/// poisoned answers with an ordinary `Response::Error` too, and fencing on that
/// wedges the leader for good: a fenced link is never shipped to again and never
/// counts toward the quorum, so with quorum == follower count every later publish
/// answers "not replicated to quorum" until the leader PROCESS is restarted.
#[test]
fn a_transient_follower_refusal_does_not_fence_the_link() {
    let (_tmp, _flog, llog, lsock) = paths("transient");
    let follower = ScriptedFollower::start();
    let leader = Broker::open_replicated_with(
        &llog,
        std::slice::from_ref(&follower.addr),
        1,
        FOLLOWER_TIMEOUT,
    )
    .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let mut p = Client::connect(&lsock).unwrap();

    // TRANSIENT: the follower answers the first Replicate the way a broker at its
    // connection cap does. Nothing is confirmed, so this publish is not acked...
    follower.refuse_next_with("too many connections (limit 1024)");
    let err = p.publish(1, 1, "/a/r/x", b"m1").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(follower.held(), 0);
    assert_eq!(leader.visible_head(), 0);

    // ...and the link is NOT fenced: the next batch re-ships from the same confirmed
    // prefix, the follower takes BOTH records, and the quorum watermark advances.
    assert_eq!(p.publish(1, 2, "/a/r/x", b"m2").unwrap(), (1, false));
    assert_eq!(
        follower.held(),
        2,
        "a transient refusal must not stop the leader shipping"
    );
    assert_eq!(leader.visible_head(), 2);

    // An AUTHORIZATION refusal (like a divergence) still fences for good: nothing is
    // shipped to that follower again, so every later ack is an error.
    follower.refuse_next_with("unauthorized: capability does not grant this subject/filter");
    let err = p.publish(1, 3, "/a/r/x", b"m3").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    let err = p.publish(1, 4, "/a/r/x", b"m4").unwrap_err();
    assert!(is_quorum_err(&err), "{err}");
    assert_eq!(
        follower.held(),
        2,
        "a fenced link is never shipped to again"
    );
    assert_eq!(leader.visible_head(), 2);

    lh.shutdown();
}

#[test]
fn shutdown_does_not_hang_on_a_follower_that_never_answers() {
    let (_tmp, _flog, llog, lsock) = paths("wedged");
    let silent = SilentFollower::start();
    // A LONG follower timeout: if shutdown waited it out, this test would take 30 s.
    let leader = Broker::open_replicated_with(
        &llog,
        std::slice::from_ref(&silent.addr),
        1,
        Duration::from_secs(30),
    )
    .unwrap();
    let mut lh = leader.serve(&lsock).unwrap();
    let sock = lsock.clone();
    let producer = thread::spawn(move || {
        Client::connect(&sock)
            .unwrap()
            .publish(1, 1, "/a/r/x", b"m1")
    });
    // The leader's Replicate frame has reached the silent follower: the writer thread
    // is now parked waiting for an ack that will never come.
    silent.got_bytes.recv().unwrap();
    let t0 = Instant::now();
    lh.shutdown();
    assert!(
        t0.elapsed() < Duration::from_secs(10),
        "shutdown waited on the wedged follower for {:?}",
        t0.elapsed()
    );
    let res = producer.join().unwrap();
    assert!(
        res.is_err(),
        "a record no follower confirmed was acked: {res:?}"
    );
}

#[test]
fn a_replicated_broker_without_followers_is_refused() {
    let (_tmp, _flog, llog, _lsock) = paths("nofollower");
    let err = Broker::open_replicated(&llog, &[], 1)
        .err()
        .expect("no followers means no quorum");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{err}");
}
