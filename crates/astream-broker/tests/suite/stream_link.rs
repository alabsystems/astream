// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A broker connection over a stream its embedder already authenticated: `Broker::serve_stream`,
//! `connect_stream` and `FederationWire::Stream`, over a memory pipe with no descriptor at all.

#![cfg(all(unix, feature = "stream"))]

use astream_broker::{
    connect_stream, identity_principal, parse_federation_rules, Broker, Durability,
    FederationBridge, FederationConfig, FederationEndpoint, FederationRunner, StreamDial,
    StreamLink, SubjectRewrite, Transport, IDLE_MARK_DEADLINE,
};
use std::collections::VecDeque;
use std::io;
use std::net::Shutdown;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{mpsc, Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// A hang detector: what must happen happens well inside it.
const HANG: Duration = Duration::from_secs(60);

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Self {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let p = std::env::temp_dir().join(format!("assl-{tag}-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        Self(p)
    }

    fn log(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// One direction of a memory pipe.
#[derive(Default)]
struct Half {
    bytes: Mutex<(VecDeque<u8>, bool)>,
    moved: Condvar,
}

impl Half {
    fn close(&self) {
        self.bytes.lock().unwrap().1 = true;
        self.moved.notify_all();
    }
}

/// One end of a memory pipe: a `StreamLink` no file descriptor stands behind. Its `set_nonblocking`
/// is the trait's refusal, so a tail's probe of its peer waits out the read timeout.
struct MemLink {
    rx: Arc<Half>,
    tx: Arc<Half>,
    read_timeout: Mutex<Option<Duration>>,
}

fn mem_pair() -> (Arc<MemLink>, Arc<MemLink>) {
    let (a, b) = (Arc::new(Half::default()), Arc::new(Half::default()));
    (
        Arc::new(MemLink {
            rx: Arc::clone(&a),
            tx: Arc::clone(&b),
            read_timeout: Mutex::new(None),
        }),
        Arc::new(MemLink {
            rx: b,
            tx: a,
            read_timeout: Mutex::new(None),
        }),
    )
}

impl StreamLink for MemLink {
    fn read(&self, buf: &mut [u8]) -> io::Result<usize> {
        let until = self
            .read_timeout
            .lock()
            .unwrap()
            .map(|d| Instant::now() + d);
        let mut held = self.rx.bytes.lock().unwrap();
        loop {
            if !held.0.is_empty() {
                let n = buf.len().min(held.0.len());
                for (slot, b) in buf.iter_mut().zip(held.0.drain(..n)) {
                    *slot = b;
                }
                return Ok(n);
            }
            if held.1 {
                return Ok(0);
            }
            held = match until {
                None => self.rx.moved.wait(held).unwrap(),
                Some(t) => {
                    let left = t.saturating_duration_since(Instant::now());
                    if left.is_zero() {
                        return Err(io::ErrorKind::WouldBlock.into());
                    }
                    self.rx.moved.wait_timeout(held, left).unwrap().0
                }
            };
        }
    }

    fn write(&self, buf: &[u8]) -> io::Result<usize> {
        let mut held = self.tx.bytes.lock().unwrap();
        if held.1 {
            return Err(io::ErrorKind::BrokenPipe.into());
        }
        held.0.extend(buf);
        self.tx.moved.notify_all();
        Ok(buf.len())
    }

    fn flush(&self) -> io::Result<()> {
        Ok(())
    }

    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        *self.read_timeout.lock().unwrap() = d;
        Ok(())
    }

    fn set_write_timeout(&self, _d: Option<Duration>) -> io::Result<()> {
        Ok(())
    }

    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        if matches!(how, Shutdown::Write | Shutdown::Both) {
            self.tx.close();
        }
        if matches!(how, Shutdown::Read | Shutdown::Both) {
            self.rx.close();
        }
        Ok(())
    }
}

/// Dials by adopting the far end on `broker`, as an embedder's fleet link does.
struct AdoptOn {
    broker: Arc<Broker>,
    peer: [u8; 32],
}

impl StreamDial for AdoptOn {
    fn dial(&self) -> io::Result<Arc<dyn StreamLink>> {
        let (near, far) = mem_pair();
        drop(self.broker.serve_stream(far, self.peer)?);
        Ok(near)
    }
}

const PEER: [u8; 32] = [0x41; 32];
const OTHER: [u8; 32] = [0x42; 32];

/// `f` on a thread of its own, its answer or a panic past [`HANG`].
fn within_hang<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(HANG)
        .unwrap_or_else(|_| panic!("{what}: still parked after {HANG:?}"))
}

#[test]
fn publish_and_subscribe_ride_a_stream_with_no_descriptor() {
    let s = Scratch::new("rt");
    let broker = Broker::open_with(s.log("a.log"), Durability::Relaxed).unwrap();

    let (near, far) = mem_pair();
    let served = broker.serve_stream(far, PEER).unwrap();
    let (mut client, closer) = connect_stream(near);
    assert_eq!(client.publish(1, 1, "/x/a", b"one").unwrap(), (0, false));
    assert_eq!(client.publish(1, 1, "/x/a", b"one").unwrap(), (0, true));

    let (near2, far2) = mem_pair();
    let served2 = broker.serve_stream(far2, PEER).unwrap();
    let (client2, closer2) = connect_stream(near2);
    let mut sub = client2.subscribe(0, "/x/>").unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (0, "/x/a".to_string(), b"one".to_vec())
    );

    // A live delivery wakes the parked tail: the second stream's record comes off the first.
    assert_eq!(client.publish(1, 2, "/x/a", b"two").unwrap(), (1, false));
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (1, "/x/a".to_string(), b"two".to_vec())
    );

    // The closer needs no descriptor: it wakes the read parked on another thread.
    let parked = std::thread::spawn(move || sub.recv().map(|r| r.is_none()));
    closer2.close();
    assert!(within_hang("closer", move || parked.join().unwrap()).unwrap_or(true));
    within_hang("second connection's thread", move || {
        let _ = served2.join().unwrap();
    });

    closer.close();
    within_hang("first connection's thread", move || {
        let _ = served.join().unwrap();
    });
    assert_eq!(broker.stats().active_conns, 0);
}

#[cfg(feature = "cap")]
#[test]
fn the_adopted_peer_is_the_only_node_its_grants_may_name() {
    use astream_cap::mint;
    const SECRET: &[u8] = b"stream-link-guarded-secret-0123456789";

    let s = Scratch::new("bind");
    let broker =
        Broker::open_guarded_with(s.log("a.log"), SECRET.to_vec(), Durability::Relaxed).unwrap();

    let (near, far) = mem_pair();
    drop(broker.serve_stream(far, PEER).unwrap());
    let (mut client, _closer) = connect_stream(near);

    let others = mint(SECRET, &format!("rw,p={}:/x/>", identity_principal(&OTHER))).unwrap();
    let err = client.attach(&others.filter, &others.tag).unwrap_err();
    assert!(
        err.to_string().contains("does not match authenticated"),
        "another node's grant was refused for the wrong reason: {err}"
    );

    let own = mint(SECRET, &format!("rw,p={}:/x/>", identity_principal(&PEER))).unwrap();
    client.attach(&own.filter, &own.tag).unwrap();
    let id = astream_cap::producer_id_of(&identity_principal(&PEER));
    assert_eq!(client.publish(id, 1, "/x/a", b"mine").unwrap(), (1, false));
}

#[test]
fn a_revocation_ends_an_idle_stream_and_refuses_the_next() {
    let s = Scratch::new("revoke");
    let broker = Broker::open_with(s.log("a.log"), Durability::Relaxed).unwrap();

    // Parked in a blocking read, with no request or delivery to come: only the shutdown ends it.
    let (idle_near, idle_far) = mem_pair();
    let idle = broker.serve_stream(idle_far, PEER).unwrap();
    // Parked in a tail.
    let (tail_near, tail_far) = mem_pair();
    let tail = broker.serve_stream(tail_far, PEER).unwrap();
    let (tail_client, _tail_closer) = connect_stream(tail_near);
    let mut sub = tail_client.subscribe(0, "/x/>").unwrap();
    // Another node's stream on the same broker stays up.
    let (other_near, other_far) = mem_pair();
    let other = broker.serve_stream(other_far, OTHER).unwrap();
    let (mut other_client, _other_closer) = connect_stream(other_near);
    assert!(!other_client.publish(9, 1, "/y/a", b"up").unwrap().1);

    assert!(broker.revoke_identity(PEER));

    within_hang("idle connection after revoke", move || {
        let _ = idle.join().unwrap();
    });
    let mut probe = [0u8; 1];
    assert_eq!(
        idle_near.read(&mut probe).unwrap(),
        0,
        "the peer read end of stream"
    );
    within_hang("tail after revoke", move || {
        let _ = tail.join().unwrap();
    });
    assert!(!matches!(sub.recv(), Ok(Some(_))));

    let (_near, far) = mem_pair();
    let refused = broker.serve_stream(far, PEER).unwrap_err();
    assert_eq!(refused.kind(), io::ErrorKind::PermissionDenied);

    assert!(!other_client.publish(9, 2, "/y/a", b"up").unwrap().1);
    assert!(!other.is_finished());
}

#[test]
fn revoking_the_nodes_principal_ends_its_stream_too() {
    let s = Scratch::new("principal");
    let broker = Broker::open_with(s.log("a.log"), Durability::Relaxed).unwrap();
    let (near, far) = mem_pair();
    let served = broker.serve_stream(far, PEER).unwrap();
    // At once, so it often runs before the connection's thread registers: that order is ended too.
    assert!(broker.revoke_principal(&identity_principal(&PEER)));
    within_hang("connection after revoke_principal", move || {
        let _ = served.join().unwrap();
    });
    let mut probe = [0u8; 1];
    assert_eq!(near.read(&mut probe).unwrap(), 0);
}

#[test]
fn a_bridge_mirrors_and_reconnects_over_streams_alone() {
    let s = Scratch::new("bridge");
    let src = Arc::new(Broker::open_with(s.log("src.log"), Durability::Relaxed).unwrap());
    let dst = Arc::new(Broker::open_with(s.log("dst.log"), Durability::Relaxed).unwrap());
    let dial = |b: &Arc<Broker>| -> Arc<dyn StreamDial> {
        Arc::new(AdoptOn {
            broker: Arc::clone(b),
            peer: PEER,
        })
    };
    let (mut publisher, _closer) = connect_stream(dial(&src).dial().unwrap());
    publisher.publish(7, 1, "/f/pub/a", b"one").unwrap();

    let cfg = FederationConfig {
        source: FederationEndpoint::stream("n-src", dial(&src)),
        dest: FederationEndpoint::stream("n-dst", dial(&dst)),
        group: "/g/fed/dst".to_string(),
        filter: "/f/pub/>".to_string(),
        carry: Vec::new(),
        producer_id: 77,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    };
    let mut bridge = FederationBridge::open(cfg).unwrap();
    assert_eq!(bridge.sync_once(16).unwrap().mirrored, 1);

    publisher.publish(7, 2, "/f/pub/a", b"two").unwrap();
    bridge.reconnect().unwrap();
    assert_eq!(bridge.sync_once(16).unwrap().mirrored, 1);

    let (dst_client, _dst_closer) = connect_stream(dial(&dst).dial().unwrap());
    let mut sub = dst_client.subscribe(0, "/f/pub/>").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"one".to_vec());
    assert_eq!(sub.recv().unwrap().unwrap().2, b"two".to_vec());
}

type Timeouts = Arc<Mutex<Vec<Option<Duration>>>>;

/// A [`MemLink`] that remembers every read timeout it was given.
struct WatchedLink {
    inner: Arc<MemLink>,
    timeouts: Timeouts,
    shut: Arc<AtomicBool>,
}

impl StreamLink for WatchedLink {
    fn read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.read(buf)
    }
    fn write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.write(buf)
    }
    fn flush(&self) -> io::Result<()> {
        self.inner.flush()
    }
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.timeouts.lock().unwrap().push(d);
        self.inner.set_read_timeout(d)
    }
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.inner.set_write_timeout(d)
    }
    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        self.shut.store(true, Ordering::SeqCst);
        self.inner.shutdown(how)
    }
}

/// Dials adopted streams, keeping the timeouts each was given, in dial order.
struct WatchedDial {
    broker: Arc<Broker>,
    links: Mutex<Vec<Timeouts>>,
    shuts: Mutex<Vec<Arc<AtomicBool>>>,
    dialed: Mutex<Vec<Arc<MemLink>>>,
}

impl StreamDial for WatchedDial {
    fn dial(&self) -> io::Result<Arc<dyn StreamLink>> {
        let (near, far) = mem_pair();
        drop(self.broker.serve_stream(far, PEER)?);
        let timeouts = Arc::new(Mutex::new(Vec::new()));
        self.links.lock().unwrap().push(Arc::clone(&timeouts));
        let shut = Arc::new(AtomicBool::new(false));
        self.shuts.lock().unwrap().push(Arc::clone(&shut));
        self.dialed.lock().unwrap().push(Arc::clone(&near));
        Ok(Arc::new(WatchedLink {
            inner: near,
            timeouts,
            shut,
        }))
    }
}

#[test]
fn a_running_bridge_waits_on_its_subscription_under_the_liveness_deadline_alone() {
    let s = Scratch::new("push");
    let src = Arc::new(Broker::open_with(s.log("src.log"), Durability::Relaxed).unwrap());
    let dst = Arc::new(Broker::open_with(s.log("dst.log"), Durability::Relaxed).unwrap());
    let watched = Arc::new(WatchedDial {
        broker: Arc::clone(&src),
        links: Mutex::new(Vec::new()),
        shuts: Mutex::new(Vec::new()),
        dialed: Mutex::new(Vec::new()),
    });
    let cfg = FederationConfig {
        source: FederationEndpoint::stream("n-src", Arc::clone(&watched) as Arc<dyn StreamDial>),
        dest: FederationEndpoint::stream(
            "n-dst",
            Arc::new(AdoptOn {
                broker: Arc::clone(&dst),
                peer: PEER,
            }),
        ),
        group: "/g/fed/dst".to_string(),
        filter: "/f/pub/>".to_string(),
        carry: Vec::new(),
        producer_id: 77,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    };
    let mut bridge = FederationBridge::open(cfg).unwrap();
    let closer = bridge.closer();
    let (tx, rx) = mpsc::channel();
    let running = std::thread::spawn(move || {
        bridge
            .run(256, &mut |report| {
                let _ = tx.send(report.mirrored);
            })
            .map_err(|e| e.to_string())
    });

    let (near, far) = mem_pair();
    drop(src.serve_stream(far, PEER).unwrap());
    let (mut publisher, _publisher_closer) = connect_stream(near);
    publisher.publish(7, 1, "/f/pub/a", b"one").unwrap();
    assert_eq!(rx.recv_timeout(HANG).unwrap(), 1);

    closer.close();
    within_hang("the bridge after close", move || {
        running.join().unwrap().unwrap();
    });

    // The bridge's own dials: the source control connection, its bootstrap, its subscription.
    // The last of them is the subscription, whose last word on its read timeout is the liveness
    // deadline: what bounds a dead source, with no interval of its own.
    let links = watched.links.lock().unwrap();
    assert_eq!(links.len(), 3);
    assert_eq!(
        links[2].lock().unwrap().last(),
        Some(&Some(IDLE_MARK_DEADLINE))
    );
}

/// Serves its first `served` dials and leaves every later one unanswered, saying when one comes.
struct StallingDial {
    broker: Arc<Broker>,
    served: Mutex<usize>,
    stalled: Mutex<Vec<Arc<MemLink>>>,
    reached: Mutex<mpsc::Sender<()>>,
}

impl StreamDial for StallingDial {
    fn dial(&self) -> io::Result<Arc<dyn StreamLink>> {
        let (near, far) = mem_pair();
        let mut served = self.served.lock().unwrap();
        if *served > 0 {
            *served -= 1;
            drop(self.broker.serve_stream(far, PEER)?);
        } else {
            self.stalled.lock().unwrap().push(far);
            let _ = self.reached.lock().unwrap().send(());
        }
        Ok(near)
    }
}

/// A bridge whose subscription's source accepts and then never answers.
fn bridge_on_a_stalled_source(
    s: &Scratch,
    io_timeout: Duration,
) -> (FederationBridge, mpsc::Receiver<()>) {
    let src = Arc::new(Broker::open_with(s.log("src.log"), Durability::Relaxed).unwrap());
    let dst = Arc::new(Broker::open_with(s.log("dst.log"), Durability::Relaxed).unwrap());
    let (reached, stalled) = mpsc::channel();
    let source = FederationEndpoint::stream(
        "n-src",
        Arc::new(StallingDial {
            broker: src,
            // The bridge's own control connection and its bootstrap.
            served: Mutex::new(2),
            stalled: Mutex::new(Vec::new()),
            reached: Mutex::new(reached),
        }),
    )
    .with_timeouts(Some(io_timeout), Some(io_timeout));
    let cfg = FederationConfig {
        source,
        dest: FederationEndpoint::stream(
            "n-dst",
            Arc::new(AdoptOn {
                broker: dst,
                peer: PEER,
            }),
        ),
        group: "/g/fed/dst".to_string(),
        filter: "/f/pub/>".to_string(),
        carry: Vec::new(),
        producer_id: 77,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    };
    (FederationBridge::open(cfg).unwrap(), stalled)
}

#[test]
fn a_close_ends_a_run_stuck_in_the_handshake() {
    let s = Scratch::new("stallclose");
    // An io timeout no test waits out: only the close can end this run.
    let (mut bridge, stalled) = bridge_on_a_stalled_source(&s, Duration::from_secs(3600));
    let closer = bridge.closer();
    let running = std::thread::spawn(move || bridge.run(256, &mut |_| {}).is_ok());
    stalled.recv_timeout(HANG).unwrap();
    closer.close();
    within_hang("the run after close", move || {
        assert!(running.join().unwrap());
    });
}

#[test]
fn a_handshake_keeps_the_endpoints_io_timeout() {
    let s = Scratch::new("stalltimeout");
    let (mut bridge, _stalled) = bridge_on_a_stalled_source(&s, Duration::from_secs(2));
    within_hang("the run on a silent source", move || {
        assert!(bridge.run(256, &mut |_| {}).is_err());
    });
}

#[test]
fn a_run_that_fails_shuts_the_connection_it_parked() {
    let s = Scratch::new("release");
    let src = Arc::new(Broker::open_with(s.log("src.log"), Durability::Relaxed).unwrap());
    let dst = Broker::open_with(s.log("dst.log"), Durability::Relaxed).unwrap();
    let dst_sock = s.log("dst.sock");
    let dst_handle = dst.serve(&dst_sock).unwrap();
    let watched = Arc::new(WatchedDial {
        broker: Arc::clone(&src),
        links: Mutex::new(Vec::new()),
        shuts: Mutex::new(Vec::new()),
        dialed: Mutex::new(Vec::new()),
    });
    let cfg = FederationConfig {
        source: FederationEndpoint::stream("n-src", Arc::clone(&watched) as Arc<dyn StreamDial>),
        dest: FederationEndpoint::new(dst_sock.to_str().unwrap(), Transport::Unix),
        group: "/g/fed/dst".to_string(),
        filter: "/f/pub/>".to_string(),
        carry: Vec::new(),
        producer_id: 77,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    };
    let mut bridge = FederationBridge::open(cfg).unwrap();
    // Kept past the run, as a supervisor's is: it must not keep the connection open.
    let _closer = bridge.closer();
    let running = std::thread::spawn(move || {
        let outcome = bridge.run(256, &mut |_| {}).is_err();
        (outcome, bridge)
    });
    drop(dst_handle);
    drop(dst);

    let (near, far) = mem_pair();
    drop(src.serve_stream(far, PEER).unwrap());
    let (mut publisher, _publisher_closer) = connect_stream(near);
    publisher.publish(7, 1, "/f/pub/a", b"one").unwrap();

    // The source sees the subscription end while the bridge, and its closer, still live.
    let (failed, _bridge) = within_hang("the run with its destination gone", move || {
        running.join().unwrap()
    });
    assert!(failed);
    let shuts = watched.shuts.lock().unwrap();
    assert_eq!(shuts.len(), 3);
    assert!(
        shuts[2].load(Ordering::SeqCst),
        "the subscription's link was shut"
    );
}

#[test]
fn revoking_the_nodes_principal_drops_its_stream_will() {
    for revoked in [true, false] {
        let s = Scratch::new("willprincipal");
        let broker = Broker::open_with(s.log("a.log"), Durability::Relaxed).unwrap();
        let (near, far) = mem_pair();
        let served = broker.serve_stream(far, PEER).unwrap();
        let (mut client, _closer) = connect_stream(Arc::clone(&near) as Arc<dyn StreamLink>);
        client.will(7, 1, "/f/pub/will", b"gone").unwrap();
        if revoked {
            assert!(broker.revoke_principal(&identity_principal(&PEER)));
        } else {
            near.shutdown(Shutdown::Both).unwrap();
        }
        within_hang("the connection", move || {
            let _ = served.join().unwrap();
        });
        // The will's firing is enqueued before the connection's thread returns, so a publish
        // after it reads the log behind it.
        let (near, far) = mem_pair();
        drop(broker.serve_stream(far, [9; 32]).unwrap());
        let (mut reader, _closer) = connect_stream(near);
        reader.publish(8, 1, "/f/pub/after", b"x").unwrap();
        let (rows, _) = reader.fetch(0, "/f/pub/will", 16).unwrap();
        assert_eq!(rows.len(), usize::from(!revoked), "revoked: {revoked}");
    }
}

#[test]
fn a_link_with_no_nonblocking_mode_leaves_a_client_framed() {
    let s = Scratch::new("nononblock");
    let broker = Broker::open_with(s.log("a.log"), Durability::Relaxed).unwrap();
    let (near, far) = mem_pair();
    drop(broker.serve_stream(far, PEER).unwrap());
    let (mut client, _closer) = connect_stream(near);
    // With no ack owed, or none here yet, the answer is the same word and costs the client nothing.
    client.send_publish(7, 1, "/f/pub/a", b"one").unwrap();
    loop {
        match client.try_recv_publish_ack() {
            Err(e) => {
                assert_eq!(e.kind(), io::ErrorKind::Unsupported);
                break;
            }
            // The ack raced ahead of the first try: it was in hand with no read to switch for.
            Ok(Some(_)) => {
                client.send_publish(7, 2, "/f/pub/a", b"two").unwrap();
            }
            Ok(None) => unreachable!("this link cannot answer not-yet"),
        }
    }
    client.recv_publish_ack().unwrap();
    client.publish(7, 3, "/f/pub/a", b"three").unwrap();
}

/// A failed run is one run: the documented recovery is to reconnect and run again, and only the
/// closer's `close` is for good.
#[test]
fn a_runner_that_lost_its_source_runs_again_after_reconnecting() {
    let s = Scratch::new("again");
    let src = Arc::new(Broker::open_with(s.log("src.log"), Durability::Relaxed).unwrap());
    let dst = Arc::new(Broker::open_with(s.log("dst.log"), Durability::Relaxed).unwrap());
    let watched = Arc::new(WatchedDial {
        broker: Arc::clone(&src),
        links: Mutex::new(Vec::new()),
        shuts: Mutex::new(Vec::new()),
        dialed: Mutex::new(Vec::new()),
    });
    let rules = parse_federation_rules(
        "group=/g/fed/a filter=/f/pub/a/>\ngroup=/g/fed/b filter=/f/pub/b/>\n",
    )
    .unwrap();
    let mut runner = FederationRunner::open(
        FederationEndpoint::stream("n-src", Arc::clone(&watched) as Arc<dyn StreamDial>),
        FederationEndpoint::stream(
            "n-dst",
            Arc::new(AdoptOn {
                broker: Arc::clone(&dst),
                peer: PEER,
            }),
        ),
        77,
        rules,
    )
    .unwrap();
    let closer = runner.closer();
    let (near, far) = mem_pair();
    drop(src.serve_stream(far, [9; 32]).unwrap());
    let (mut publisher, _publisher_closer) = connect_stream(near);

    let (tx, rx) = mpsc::channel();
    let tx = Arc::new(Mutex::new(tx));
    let report = {
        let tx = Arc::clone(&tx);
        move |group: &str, report: &astream_broker::FederationReport| {
            let _ = tx
                .lock()
                .unwrap()
                .send((group.to_string(), report.mirrored));
        }
    };
    let (report_a, report_b) = (report.clone(), report);
    let running = std::thread::spawn(move || {
        let failed = runner.run(&report_a).is_err();
        (runner, failed)
    });
    publisher.publish(7, 1, "/f/pub/a/x", b"one").unwrap();
    assert_eq!(rx.recv_timeout(HANG).unwrap(), ("/g/fed/a".to_string(), 1));
    // Every connection the bridges hold goes, as when the link to the source does.
    for link in watched.dialed.lock().unwrap().iter() {
        link.shutdown(Shutdown::Both).unwrap();
    }
    let (mut runner, failed) = within_hang("the run that lost its source", move || {
        running.join().unwrap()
    });
    assert!(failed);
    assert!(!runner.is_stopped());

    runner.reconnect_all().unwrap();
    let running = std::thread::spawn(move || runner.run(&report_b).map_err(|e| e.to_string()));
    publisher.publish(7, 2, "/f/pub/a/x", b"two").unwrap();
    assert_eq!(rx.recv_timeout(HANG).unwrap(), ("/g/fed/a".to_string(), 1));
    closer.close();
    within_hang("the closed run", move || running.join().unwrap().unwrap());
}
