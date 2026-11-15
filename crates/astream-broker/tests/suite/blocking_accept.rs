// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.blocking-accept`: the acceptor BLOCKS in `accept()` — no
//! connection waits out a sleep, an idle listener never wakes — and shutdown still
//! gets it out in every embedder pattern: the socket path unlinked by the embedder
//! first, TCP, sealed TCP, a second broker bound on the unlinked path, and even both
//! of the broker's names removed or now naming another broker (it is abandoned,
//! counted, and shutdown returns, having dialed nobody else). A wakeup dial that
//! connects to some OTHER listener — a socket on `127.0.0.1:P` beside a `0.0.0.0:P`
//! broker on macOS, or the winner of two racing `serve`s — is the unit tests' in
//! `src/broker.rs` (`*_wake_dial_another_listener_answers_is_not_redialed_forever`),
//! which can point a handle's endpoint at a stranger directly.
//!
//! Counts, never durations. The seams are [`BrokerStats`]'s acceptor counters and
//! [`BrokerHandle::blocks_in_accept`]; every wait for something that must happen is a
//! one-minute HANG DETECTOR, never a latency budget. The negative control is the
//! polling fallback (a socket path whose `<socket>.wake` cannot fit a socket address):
//! the same counters are seen to move there, so a zero elsewhere is a measurement.

#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, BrokerStats, Client};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// An exclusive scratch directory under `/tmp` (a Darwin `TMPDIR` is long enough to
/// push a socket path past `SUN_LEN`), removed on drop. Created exclusively, so no
/// preexisting entry is adopted or removed. Bind it before every broker using it.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asba-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn join(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// `<socket>.wake`, the broker-owned second name of a Unix listener.
fn wake_name(sock: &Path) -> PathBuf {
    let mut name = sock.as_os_str().to_owned();
    name.push(".wake");
    PathBuf::from(name)
}

fn inode(path: &Path) -> Option<u64> {
    std::fs::symlink_metadata(path).ok().map(|m| m.ino())
}

/// Run `f` on its own thread and wait for it — a one-minute HANG DETECTOR, never a
/// latency budget: a shutdown that wedges fails here instead of hanging the suite.
fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(Duration::from_secs(60))
        .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
}

/// Shut `h` down under the hang detector.
fn shut_down(mut h: BrokerHandle) {
    within_a_minute("BrokerHandle::shutdown", move || h.shutdown());
}

/// Wait until `cond` holds — a one-minute HANG DETECTOR for something that must happen.
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(60);
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::sleep(Duration::from_millis(5));
    }
}

/// The acceptor counters' growth from `before` to `after`:
/// `(accepted, wakeups, sleeps)`.
fn grew(before: &BrokerStats, after: &BrokerStats) -> (u64, u64, u64) {
    (
        after.accepted - before.accepted,
        after.acceptor_wakeups - before.acceptor_wakeups,
        after.acceptor_sleeps - before.acceptor_sleeps,
    )
}

const CONNECTS: u64 = 32;

/// The handles stay `Send + Sync`: an embedder shares one across threads (aterm's
/// fabric harness keeps its `BrokerHandle` in a value its threads all borrow), and the
/// acceptor's exit signal — an `mpsc::Receiver`, which is not `Sync` — once made the
/// handle lose it. A compile-time check: this file stops building if either type does.
#[test]
fn broker_and_handle_stay_send_and_sync() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Broker>();
    send_sync::<BrokerHandle>();
}

/// Connections opened BACK TO BACK — each right after the previous one was served,
/// the pattern of an aterm attach's serial dials — each wake the acceptor exactly once
/// and none waits out a sleep. The polling acceptor this replaced slept once per
/// connection here (the cost study measured 1.00 sleeps per connect, p50 24.4 ms).
#[test]
fn back_to_back_unix_connections_wait_out_no_acceptor_sleep() {
    let dir = Scratch::new("b2b");
    let (log, sock) = (dir.join("b.log"), dir.join("b.sock"));
    let b = Broker::open(&log).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(
        h.blocks_in_accept(),
        "a Unix listener with its wake name blocks"
    );
    let before = b.stats();
    for _ in 0..CONNECTS {
        Client::connect(&sock).unwrap().hello().unwrap();
    }
    let after = b.stats();
    assert_eq!(
        grew(&before, &after),
        (CONNECTS, CONNECTS, 0),
        "(accepted, acceptor wakeups, acceptor sleeps) for {CONNECTS} back-to-back connections"
    );
    shut_down(h);
    assert_eq!(b.stats().acceptors_abandoned, 0);
}

/// A burst from several threads at once: still one wakeup per connection (each
/// `accept()` returns one) and no sleep.
#[test]
fn a_concurrent_burst_of_unix_connections_waits_out_no_acceptor_sleep() {
    const THREADS: u64 = 8;
    const EACH: u64 = 16;
    let dir = Scratch::new("burst");
    let (log, sock) = (dir.join("b.log"), dir.join("b.sock"));
    let b = Broker::open(&log).unwrap();
    let h = b.serve(&sock).unwrap();
    let before = b.stats();
    let dialers: Vec<_> = (0..THREADS)
        .map(|_| {
            let sock = sock.clone();
            thread::spawn(move || {
                for _ in 0..EACH {
                    Client::connect(&sock).unwrap().hello().unwrap();
                }
            })
        })
        .collect();
    for d in dialers {
        d.join().unwrap();
    }
    let after = b.stats();
    let n = THREADS * EACH;
    assert_eq!(grew(&before, &after), (n, n, 0));
    shut_down(h);
}

/// TCP: the same — one wakeup per connection, no sleep.
#[test]
fn back_to_back_tcp_connections_wait_out_no_acceptor_sleep() {
    let dir = Scratch::new("tcp");
    let b = Broker::open(dir.join("b.log")).unwrap();
    let h = b.serve_tcp("127.0.0.1:0").unwrap();
    assert!(h.blocks_in_accept(), "TCP always blocks");
    let addr = h.tcp_addr().unwrap().to_string();
    let before = b.stats();
    for _ in 0..CONNECTS {
        Client::connect_tcp(&addr).unwrap().hello().unwrap();
    }
    assert_eq!(grew(&before, &b.stats()), (CONNECTS, CONNECTS, 0));
    shut_down(h);
    assert_eq!(b.stats().acceptors_abandoned, 0);
}

/// Sealed TCP: the handshake runs on the connection thread, so the acceptor's count is
/// the plaintext one.
#[cfg(feature = "aead")]
#[test]
fn back_to_back_sealed_connections_wait_out_no_acceptor_sleep() {
    const KEY: [u8; 32] = [0x5a; 32];
    let dir = Scratch::new("sealed");
    let b = Broker::open(dir.join("b.log")).unwrap();
    let h = b.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap();
    assert!(h.blocks_in_accept());
    let addr = h.tcp_addr().unwrap().to_string();
    let before = b.stats();
    for _ in 0..CONNECTS {
        Client::connect_tcp_sealed(&addr, KEY)
            .unwrap()
            .hello()
            .unwrap();
    }
    assert_eq!(grew(&before, &b.stats()), (CONNECTS, CONNECTS, 0));
    shut_down(h);
    assert_eq!(b.stats().acceptors_abandoned, 0);
}

/// An idle broker's acceptors never wake: over an observation window (here 300 ms,
/// in which the polling acceptors this replaced would have woken about 24 times, two
/// listeners at one sleep per ~25 ms) the counters do not move. The window bounds the
/// observation only — no count can pass or fail by load, since nothing but a
/// connection can return a blocked `accept()`.
#[test]
fn an_idle_broker_acceptor_never_wakes() {
    let dir = Scratch::new("idle");
    let (log, sock) = (dir.join("b.log"), dir.join("b.sock"));
    let b = Broker::open(&log).unwrap();
    let unix = b.serve(&sock).unwrap();
    let tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    assert!(unix.blocks_in_accept() && tcp.blocks_in_accept());
    // One connection each first, so both acceptors are certainly parked in accept().
    Client::connect(&sock).unwrap().hello().unwrap();
    Client::connect_tcp(tcp.tcp_addr().unwrap())
        .unwrap()
        .hello()
        .unwrap();
    let before = b.stats();
    thread::sleep(Duration::from_millis(300));
    let after = b.stats();
    assert_eq!(grew(&before, &after), (0, 0, 0), "an idle acceptor woke");
    shut_down(unix);
    shut_down(tcp);
}

/// The longest socket path this platform's socket address takes (`SUN_LEN` less the
/// NUL: 103 bytes on macOS, 107 on Linux), under `dir`.
fn longest_socket_path(dir: &Scratch) -> PathBuf {
    let base = dir.0.as_os_str().len() + 1;
    (1..200usize)
        .map(|n| dir.join(&"s".repeat(n)))
        .take_while(|p| std::os::unix::net::SocketAddr::from_pathname(p).is_ok())
        .last()
        .unwrap_or_else(|| panic!("no socket path fits under a {base}-byte directory"))
}

/// THE NEGATIVE CONTROL. A socket path so long that `<socket>.wake` cannot fit a
/// socket address leaves the listener without its wake name, so it POLLS — and the
/// counters are seen to move: it sleeps while idle and each sleep's end is a wakeup.
/// It still serves, and its shutdown still returns and unlinks the socket.
#[test]
fn a_listener_without_a_wake_name_polls_and_the_counters_see_it() {
    let dir = Scratch::new("long");
    let sock = longest_socket_path(&dir);
    assert!(std::os::unix::net::SocketAddr::from_pathname(wake_name(&sock)).is_err());
    let b = Broker::open(dir.join("b.log")).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(!h.blocks_in_accept(), "no wake name, so the fallback polls");
    assert_eq!(inode(&wake_name(&sock)), None);
    until("a polling acceptor sleeps while idle", || {
        let s = b.stats();
        s.acceptor_sleeps >= 2 && s.acceptor_wakeups >= 2
    });
    Client::connect(&sock).unwrap().hello().unwrap();
    assert_eq!(b.stats().accepted, 1);
    shut_down(h);
    assert_eq!(inode(&sock), None, "shutdown unlinks the socket");
}

/// THE HAZARD the cost study found: an embedder that unlinks the socket path BEFORE it
/// shuts the broker down (astream's own `tests/suite/any_connection.rs` does). A one-shot
/// dial of the socket path would hang there; the broker-owned wake name — a hard link
/// to the same inode — still reaches the acceptor, and shutdown removes it.
#[test]
fn shutdown_returns_when_the_embedder_unlinked_the_socket_first() {
    let dir = Scratch::new("unlinked");
    let (log, sock) = (dir.join("b.log"), dir.join("b.sock"));
    let b = Broker::open(&log).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(h.blocks_in_accept());
    let wake = wake_name(&sock);
    assert_eq!(
        inode(&wake),
        inode(&sock),
        "the wake name is the socket's own inode"
    );
    Client::connect(&sock).unwrap().hello().unwrap();
    std::fs::remove_file(&sock).unwrap();
    shut_down(h);
    let s = b.stats();
    assert_eq!(
        s.acceptors_abandoned, 0,
        "the acceptor was reached, not abandoned"
    );
    assert_eq!(s.active_listeners, 0);
    assert_eq!(inode(&wake), None, "shutdown removes its wake name");
    drop(b);
    Broker::open(&log).expect("the last listener's shutdown released the log lock");
}

/// The pathological embedder: BOTH names removed, so nothing can dial the acceptor
/// out of `accept()`. Shutdown neither hangs nor pretends: after its bounded run of
/// failed dials it abandons the parked acceptor, counts it, and finishes the rest —
/// the writer joined and the log lock released.
#[test]
fn shutdown_abandons_rather_than_hangs_when_no_name_reaches_the_listener() {
    let dir = Scratch::new("nameless");
    let (log, sock) = (dir.join("b.log"), dir.join("b.sock"));
    let b = Broker::open(&log).unwrap();
    let h = b.serve(&sock).unwrap();
    Client::connect(&sock).unwrap().hello().unwrap();
    std::fs::remove_file(&sock).unwrap();
    std::fs::remove_file(wake_name(&sock)).unwrap();
    shut_down(h);
    assert_eq!(b.stats().acceptors_abandoned, 1);
    drop(b);
    Broker::open(&log).expect("shutdown released the log lock even so");
}

/// The DIAL side of "only names that still point at its own listener's inode": the
/// embedder removed both of the first broker's names and a second broker bound the
/// path afresh, making its own wake name, so both names now carry the SECOND broker's
/// inode. A dial through either would connect — to the wrong acceptor — so the first
/// broker's shutdown dials neither: it abandons its own acceptor, and the second
/// broker sees not one stray connection and keeps both its names. (Without the dial
/// side's identity check this shutdown sent the second broker a wakeup dial every
/// round until it gave up, and before that give-up counted only rounds its own
/// acceptor answered, it redialed the second broker forever.)
#[test]
fn shutdown_never_dials_a_name_that_now_names_another_broker() {
    let dir = Scratch::new("redial");
    let sock = dir.join("b.sock");
    let wake = wake_name(&sock);
    let first = Broker::open(dir.join("first.log")).unwrap();
    let h1 = first.serve(&sock).unwrap();
    assert!(h1.blocks_in_accept());
    std::fs::remove_file(&sock).unwrap();
    std::fs::remove_file(&wake).unwrap();

    let second = Broker::open(dir.join("second.log")).unwrap();
    let h2 = second.serve(&sock).unwrap();
    assert!(
        h2.blocks_in_accept(),
        "the wake name was free, so the second broker made its own"
    );
    let second_node = inode(&sock);
    assert_eq!(inode(&wake), second_node);

    shut_down(h1);
    assert_eq!(first.stats().acceptors_abandoned, 1);
    assert_eq!(
        (inode(&sock), inode(&wake)),
        (second_node, second_node),
        "the second broker's names survive"
    );
    // The second broker's acceptor takes connections in the order they were queued
    // and counts each before it hands it off, so once this one is answered every
    // earlier one — a stray wakeup dial among them — is counted.
    Client::connect(&sock).unwrap().hello().unwrap();
    assert_eq!(
        second.stats().accepted,
        1,
        "the first broker's shutdown dialed the second broker"
    );
    shut_down(h2);
    assert_eq!((inode(&sock), inode(&wake)), (None, None));
}

/// A STALE socket at `<socket>.wake` (a broker that crashed or was killed) is taken
/// over: the listener blocks, and the name now carries the new socket's inode.
#[test]
fn a_stale_wake_name_is_taken_over() {
    let dir = Scratch::new("stale");
    let sock = dir.join("b.sock");
    let wake = wake_name(&sock);
    super::stale_socket::from_crashed_broker(&wake, dir.join("stale.log"));
    let stale = inode(&wake);
    let b = Broker::open(dir.join("b.log")).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(h.blocks_in_accept());
    assert_ne!(inode(&wake), stale);
    assert_eq!(inode(&wake), inode(&sock));
    shut_down(h);
    assert_eq!((inode(&sock), inode(&wake)), (None, None));
}

/// Something at `<socket>.wake` that is not a socket — a user's file, a symlink — is
/// never removed or followed: the listener polls instead, serves, and shuts down, and
/// the file is untouched.
#[test]
fn a_foreign_file_at_the_wake_name_is_kept_and_the_listener_polls() {
    let dir = Scratch::new("foreign");
    let sock = dir.join("b.sock");
    let wake = wake_name(&sock);
    std::fs::write(&wake, b"not the broker's").unwrap();
    let b = Broker::open(dir.join("b.log")).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(!h.blocks_in_accept());
    Client::connect(&sock).unwrap().hello().unwrap();
    shut_down(h);
    assert_eq!(std::fs::read(&wake).unwrap(), b"not the broker's");
    assert_eq!(inode(&sock), None);

    // A symlink there: not followed, not removed. A fresh broker: the first one's
    // last listener has shut down, so it stopped for good and a listener it served now
    // would leave at once instead of serving.
    std::fs::remove_file(&wake).unwrap();
    let target = dir.join("elsewhere");
    std::fs::write(&target, b"untouched").unwrap();
    std::os::unix::fs::symlink(&target, &wake).unwrap();
    let b = Broker::open(dir.join("b2.log")).unwrap();
    let h = b.serve(&sock).unwrap();
    assert!(!h.blocks_in_accept());
    Client::connect(&sock).unwrap().hello().unwrap();
    assert_eq!(b.stats().accepted, 1);
    shut_down(h);
    assert_eq!(inode(&sock), None);
    assert!(std::fs::symlink_metadata(&wake)
        .unwrap()
        .file_type()
        .is_symlink());
    assert_eq!(std::fs::read(&target).unwrap(), b"untouched");
}

/// A SECOND broker bound on a path the first one's embedder unlinked finds the first
/// one's wake name LIVE and leaves it (polling instead), so the first still shuts down
/// through it — and that shutdown unlinks only its own names: the second broker's
/// socket at the shared path survives and keeps serving.
#[test]
fn a_second_broker_on_the_unlinked_path_keeps_both_reachable() {
    let dir = Scratch::new("second");
    let sock = dir.join("b.sock");
    let wake = wake_name(&sock);
    let first = Broker::open(dir.join("first.log")).unwrap();
    let h1 = first.serve(&sock).unwrap();
    let first_node = inode(&sock);
    std::fs::remove_file(&sock).unwrap();

    let second = Broker::open(dir.join("second.log")).unwrap();
    let h2 = second.serve(&sock).unwrap();
    assert!(
        !h2.blocks_in_accept(),
        "the live wake name is the first broker's"
    );
    assert_eq!(inode(&wake), first_node);
    // The second broker found the name live with a nonblocking datagram probe, which
    // queues no stream connection (`claim_socket_path`): the first one's acceptor is
    // parked in accept(), took no dial, and only its wake name — the socket path is the
    // second broker's now — can reach it.
    assert_eq!(
        first.stats().accepted,
        0,
        "the liveness probe dialed the stream"
    );

    shut_down(h1);
    assert_eq!(first.stats().acceptors_abandoned, 0);
    assert_eq!(
        inode(&wake),
        None,
        "the first broker removed its own wake name"
    );
    assert!(
        inode(&sock).is_some(),
        "the second broker's socket survived"
    );
    Client::connect(&sock).unwrap().hello().unwrap();
    assert_eq!(second.stats().accepted, 1);

    shut_down(h2);
    assert_eq!(inode(&sock), None);
}
