// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.peer-probe-nonblocking`: a subscriber tail probes its peer for
//! having gone at most once per liveness poll, and the probe never blocks, so it can no
//! longer sit out the wakeup of the next commit — while a subscriber that left is
//! still reaped, parked or under traffic it does not match, and a probed stream still
//! blocks, as a delivery stream must, when its subscriber falls behind.
//!
//! Before this, a tail that read a batch without matching any of it probed at once, in
//! a read bounded only by a 1 ms socket timeout (1.13 ms measured), during which the
//! `Condvar` wake of the next commit found nobody waiting: on the Relaxed tier a
//! matching record 0.3 ms behind a non-matching one reached its subscriber at p50
//! 0.80-0.84 ms against 0.07 ms alone (cost study B3). On the Strict tier the next
//! batch's fsync outlasts the probe, so it never showed there; the Ordered tier's
//! 0.13-0.6 ms flush does not.
//!
//! Counts, never durations: [`BrokerStats`]'s `peer_probes`, `tail_wakeups`,
//! `parked_tails` and `active_conns`. Every wait for something that must happen is a
//! one-minute HANG DETECTOR, never a latency budget. The negative controls: a parked
//! tail whose poll comes due does probe, and a subscriber that left is reaped.

#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, BrokerStats, Client, Durability, Subscription};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// A wait for something that must happen: a hang detector, never a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// A liveness poll no test outlasts: no probe comes due inside a count.
const NO_POLL: Duration = Duration::from_secs(3600);

/// A liveness poll short enough that a test sees several probes come due.
const SHORT_POLL: Duration = Duration::from_millis(5);

/// A liveness poll a test waits out once, and one turn of a publish-and-wait loop
/// never comes near: a park in that loop does not run out.
const TRAFFIC_POLL: Duration = Duration::from_secs(1);

/// An exclusive scratch directory under `/tmp` (a Darwin `TMPDIR` is long enough to
/// push a socket path past `SUN_LEN`), removed on drop. Bind it before every broker
/// using it.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/aspp-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Wait until `cond` holds — a one-minute HANG DETECTOR for something that must
/// happen, never a latency budget.
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + HANG;
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::sleep(Duration::from_millis(2));
    }
}

/// A Relaxed broker with a liveness poll of `poll`, served on a Unix socket.
fn serve(s: &Scratch, poll: Duration) -> (Broker, BrokerHandle, PathBuf) {
    let b = Broker::open_with(s.path("b.log"), Durability::Relaxed).unwrap();
    b.set_liveness_poll(poll);
    let sock = s.path("b.sock");
    let h = b.serve(&sock).unwrap();
    (b, h, sock)
}

fn subscribe(sock: &PathBuf, filter: &str) -> Subscription {
    let sub = Client::connect(sock).unwrap().subscribe(0, filter).unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    sub
}

/// The wakeups since `from` once every one of `tails` tails has resumed `expect`
/// times in all and parked again — final, since only a broadcast resumes them then.
fn settled(b: &Broker, from: &BrokerStats, tails: usize, expect: u64) -> BrokerStats {
    until("every woken tail parked again", || {
        let s = b.stats();
        s.tail_wakeups - from.tail_wakeups >= expect && s.parked_tails == tails
    });
    b.stats()
}

/// Three tails that match none of twenty deliverable records each read every one of
/// them, and none probes: its poll is an hour away. The old rule probed whenever a
/// tail wrote nothing and had nothing more to read — three probes per record here.
#[test]
fn a_tail_that_matched_nothing_does_not_probe_before_its_poll() {
    const N: u64 = 20;
    let s = Scratch::new("quiet");
    let (b, _h, sock) = serve(&s, NO_POLL);
    let mut m = subscribe(&sock, "/m/>");
    let _others: Vec<_> = (0..3)
        .map(|i| subscribe(&sock, &format!("/n{i}/>")))
        .collect();
    until("every tail parked", || b.stats().parked_tails == 4);
    let s0 = b.stats();
    let mut p = Client::connect(&sock).unwrap();
    for i in 0..N {
        let (off, _) = p.publish(1, i + 1, "/m/x", b"m").unwrap();
        assert_eq!(m.recv().unwrap().unwrap().0, off);
        // Every tail took this record before the next one is published.
        settled(&b, &s0, 4, 4 * (i + 1));
    }
    let s1 = b.stats();
    assert_eq!(
        s1.tail_wakeups - s0.tail_wakeups,
        4 * N,
        "each tail read each record"
    );
    assert_eq!(
        s1.peer_probes - s0.peer_probes,
        0,
        "a tail probed before its liveness poll came due"
    );
}

/// Negative control, and the parked half of reaping: a parked tail whose poll comes
/// due probes, and once its subscriber has gone the probe reaps the tail's thread and
/// connection.
#[test]
fn a_parked_tail_probes_when_its_poll_is_due_and_reaps_a_vanished_subscriber() {
    let s = Scratch::new("parked");
    let (b, _h, sock) = serve(&s, SHORT_POLL);
    let sub = subscribe(&sock, "/n/>");
    until("the tail parked", || b.stats().parked_tails == 1);
    until("the parked tail probed when due", || {
        b.stats().peer_probes >= 3
    });
    assert_eq!(b.stats().active_conns, 1);
    drop(sub);
    until("the vanished subscriber was reaped", || {
        let s = b.stats();
        s.active_conns == 0 && s.parked_tails == 0
    });
}

/// The other half: a subscriber that left while records it does not match keep
/// arriving is reaped too. Its tail is woken by those records and never writes, so it
/// must probe after reading them, not only when a park runs out: once its poll is due
/// it does.
///
/// ONLY THAT PROBE CAN REAP IT HERE. Two other things would: a park that runs out its
/// poll probes too, and an idle mark is a write, which fails once the subscriber has
/// closed its end. So idle marks are an hour apart (the catch-up mark goes out while
/// the subscriber is still there), the poll is a second, and the records go out in
/// lockstep with the tail — the next one once the tail has read this one and parked
/// again — so each park lasts one turn of this loop, never the second it would take to
/// run out. A tail whose probe after a batch is gone is then reaped by nothing, and
/// this fails at its hang detector, which it did not with a 5 ms poll and idle marks
/// on: there the parked branch or the idle mark reaped the subscriber, and the test
/// passed without the probe it stands for. (A host that stalls this loop for a whole
/// second lets a park run out and probe; that can let such a broken tail pass, never
/// fail a sound one.)
#[test]
fn a_vanished_subscriber_is_reaped_under_traffic_it_does_not_match() {
    let s = Scratch::new("traffic");
    let (b, _h, sock) = serve(&s, TRAFFIC_POLL);
    b.set_idle_mark(NO_POLL);
    let sub = subscribe(&sock, "/never/>");
    until("the tail parked", || b.stats().parked_tails == 1);
    let mut p = Client::connect(&sock).unwrap();
    // One record in lockstep: the tail has read it and parked again, or left.
    let send = |p: &mut Client, seq: u64| {
        let before = b.stats().tail_wakeups;
        p.publish(1, seq, "/other/x", b"o").unwrap();
        until("the tail read the record and parked again, or left", || {
            let s = b.stats();
            s.active_conns == 1 || (s.tail_wakeups > before && s.parked_tails == 1)
        });
    };
    // Its answer says the publisher's connection is registered.
    send(&mut p, 1);
    assert_eq!(
        b.stats().active_conns,
        2,
        "the publisher and the subscriber"
    );
    drop(sub);
    let s0 = b.stats();
    let deadline = Instant::now() + HANG;
    for seq in 2.. {
        send(&mut p, seq);
        if b.stats().active_conns == 1 {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the vanished subscriber was never reaped"
        );
    }
    let s1 = b.stats();
    assert_eq!(s1.parked_tails, 0, "the reaped tail is not parked");
    assert!(s1.peer_probes > s0.peer_probes, "reaped without a probe");
}

/// The probe switches the socket to non-blocking for its one read and back. A stream
/// left non-blocking would fail its next write the moment the subscriber's socket
/// buffer filled, ending the subscription mid-backlog: here the subscriber reads
/// nothing until ~3.8 MB of records it matches are committed, after its tail has
/// probed several times, and then reads every one of them.
#[test]
fn a_probed_stream_still_blocks_when_its_subscriber_falls_behind() {
    const RECORDS: u64 = 64;
    const BODY: usize = 60 * 1024;
    let s = Scratch::new("block");
    let (b, _h, sock) = serve(&s, SHORT_POLL);
    let mut sub = subscribe(&sock, "/big/>");
    until("the tail parked", || b.stats().parked_tails == 1);
    until("the parked tail probed", || b.stats().peer_probes >= 3);
    let mut p = Client::connect(&sock).unwrap();
    for i in 0..RECORDS {
        let body = vec![(i % 251) as u8; BODY];
        assert_eq!(p.publish(1, i + 1, "/big/x", &body).unwrap(), (i, false));
    }
    for i in 0..RECORDS {
        let (off, subject, body) = sub
            .recv()
            .unwrap()
            .unwrap_or_else(|| panic!("the subscription ended at record {i}"));
        assert_eq!((off, subject.as_str()), (i, "/big/x"));
        assert!(body.len() == BODY && body.iter().all(|&x| x == (i % 251) as u8));
    }
}
