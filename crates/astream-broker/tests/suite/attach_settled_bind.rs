// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.attach-settled-bind`: a guarded connection whose principal is
//! already durably bound attaches with NO writer round trip and no empty batch, and
//! its whole handshake — `Hello` and every `Attach` — completes while the writer holds
//! the log lock; a principal's FIRST bind still goes through the writer, exactly once
//! per connection, and a different principal on a bound id is still the writer's to
//! refuse.
//!
//! Before this, every `rw,p=` grant queued a `Bind` to the writer even when the
//! principal was bound long ago: the writer found the binding, appended nothing, and
//! ran an empty batch, behind whatever batch (fsync included) it was already in.
//! aterm's node ring then named one principal in four of its eight grants, so each guarded
//! connection paid four serial writer round trips and four empty batches. The ring aterm
//! mints now, [`GrantCeiling::aterm_node_ring`]'s rules, names it in [`RW`] of eight.
//!
//! Counts, never durations. The seams are [`BrokerStats`]'s `writer_round_trips`,
//! `writer_batches`, `empty_batches` and `binds_settled` (and
//! [`Broker::writer_round_trips`], the one of them readable without the log lock);
//! [`Broker::pause_next_batch`], which parks the writer INSIDE a batch with the log
//! lock held, so "completes without the log lock" is a fact a test can observe: the
//! handshake either returns or hangs; and [`Broker::pause_next_acks`], which parks it
//! after a batch committed and before it answered, so what a batch's acks may rely on
//! is observable too. Every wait for something that must happen is a one-minute HANG
//! DETECTOR, never a latency budget. The negative controls are a first-time principal
//! (it queues one round trip behind the parked writer, and is answered only once its
//! own binding is visible) and a ring of four DIFFERENT new principals (four round
//! trips), so a zero elsewhere is a measurement.

#![cfg(all(unix, feature = "cap"))]

use astream_broker::{Broker, BrokerHandle, BrokerStats, Client, InjectedFaults};
use astream_cap::{mint, producer_id_of, Capability, GrantCeiling};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::TryRecvError;
use std::sync::{mpsc, Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};

const SECRET: &[u8] = b"settled-bind-secret";
const FLEET: &str = "F";

static NEXT: AtomicU64 = AtomicU64::new(0);

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
            let p = PathBuf::from(format!("/tmp/asbs-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn log(&self) -> PathBuf {
        self.0.join("b.log")
    }

    fn sock(&self, n: u32) -> PathBuf {
        self.0.join(format!("b{n}.sock"))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Run `f` on its own thread and wait for it — a one-minute HANG DETECTOR, never a
/// latency budget: something that waits on the log lock while the writer is parked
/// holding it fails here instead of hanging the suite.
fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(Duration::from_secs(60))
        .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
}

/// Wait until `cond` holds — a one-minute HANG DETECTOR for something that must
/// happen, never a latency budget.
fn until(what: &str, mut cond: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(60);
    while !cond() {
        assert!(Instant::now() < deadline, "{what}: never happened");
        thread::sleep(Duration::from_millis(5));
    }
}

/// The read-write grants AS the node in aterm's node ring: each settles or binds once per
/// attach, so every count below is a sum of them.
const RW: u64 = 4;

/// aterm's node ring for `node` on [`FLEET`]: the rules of
/// [`GrantCeiling::aterm_node_ring`], eight grants, [`RW`] of them read-write AS `node`.
/// aterm mints its node ring from those rules (DESIGN-aterm-fabric §8.2), so this is the
/// ring an aterm bridge presents, not a copy of it: a change to the ceiling's read-write
/// grants fails here, before any count below is read.
fn node_ring(node: &str) -> Vec<Capability> {
    let ring: Vec<Capability> = GrantCeiling::aterm_node_ring(FLEET, node)
        .expect("a node's ceiling")
        .rules()
        .iter()
        .map(|g| mint(SECRET, g).unwrap())
        .collect();
    let bound = format!("rw,p={node}:");
    assert_eq!(
        ring.iter().filter(|c| c.filter.starts_with(&bound)).count() as u64,
        RW,
        "the node ring's read-write grants as {node}"
    );
    ring
}

/// Connect and present `ring` under one `Hello`, as aterm's `connect()` does.
fn attach(sock: &PathBuf, ring: &[Capability]) -> Client {
    let mut c = Client::connect(sock).unwrap();
    c.attach_all(ring.iter().map(|g| (g.filter.as_str(), &g.tag[..])))
        .unwrap_or_else(|e| panic!("attach: {e}"));
    c
}

fn serve(s: &Scratch, n: u32) -> (Broker, BrokerHandle) {
    let b = Broker::open_guarded(s.log(), SECRET.to_vec()).unwrap();
    let h = b.serve(s.sock(n)).unwrap();
    (b, h)
}

/// The writer counters' growth from `before` to `after`:
/// `(round trips, batches, empty batches, binds settled)`.
fn grew(before: &BrokerStats, after: &BrokerStats) -> (u64, u64, u64, u64) {
    (
        after.writer_round_trips - before.writer_round_trips,
        after.writer_batches - before.writer_batches,
        after.empty_batches - before.empty_batches,
        after.binds_settled - before.binds_settled,
    )
}

/// The first connection of a new principal binds it through the writer ONCE — its
/// first `rw,p=` grant appends the `/a/bind` record, the others find it settled —
/// and every later connection presenting the same ring (an aterm attach dials three
/// or four) makes no writer round trip and runs no empty batch, yet keeps the
/// authority to publish as that principal.
#[test]
fn a_first_bind_goes_through_the_writer_once_and_a_repeat_principal_never() {
    let s = Scratch::new("once");
    let (b, _h) = serve(&s, 0);
    let ring = node_ring("n-node1");

    let s0 = b.stats();
    let first = attach(&s.sock(0), &ring);
    let s1 = b.stats();
    assert_eq!(
        grew(&s0, &s1),
        (1, 1, 0, RW - 1),
        "a new principal: one writer round trip, one batch holding its /a/bind record, \
         its other rw grants settled"
    );
    assert_eq!(b.head(), 1, "exactly one /a/bind record");
    drop(first);

    let mut before = s1;
    let mut conns = Vec::new();
    for dial in 0..4 {
        conns.push(attach(&s.sock(0), &ring));
        let after = b.stats();
        assert_eq!(
            grew(&before, &after),
            (0, 0, 0, RW),
            "dial {dial} of a bound principal: no writer round trip, no batch, every rw \
             grant settled"
        );
        before = after;
    }
    assert_eq!(b.head(), 1, "and nothing was appended for them");

    let pid = producer_id_of("n-node1");
    assert_eq!(
        conns[0]
            .publish(pid, 1, "/f/F/pub/n-node1/presence", b"up")
            .unwrap(),
        (1, false),
        "the settled ring still publishes as its principal"
    );
}

/// NEGATIVE CONTROL: four read-write grants naming four DIFFERENT new principals make
/// four writer round trips and append four `/a/bind` records — the counter sees every
/// bind the writer is asked for — and presenting the same ring again makes none.
#[test]
fn four_new_principals_make_four_round_trips_and_then_none() {
    let s = Scratch::new("four");
    let (b, _h) = serve(&s, 0);
    let ring: Vec<Capability> = ["n-a", "n-b", "n-c", "n-d"]
        .iter()
        .map(|p| mint(SECRET, &format!("rw,p={p}:/f/F/pub/{p}/>")).unwrap())
        .collect();

    let s0 = b.stats();
    let _c = attach(&s.sock(0), &ring);
    let s1 = b.stats();
    assert_eq!(grew(&s0, &s1), (4, 4, 0, 0), "four first binds");
    assert_eq!(b.head(), 4, "four /a/bind records");

    let _c2 = attach(&s.sock(0), &ring);
    assert_eq!(grew(&s1, &b.stats()), (0, 0, 0, 4), "then all four settled");
}

/// THE HANDSHAKE TAKES NO LOG LOCK. With the writer parked inside a batch, holding
/// the log lock — what a reader met behind a busy Strict writer's fsync before the
/// write and flush left the lock (`broker.unlocked-batch-write`), and still meets while
/// the writer stages — a new
/// connection's `Hello` and its whole eight-grant attach of a bound principal still
/// complete, and `Broker::log_identity` answers, the same identity `Hello` carried.
///
/// NEGATIVE CONTROL in the same window: a principal's FIRST attach needs the writer.
/// Its first read-write grant queues a `Bind` behind the parked batch — seen through
/// [`Broker::writer_round_trips`], which the connection thread bumps before it hands
/// the op over and which needs no log lock — and an attach seen to finish while the
/// test waits for that did not wait for the writer to bind it, which fails at once,
/// not at the minute. Once the batch is resumed the attach completes, and its last ack
/// names head 3: n-node2's own `/a/bind` record sits at offset 2, behind n-node1's at
/// 0 and the parked publish at 1, so the attach was answered only once its binding was
/// durable and visible. An attach that authorized before then would name the head of
/// that moment — 1 while the writer is parked. The counts show exactly one round trip
/// for it.
#[test]
fn the_handshake_of_a_bound_principal_completes_while_the_writer_holds_the_log_lock() {
    let s = Scratch::new("locked");
    let (b, _h) = serve(&s, 0);
    let b = Arc::new(b);
    let sock = s.sock(0);
    let ring = node_ring("n-node1");
    let pid = producer_id_of("n-node1");

    let s0 = b.stats();
    let mut publisher = attach(&sock, &ring); // binds n-node1: 1 round trip, RW - 1 settled
    let identity = b.log_identity();

    let pause = b.pause_next_batch();
    let parked =
        thread::spawn(move || publisher.publish(pid, 1, "/f/F/pub/n-node1/presence", b"x"));
    let pause = within_a_minute("the writer to reach the paused batch", move || {
        assert!(pause.wait(), "the writer stopped before the paused batch");
        pause
    });

    // The writer holds the log lock from here until `resume`.
    let (sock2, ring2) = (sock.clone(), ring.clone());
    let seen = within_a_minute("Hello + attach_all of a bound principal", move || {
        attach(&sock2, &ring2).seen_log_identity()
    });
    assert_eq!(seen, Some(identity), "Hello carried the log's identity");
    let b2 = Arc::clone(&b);
    assert_eq!(
        within_a_minute("Broker::log_identity", move || b2.log_identity()),
        identity
    );

    let queued = b.writer_round_trips();
    let (tx, first_bind) = mpsc::channel();
    let (sock3, ring3) = (sock.clone(), node_ring("n-node2"));
    thread::spawn(move || {
        let mut c = Client::connect(&sock3).unwrap();
        let mark = c
            .attach_all(ring3.iter().map(|g| (g.filter.as_str(), &g.tag[..])))
            .unwrap_or_else(|e| panic!("n-node2's attach: {e}"));
        let _ = tx.send((c, mark));
    });
    until(
        "n-node2's first grant to queue its Bind behind the parked batch",
        || {
            match first_bind.try_recv() {
                Ok(_) => panic!(
                    "a first-time principal's attach finished while the writer was parked: it \
                     did not wait for the writer to bind it"
                ),
                Err(TryRecvError::Disconnected) => panic!("n-node2's attach thread died"),
                Err(TryRecvError::Empty) => {}
            }
            b.writer_round_trips() > queued
        },
    );
    assert!(
        matches!(first_bind.try_recv(), Err(TryRecvError::Empty)),
        "n-node2's attach finished with its Bind still queued behind the parked writer"
    );

    pause.resume();
    let (_node2, mark) = first_bind
        .recv_timeout(Duration::from_secs(60))
        .expect("the first bind completes once the writer resumes");
    assert_eq!(
        mark,
        Some((3, 3)),
        "n-node2's attach is answered only once its own /a/bind record (offset 2) is \
         visible"
    );
    assert_eq!(
        within_a_minute("the parked publish's ack", move || parked.join().unwrap()).unwrap(),
        (1, false)
    );
    assert_eq!(
        grew(&s0, &b.stats()),
        (2, 3, 0, (RW - 1) + RW + (RW - 1)),
        "round trips: n-node1's first bind and n-node2's; batches: those two and the \
         publish; settled: n-node1's other rw grants, the parked-window connection's every \
         one, n-node2's other rw grants"
    );
}

/// Concurrent first attaches of ONE new principal append exactly one `/a/bind` record
/// (the writer, which decides under the log lock, dedups the rest), every attach
/// succeeds, and each of the 32 read-write grants is answered exactly one way — by
/// the writer or as settled — with no more round trips than connections. That bound
/// holds per connection, which a total cannot show (two on one connection beside none
/// on another keep it); the ordering that makes it so — a batch's bindings are copied
/// before any of its acks is sent — is pinned by
/// `a_first_binds_batch_copies_the_binding_before_it_answers`.
#[test]
fn concurrent_first_attaches_of_one_principal_bind_it_once() {
    let s = Scratch::new("race");
    let (b, _h) = serve(&s, 0);
    const CONNS: usize = 8;
    let start = Arc::new(Barrier::new(CONNS));
    let s0 = b.stats();
    let joins: Vec<_> = (0..CONNS)
        .map(|_| {
            let (sock, start) = (s.sock(0), Arc::clone(&start));
            thread::spawn(move || {
                let ring = node_ring("n-race");
                start.wait();
                drop(attach(&sock, &ring));
            })
        })
        .collect();
    for j in joins {
        within_a_minute("a racing attach", move || j.join().unwrap());
    }
    let (round_trips, _, empty, settled) = grew(&s0, &b.stats());
    assert_eq!(
        b.head(),
        1,
        "one /a/bind record, however the attaches raced"
    );
    assert_eq!(
        round_trips + settled,
        RW * CONNS as u64,
        "every rw grant answered once"
    );
    assert!(
        (1..=CONNS as u64).contains(&round_trips),
        "at least the one bind, at most as many round trips as connections: {round_trips}"
    );
    assert!(
        empty < round_trips,
        "only the re-binds that lost the race can be empty batches: {empty} of {round_trips}"
    );
}

/// THE COPY IS REFRESHED BEFORE THE ACKS — the ordering that bounds a connection to
/// ONE writer round trip. A connection's connection thread reads its next grant only
/// once its first grant's `Bind` has been answered, so its later `rw,p=` grants find
/// the binding settled exactly when the batch that appended it copied it before
/// answering. [`Broker::pause_next_acks`] parks the writer at that point — committed,
/// head published, log lock released, not one ack sent — and in that window a SECOND
/// connection presenting the same ring attaches with every grant settled and no round
/// trip. Had the copy come after the acks, that attach's first grant would queue a
/// `Bind` behind the parked writer and never return: the hang detector fails it.
#[test]
fn a_first_binds_batch_copies_the_binding_before_it_answers() {
    let s = Scratch::new("order");
    let (b, _h) = serve(&s, 0);
    let ring = node_ring("n-node1");

    let s0 = b.stats();
    let pause = b.pause_next_acks();
    let (tx, first) = mpsc::channel();
    let (sock1, ring1) = (s.sock(0), ring.clone());
    thread::spawn(move || {
        let _ = tx.send(attach(&sock1, &ring1));
    });
    let pause = within_a_minute("the first bind's batch to reach its acks", move || {
        assert!(
            pause.wait(),
            "the writer stopped before the first bind's acks"
        );
        pause
    });
    // The batch holding n-node1's /a/bind record is committed; nothing is answered,
    // so the first connection is still waiting on its first grant.
    assert!(matches!(first.try_recv(), Err(TryRecvError::Empty)));
    let s1 = b.stats(); // the log lock is free at this point of the batch
    assert_eq!(
        grew(&s0, &s1),
        (1, 1, 0, 0),
        "the first bind queued and its batch committed, nothing settled yet"
    );
    assert_eq!(b.head(), 1, "the /a/bind record is in the log");

    let (sock2, ring2) = (s.sock(0), ring.clone());
    let _second = within_a_minute(
        "a second connection of the principal, with the first bind's acks unsent",
        move || attach(&sock2, &ring2),
    );
    assert_eq!(
        grew(&s1, &b.stats()),
        (0, 0, 0, RW),
        "every rw grant of the second connection settled from the copy, before the batch \
         that bound the principal answered anyone"
    );

    pause.resume();
    let _first = first
        .recv_timeout(Duration::from_secs(60))
        .expect("the first connection's attach completes once the acks go out");
    assert_eq!(
        grew(&s0, &b.stats()),
        (1, 1, 0, (RW - 1) + RW),
        "the first connection: one round trip, its other rw grants settled"
    );
}

/// ON A POISONED LOG — the one place an attach answered from the copy differs from
/// one the writer answers. A principal bound (and so copied) before the log poisoned
/// still attaches, with no round trip, and every publish it makes is refused by the
/// log (`log poisoned`), so the attach authorizes nothing the log will take; a
/// first-time principal still goes to the writer, which refuses its binding as before
/// (`the producer binding was not persisted`). The writer used to refuse a repeat
/// principal's attach the same way; now its reads still work until the reopen.
#[test]
fn on_a_poisoned_log_a_copied_binding_attaches_and_its_publishes_are_refused() {
    let s = Scratch::new("poison");
    let (b, _h) = serve(&s, 0);
    let ring = node_ring("n-node1");
    let pid = producer_id_of("n-node1");
    let mut c = attach(&s.sock(0), &ring);
    assert_eq!(
        c.publish(pid, 1, "/f/F/pub/n-node1/presence", b"up")
            .unwrap(),
        (1, false)
    );
    // A failed fsync whose rollback truncate also fails poisons the log until reopen.
    b.inject_faults(InjectedFaults {
        write: false,
        sync: true,
        truncate: true,
    });
    let e = c
        .publish(pid, 2, "/f/F/pub/n-node1/presence", b"lost")
        .unwrap_err();
    assert!(e.to_string().contains("commit failed"), "{e}");
    b.inject_faults(InjectedFaults::default());
    assert!(b.stats().log.poisoned, "the log is poisoned");

    let s0 = b.stats();
    let mut again = attach(&s.sock(0), &ring);
    assert_eq!(
        grew(&s0, &b.stats()),
        (0, 0, 0, RW),
        "a binding copied before the poisoning attaches settled"
    );
    let e = again
        .publish(pid, 3, "/f/F/pub/n-node1/presence", b"after")
        .unwrap_err();
    assert!(
        e.to_string().contains("poisoned"),
        "its publish is refused by the poisoned log: {e}"
    );

    // One grant, not the ring: every `rw,p=` grant of a principal the writer refuses
    // goes back to the writer, and one is the case to count.
    let s1 = b.stats();
    let fresh = mint(SECRET, "rw,p=n-node2:/f/F/pub/n-node2/>").unwrap();
    let e = Client::connect(s.sock(0))
        .unwrap()
        .attach(&fresh.filter, &fresh.tag)
        .unwrap_err();
    assert!(
        e.to_string()
            .contains("the producer binding was not persisted")
            && e.to_string().contains("poisoned"),
        "a first-time principal's binding is refused by the writer: {e}"
    );
    assert_eq!(
        grew(&s1, &b.stats()),
        (1, 1, 1, 0),
        "one round trip to the writer, which appended nothing"
    );
    assert_eq!(b.head(), 2, "nothing landed after the poisoning");
}

/// The pause seam never wedges a test: [`Broker::pause_next_batch`] and
/// [`Broker::pause_next_acks`] armed on a broker whose writer then stops without
/// reaching them — and armed after it has stopped — answer `wait` with `false`,
/// instead of blocking for as long as the `Broker` lives.
#[test]
fn a_batch_pause_the_writer_never_reaches_answers_false_once_it_stops() {
    let s = Scratch::new("stop");
    let (b, mut h) = serve(&s, 0);
    let staged = b.pause_next_batch();
    within_a_minute("shutdown", move || h.shutdown());
    assert!(
        !within_a_minute(
            "wait on a pause armed before the writer stopped",
            move || staged.wait()
        ),
        "the writer stopped without reaching the pause"
    );
    let staged = b.pause_next_batch();
    let acks = b.pause_next_acks();
    assert!(!within_a_minute(
        "wait on pause_next_batch armed after the writer stopped",
        move || staged.wait()
    ));
    assert!(!within_a_minute(
        "wait on pause_next_acks armed after the writer stopped",
        move || acks.wait()
    ));
}

/// A DIFFERENT principal on a bound id is never answered from the broker's copy of
/// the binding table: it goes to the writer, which refuses it (`producer id
/// collision`) — one round trip per attempt, none settled — exactly as before.
///
/// A real SHA-256/64 collision cannot be searched for in a test, so the table is
/// forced into the colliding state through `Replicate` (as `cap_keyring.rs` does);
/// that binding reaches the copy like any other the log promotes.
#[test]
fn a_different_principal_on_a_bound_id_still_goes_to_the_writer() {
    use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
    use astream_broker::{Request, Response};

    let s = Scratch::new("collide");
    let (b, _h) = serve(&s, 0);
    let victim = mint(SECRET, "rw,p=n-victim:/f/F/>").unwrap();
    let root = mint(SECRET, "/a/>").unwrap(); // unbound rw: binds nothing
    let mut r = attach(&s.sock(0), &[root]).into_stream();
    write_frame(
        &mut r,
        &encode_request(&Request::Replicate {
            seq: 0,
            producer_id: producer_id_of("n-victim"),
            producer_seq: 0,
            subject: "/a/bind".to_string(),
            body: b"n-imposter".to_vec(),
            commit: None,
            leader: None,
        }),
    )
    .unwrap();
    assert_eq!(
        decode_response(&read_frame(&mut r).unwrap().unwrap()),
        Some(Response::PublishAck {
            offset: 0,
            deduped: false
        })
    );

    for attempt in 0..2 {
        let s0 = b.stats();
        let mut c = Client::connect(s.sock(0)).unwrap();
        let e = c.attach(&victim.filter, &victim.tag).unwrap_err();
        assert!(
            e.to_string().contains("producer id collision"),
            "attempt {attempt}: expected the writer's collision refusal, got: {e}"
        );
        assert_eq!(
            grew(&s0, &b.stats()),
            (1, 1, 1, 0),
            "attempt {attempt}: one round trip to the writer, nothing settled"
        );
    }
}

/// A binding seen once STAYS settled: across a restart (the copy is rebuilt from the
/// log at open, so a repeat principal's first connection after it makes no round
/// trip), and past retention — `retain_before` refuses to drop the binding's record,
/// and `retain_before_carrying_state` drops it from the file while carrying the
/// binding in `<log>.state`, after which the principal is still settled, before and
/// after another restart.
#[cfg(feature = "retention")]
#[test]
fn a_binding_stays_settled_across_restarts_and_retention() {
    let s = Scratch::new("keep");
    let ring = node_ring("n-node1");
    let pid = producer_id_of("n-node1");
    {
        let (b, mut h) = serve(&s, 0);
        let mut c = attach(&s.sock(0), &ring);
        for seq in 1..=3 {
            c.publish(pid, seq, "/f/F/pub/n-node1/ev", b"e").unwrap();
        }
        assert_eq!(b.head(), 4, "the bind record and three publishes");
        drop(c);
        within_a_minute("shutdown", move || h.shutdown());
    }

    let (b, mut h) = serve(&s, 1);
    let s0 = b.stats();
    let _c = attach(&s.sock(1), &ring);
    assert_eq!(
        grew(&s0, &b.stats()),
        (0, 0, 0, RW),
        "after a restart: settled from the rebuilt table, no round trip"
    );

    let e = b.retain_before(4).unwrap_err();
    assert!(
        e.to_string().contains("binding"),
        "retention refuses to drop the binding's record: {e}"
    );
    assert_eq!(b.retain_before_carrying_state(4).unwrap(), 4);
    assert_eq!(b.stats().log.base.0, 4, "the /a/bind record left the file");
    let s1 = b.stats();
    let mut c = attach(&s.sock(1), &ring);
    assert_eq!(
        grew(&s1, &b.stats()),
        (0, 0, 0, RW),
        "past retention: still settled"
    );
    assert_eq!(
        c.publish(pid, 4, "/f/F/pub/n-node1/ev", b"e").unwrap(),
        (4, false)
    );
    drop(c);
    within_a_minute("shutdown", move || h.shutdown());
    drop(b);

    let (b, _h) = serve(&s, 2);
    let s2 = b.stats();
    let _c = attach(&s.sock(2), &ring);
    assert_eq!(
        grew(&s2, &b.stats()),
        (0, 0, 0, RW),
        "after retention and a restart: rebuilt from <log>.state, still settled"
    );
}
