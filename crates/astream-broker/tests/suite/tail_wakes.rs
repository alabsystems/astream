// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.targeted-tail-wake`: the writer wakes the parked subscriber
//! tails only after a batch that made a record some subscriber could be delivered
//! visible. A batch that made nothing visible (a deduplicated retry) and one whose
//! records are all hidden (a group commit, a will registration, a retirement, a
//! guarded attach's first bind) wake nobody, and a tail parked past such a batch still
//! ends at shutdown and at its authority's lapse, and still reports a cursor past the
//! hidden records in its idle marks. In the Replicated tier what a batch makes visible
//! is what the quorum watermark newly passed, so there a deduplicated retry or a group
//! commit whose ship confirms an earlier publish does wake the tails, and a publish no
//! quorum confirmed does not.
//!
//! Before this every batch woke every parked tail, so a lone delivery through aterm's
//! bridge was two broadcasts — the publish and the commit of the inbox group after it —
//! and with S parked tails, 2S wakeups (cost study B4 step 1). A LONE delivery: aterm
//! commits its inbox group once per burst (aterm `78e8cbfdaf`: once no inbox record is
//! queued, or every 256 records), so only a delivery nothing is queued behind pays a
//! commit of its own, and a refused record's notice and its commit go out together as
//! one `ProcessAndProduce` ack, one batch.
//!
//! Counts, never durations. The seams are [`BrokerStats`]'s `tail_broadcasts` (the
//! writer's `notify_all`s), `tail_wakeups` (each resume of a parked tail, counted under
//! the log lock), `parked_tails` (a gauge, counted under the lock the writer publishes
//! the head under, so a head published after it reads N finds N tails waiting) and
//! `writer_batches`/`empty_batches`. Every broker here sets a liveness poll of an hour
//! ([`Broker::set_liveness_poll`]) unless the test is about the poll, so no poll
//! timeout lands inside a count. The writer acks a batch before it decides whether to
//! broadcast, so a broadcast count is read only after a LATER op's ack — the writer is
//! one thread, and it starts the next batch only once the last one is done. Every
//! wait for something that must happen is a one-minute HANG DETECTOR, never a latency
//! budget. The negative control is in every test: a deliverable publish broadcasts
//! once and resumes every parked tail, so a zero beside it is a measurement.

#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, BrokerStats, Client, Durability, Event, Subscription};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// A wait for something that must happen: a hang detector, never a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// A liveness poll no test outlasts: no parked tail times out inside a count.
const NO_POLL: Duration = Duration::from_secs(3600);

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
            let p = PathBuf::from(format!("/tmp/astw-{tag}-{}-{n}", std::process::id()));
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

/// A Relaxed broker (no fsync to wait out; the wake decision does not read the tier)
/// with a liveness poll of `poll`, served on a Unix socket.
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

/// One matching tail on `/m/>` and `others` on `/n<i>/>`, which nothing here publishes
/// to — every one of them parked before this returns.
fn tails(b: &Broker, sock: &PathBuf, others: usize) -> (Subscription, Vec<Subscription>) {
    let m = subscribe(sock, "/m/>");
    let n = (0..others)
        .map(|i| subscribe(sock, &format!("/n{i}/>")))
        .collect();
    until("every tail parked", || b.stats().parked_tails == others + 1);
    (m, n)
}

/// After a delivery that resumed `tails` parked tails: wait until every one of them
/// has resumed and parked again, then return the wakeups counted since `from`. Once
/// all of them are parked again nothing resumes them but another broadcast, so the
/// count read here is final.
fn settled_wakeups(b: &Broker, from: &BrokerStats, tails: usize, expect: u64) -> u64 {
    until("every woken tail parked again", || {
        let s = b.stats();
        s.tail_wakeups - from.tail_wakeups >= expect && s.parked_tails == tails
    });
    b.stats().tail_wakeups - from.tail_wakeups
}

/// The next delivery on `sub`, skipping its marks: `(offset, subject)`.
fn next(sub: &mut Subscription) -> (u64, String) {
    let (off, subject, _) = sub.recv().unwrap().expect("the subscription ended");
    (off, subject)
}

/// A batch the writer appends nothing for: producer 1's sequence 1 again. Its ack
/// also says the writer has finished every batch before it, broadcast included.
fn fence(c: &mut Client) {
    let (_, deduped) = c.publish(1, 1, "/m/x", b"m").unwrap();
    assert!(deduped, "the fence re-sends producer 1's sequence 1");
}

#[test]
fn a_batch_with_nothing_deliverable_wakes_no_tail() {
    let s = Scratch::new("quiet");
    let (b, _h, sock) = serve(&s, NO_POLL);
    let (mut m, _others) = tails(&b, &sock, 3);
    let mut c = Client::connect(&sock).unwrap();

    // Negative control: each deliverable publish broadcasts once and resumes all four.
    let s0 = b.stats();
    assert_eq!(c.publish(1, 1, "/m/x", b"m").unwrap(), (0, false));
    assert_eq!(next(&mut m), (0, "/m/x".to_string()));
    assert_eq!(
        settled_wakeups(&b, &s0, 4, 4),
        4,
        "one resume per parked tail"
    );
    assert_eq!(c.publish(4, 1, "/m/r", b"r").unwrap(), (1, false));
    assert_eq!(next(&mut m), (1, "/m/r".to_string()));
    assert_eq!(
        settled_wakeups(&b, &s0, 4, 8),
        8,
        "one resume per parked tail"
    );

    // A group commit, a will registration and a retirement append only hidden
    // records; a deduplicated retry appends nothing. The second retry's ack says the
    // writer finished every batch before it, broadcast decision included.
    let s1 = b.stats();
    c.commit("g", 0).unwrap();
    let mut w = Client::connect(&sock).unwrap();
    w.will(2, 1, "/m/gone", b"bye").unwrap();
    assert!(!c.retire_subject(4, "/m/r").unwrap().1, "/m/r was retired");
    fence(&mut c);
    fence(&mut c);
    let s2 = b.stats();
    assert_eq!(s2.writer_batches - s1.writer_batches, 5, "five batches");
    assert_eq!(s2.empty_batches - s1.empty_batches, 2, "two of them empty");
    assert_eq!(s2.visible_head, 5, "three hidden records above /m/r@1");
    assert_eq!(
        s2.tail_broadcasts - s1.tail_broadcasts,
        0,
        "a hidden-only or empty batch broadcast to the tails"
    );
    assert_eq!(s2.parked_tails, 4, "every tail stayed parked");

    // The next deliverable record wakes each tail once more, and only once: had the
    // five quiet batches resumed anyone, the count here would be past four.
    let (off, _) = c.publish(3, 1, "/m/y", b"y").unwrap();
    assert_eq!(off, 5);
    assert_eq!(
        next(&mut m),
        (5, "/m/y".to_string()),
        "past the hidden records"
    );
    assert_eq!(
        settled_wakeups(&b, &s1, 4, 4),
        4,
        "one resume per parked tail"
    );
    fence(&mut c);
    assert_eq!(b.stats().tail_broadcasts - s1.tail_broadcasts, 1);
    drop(w);
}

/// A lone delivery through aterm's bridge: a publish, its delivery, then a commit of
/// the inbox group (aterm commits once per burst, so each message here is a burst of
/// one). With S parked tails that is now one broadcast and S wakeups per message, where
/// it was two broadcasts and up to 2S.
#[test]
fn a_publish_then_commit_message_wakes_each_tail_once() {
    const N: u64 = 20;
    const TAILS: usize = 4;
    let s = Scratch::new("msg");
    let (b, _h, sock) = serve(&s, NO_POLL);
    let (mut m, _others) = tails(&b, &sock, TAILS - 1);
    let mut p = Client::connect(&sock).unwrap();
    let mut cm = Client::connect(&sock).unwrap();
    let s0 = b.stats();
    for i in 0..N {
        let (off, _) = p.publish(1, i + 1, "/m/x", b"m").unwrap();
        assert_eq!(next(&mut m), (off, "/m/x".to_string()));
        assert_eq!(
            settled_wakeups(&b, &s0, TAILS, TAILS as u64 * (i + 1)),
            TAILS as u64 * (i + 1),
            "message {i}: one resume per tail per message"
        );
        cm.commit("g", off).unwrap();
    }
    let (_, deduped) = p.publish(1, N, "/m/x", b"m").unwrap();
    assert!(deduped);
    let s1 = b.stats();
    assert_eq!(s1.writer_batches - s0.writer_batches, 2 * N + 1);
    assert_eq!(
        s1.tail_broadcasts - s0.tail_broadcasts,
        N,
        "one per message"
    );
    assert_eq!(s1.tail_wakeups - s0.tail_wakeups, TAILS as u64 * N);
}

/// Replicated tier: the visible head is the quorum watermark, so a record becomes
/// visible when a quorum holds it, and the broadcast follows what the watermark
/// passed. On the follower, which is an ordinary broker taking `Replicate` ops, the
/// leader's commit record is hidden there too.
#[test]
fn the_replicated_tier_wakes_for_what_a_quorum_newly_holds() {
    let s = Scratch::new("rep");
    let follower = Broker::open(s.path("f.log")).unwrap();
    follower.set_liveness_poll(NO_POLL);
    let fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let fsock = s.path("f.sock");
    let _fu = follower.serve(&fsock).unwrap();
    let leader = Broker::open_replicated(s.path("l.log"), std::slice::from_ref(&faddr), 1).unwrap();
    leader.set_liveness_poll(NO_POLL);
    let lsock = s.path("l.sock");
    let _lh = leader.serve(&lsock).unwrap();

    let mut on_leader = subscribe(&lsock, "/m/>");
    until("the leader's tail parked", || {
        leader.stats().parked_tails == 1
    });
    let mut on_follower = subscribe(&fsock, "/m/>");
    until("the follower's tail parked", || {
        follower.stats().parked_tails == 1
    });
    let (l0, f0) = (leader.stats(), follower.stats());

    let mut c = Client::connect(&lsock).unwrap();
    assert_eq!(c.publish(1, 1, "/m/x", b"m").unwrap(), (0, false));
    assert_eq!(next(&mut on_leader), (0, "/m/x".to_string()));
    assert_eq!(next(&mut on_follower), (0, "/m/x".to_string()));
    c.commit("g", 0).unwrap();
    fence(&mut c);
    let l1 = leader.stats();
    assert_eq!(l1.visible_head, 2, "the commit is quorum-held");
    assert_eq!(
        l1.tail_broadcasts - l0.tail_broadcasts,
        1,
        "the leader broadcast for /m/x and not for the commit"
    );
    // The follower held the commit before the leader acked it. A commit of its own is
    // another batch through the follower's writer, hidden too, and its answer says
    // that writer is past the replicated commit's batch.
    assert_eq!(follower.stats().visible_head, 2);
    let _ = Client::connect(&fsock).unwrap().commit("h", 0);
    let f1 = follower.stats();
    assert_eq!(
        f1.tail_broadcasts - f0.tail_broadcasts,
        1,
        "the follower broadcast for /m/x and not for the commit"
    );
    drop(fh);
}

/// A Replicated leader (quorum 1, an hour's poll) with one tail parked on `/m/>`, whose
/// only follower is down, and on it `/m/x@0`: committed on the leader, refused for want
/// of a quorum, and so invisible. Nothing has broadcast for it.
struct Unconfirmed {
    leader: Broker,
    _lh: BrokerHandle,
    tail: Subscription,
    client: Client,
    flog: PathBuf,
    faddr: String,
    /// The stats once `/m/x`'s batch is done, before the follower comes back.
    before: BrokerStats,
}

fn is_quorum_refusal(e: &std::io::Error) -> bool {
    e.to_string().contains("not replicated to quorum")
}

impl Unconfirmed {
    fn new(s: &Scratch) -> Unconfirmed {
        let flog = s.path("f.log");
        let follower = Broker::open(&flog).unwrap();
        let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
        let faddr = fh.tcp_addr().unwrap().to_string();
        let leader =
            Broker::open_replicated(s.path("l.log"), std::slice::from_ref(&faddr), 1).unwrap();
        leader.set_liveness_poll(NO_POLL);
        let lsock = s.path("l.sock");
        let lh = leader.serve(&lsock).unwrap();
        let tail = subscribe(&lsock, "/m/>");
        until("the leader's tail parked", || {
            leader.stats().parked_tails == 1
        });
        // Down: the last listener's shutdown closes the leader's link and releases the
        // follower's log for `revive` to reopen.
        fh.shutdown();
        drop(follower);
        let s0 = leader.stats();
        let mut client = Client::connect(&lsock).unwrap();
        let e = client.publish(1, 1, "/m/x", b"m").unwrap_err();
        assert!(is_quorum_refusal(&e), "{e}");
        // The retry, while the follower is still down, is refused the same way, and its
        // answer says `/m/x`'s batch is done, broadcast decision included.
        let e = client.publish(1, 1, "/m/x", b"m").unwrap_err();
        assert!(is_quorum_refusal(&e), "{e}");
        let before = leader.stats();
        assert_eq!(before.visible_head, 0, "no quorum holds /m/x");
        assert_eq!(
            before.tail_broadcasts - s0.tail_broadcasts,
            0,
            "a batch whose publish no quorum confirmed broadcast"
        );
        assert_eq!(before.parked_tails, 1);
        Unconfirmed {
            leader,
            _lh: lh,
            tail,
            client,
            flog,
            faddr,
            before,
        }
    }

    /// The follower again, on its address and its log: the next batch re-dials it and
    /// ships it what it lacks, `/m/x` first.
    fn revive(&self) -> (Broker, BrokerHandle) {
        let follower = Broker::open(&self.flog).unwrap();
        let fh = follower.serve_tcp(&self.faddr).unwrap();
        (follower, fh)
    }

    /// `op` again until it is not refused for want of a quorum, and what it returned
    /// then, with the number of refusals before it. The first ship to the revived
    /// follower is on a fresh link, which gets one ack read within
    /// `REPLICA_IO_TIMEOUT` and no second try: a loaded host that stalls the follower
    /// past it fails that batch's confirmation, and the link is dialed again by the
    /// next batch. So the refusals are counted, not assumed to be none. Each one is a
    /// batch whose ship confirmed nothing and so broadcast nothing, which
    /// [`Self::confirmed_by_a_later_batch`] checks with the exact counts.
    fn until_confirmed<T>(
        &mut self,
        mut op: impl FnMut(&mut Client) -> std::io::Result<T>,
    ) -> (T, u64) {
        let deadline = Instant::now() + HANG;
        let mut refused = 0;
        loop {
            match op(&mut self.client) {
                Ok(v) => return (v, refused),
                Err(e) if is_quorum_refusal(&e) => refused += 1,
                Err(e) => panic!("{e}"),
            }
            assert!(
                Instant::now() < deadline,
                "no ship to the revived follower confirmed"
            );
        }
    }

    /// After the batch that confirmed `/m/x` and a fence behind it: that batch, and
    /// nothing else, broadcast, and the parked tail was resumed once and delivered
    /// `/m/x`. With the broadcast range narrowed to the batch's own appends — the Strict
    /// and Relaxed range, which is wrong here — the count is 0 and the tail sleeps an
    /// hour.
    fn confirmed_by_a_later_batch(&mut self, visible: u64, empty: u64) {
        let s = self.leader.stats();
        assert_eq!(s.visible_head, visible, "the ship confirmed /m/x");
        assert_eq!(s.empty_batches - self.before.empty_batches, empty);
        assert_eq!(
            s.tail_broadcasts - self.before.tail_broadcasts,
            1,
            "the batch whose ship confirmed /m/x did not broadcast for it"
        );
        assert_eq!(next(&mut self.tail), (0, "/m/x".to_string()));
        assert_eq!(settled_wakeups(&self.leader, &self.before, 1, 1), 1);
    }
}

/// An empty batch can broadcast in the Replicated tier: the retry of a publish refused
/// for want of a quorum appends nothing — the leader already holds the record — but
/// its ship confirms the record, which makes it visible.
#[test]
fn a_retry_whose_ship_confirms_its_refused_publish_wakes_the_tails() {
    let s = Scratch::new("retry");
    let mut u = Unconfirmed::new(&s);
    let _follower = u.revive();
    let (ack, refused) = u.until_confirmed(|c| c.publish(1, 1, "/m/x", b"m"));
    assert_eq!(ack, (0, true), "the retry deduplicated and was confirmed");
    fence(&mut u.client);
    // Empty batches: each refused retry, the confirmed retry and the fence.
    u.confirmed_by_a_later_batch(1, refused + 2);
}

/// A hidden-only batch can broadcast in the Replicated tier: a group commit appends
/// only a hidden record, but its ship confirms the deliverable record an earlier batch
/// appended, which makes that record visible. A lone delivery's commit (aterm's bridge
/// commits once per burst, so a delivery nothing is queued behind is followed by its
/// own) is this batch when it follows a publish refused while a follower was away.
#[test]
fn a_commit_whose_ship_confirms_an_earlier_publish_wakes_the_tails() {
    let s = Scratch::new("later");
    let mut u = Unconfirmed::new(&s);
    let _follower = u.revive();
    // A refused commit is still appended on the leader, a hidden record after /m/x@0.
    let (off, refused) = u.until_confirmed(|c| c.commit("g", 0));
    assert_eq!(
        off,
        1 + refused,
        "the confirmed commit follows each refused one"
    );
    fence(&mut u.client);
    // One empty batch: the fence.
    u.confirmed_by_a_later_batch(2 + refused, 1);
}

/// A tail left parked past a hidden-only batch still ends at shutdown: shutdown
/// broadcasts on its own, and the tail reads past the hidden record on its way out.
#[test]
fn shutdown_still_ends_a_tail_parked_past_a_hidden_batch() {
    let s = Scratch::new("down");
    let (b, mut h, sock) = serve(&s, NO_POLL);
    let (mut m, _others) = tails(&b, &sock, 1);
    let mut c = Client::connect(&sock).unwrap();
    // Two commits: the second one's ack says the first one's batch is done.
    c.commit("g", 0).unwrap();
    c.commit("g", 0).unwrap();
    let s1 = b.stats();
    assert_eq!(s1.visible_head, 2);
    assert_eq!(s1.tail_broadcasts, 0);
    assert_eq!(
        s1.parked_tails, 2,
        "both tails parked past the first commit"
    );
    h.shutdown();
    until("both tails left their wait", || b.stats().parked_tails == 0);
    assert!(
        matches!(m.recv(), Ok(None) | Err(_)),
        "the subscription ended with the broker"
    );
}

/// The checker's caveat on skipping hidden-only batches: would it delay an observer
/// that reads the tail's cursor off its `Mark`s? A tail not woken for a commit still
/// reads past it at its next liveness poll, so its next idle mark names a cursor past
/// the hidden record, with nothing deliverable published after it.
#[test]
fn an_idle_mark_names_a_cursor_past_hidden_records() {
    let s = Scratch::new("mark");
    let (b, _h, sock) = serve(&s, Duration::from_millis(20));
    b.set_idle_mark(Duration::from_millis(50));
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/m/>")
        .unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    assert_eq!(
        sub.recv_event().unwrap(),
        Some(Event::Mark {
            next: 0,
            head: 0,
            durable: Some(0)
        }),
        "the catch-up mark"
    );
    let mut c = Client::connect(&sock).unwrap();
    c.commit("g", 0).unwrap();
    c.commit("g", 0).unwrap();
    let deadline = Instant::now() + HANG;
    loop {
        match sub.recv_event().unwrap() {
            Some(Event::Mark { next: 2, head, .. }) => {
                assert_eq!(head, 2);
                break;
            }
            Some(Event::Mark { next, head, .. }) => assert!(next <= head && head <= 2),
            other => panic!("only marks: {other:?}"),
        }
        assert!(Instant::now() < deadline, "no mark ever passed the commits");
    }
    assert_eq!(
        b.stats().tail_broadcasts,
        0,
        "nothing deliverable was published"
    );
}

/// A guarded attach's FIRST bind of a principal appends a hidden `/a/bind` record:
/// the batch that carries it wakes no tail.
#[cfg(feature = "cap")]
#[test]
fn a_first_bind_wakes_no_tail() {
    use astream_cap::mint;
    const SECRET: &[u8] = b"tail-wake-secret";
    let s = Scratch::new("bind");
    let b =
        Broker::open_guarded_with(s.path("b.log"), SECRET.to_vec(), Durability::Relaxed).unwrap();
    b.set_liveness_poll(NO_POLL);
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();
    let ro = mint(SECRET, "ro:/m/>").unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&ro.filter, &ro.tag).unwrap();
    let mut sub = r.subscribe(0, "/m/>").unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    until("the tail parked", || b.stats().parked_tails == 1);

    let rw = mint(SECRET, "rw,p=n-0102030405060708:/m/>").unwrap();
    let pid = astream_cap::producer_id_of("n-0102030405060708");
    let mut c = Client::connect(&sock).unwrap();
    c.attach(&rw.filter, &rw.tag).unwrap();
    let s1 = b.stats();
    assert_eq!(s1.visible_head, 1, "the bind appended its hidden record");
    assert_eq!(s1.writer_round_trips, 1);
    // Negative control, and the fence for the bind's batch: a publish broadcasts.
    assert_eq!(c.publish(pid, 1, "/m/x", b"m").unwrap(), (1, false));
    assert_eq!(next(&mut sub), (1, "/m/x".to_string()));
    let (_, deduped) = c.publish(pid, 1, "/m/x", b"m").unwrap();
    assert!(deduped);
    assert_eq!(
        b.stats().tail_broadcasts,
        1,
        "the bind's batch broadcast to the tails"
    );
}

/// A tail left parked past a hidden-only batch still ends at its authority's lapse:
/// its wait is bounded by the lapse, not by a broadcast, and on waking it reads past
/// the hidden records into the refusal.
///
/// The lapse is a wall-clock instant fixed before the tail exists, so an attempt shows
/// the claim only if the tail parked and both commits were acked before it. Each
/// attempt checks that order itself. An attempt the host lost (a loaded host can spend
/// the whole window before the tail parks, and a tail that never parks would leave a
/// wait for the park hanging) is redone on a fresh broker with twice the window,
/// never passed. Five attempts span 1 s to 16 s, inside the one-minute HANG.
#[cfg(feature = "cap")]
#[test]
fn a_lapse_still_ends_a_tail_parked_past_a_hidden_batch() {
    let mut window_ms = 1_000;
    for attempt in 1..=5 {
        if lapse_after_two_commits(window_ms) {
            return;
        }
        eprintln!("lapse attempt {attempt}: the {window_ms} ms window ran out first; doubling");
        window_ms *= 2;
    }
    panic!("in five attempts up to 16 s the tail never parked past two commits before its lapse");
}

/// One attempt of [`a_lapse_still_ends_a_tail_parked_past_a_hidden_batch`] with a
/// read capability that lapses `window_ms` from now: `false` if the lapse came before
/// the tail parked or before the second commit's ack, so nothing was shown; otherwise
/// every assertion of the claim, and `true`.
#[cfg(feature = "cap")]
fn lapse_after_two_commits(window_ms: u64) -> bool {
    use astream_broker::{broker_refusal, BrokerRefusal};
    use astream_cap::mint;
    use std::time::{SystemTime, UNIX_EPOCH};
    const SECRET: &[u8] = b"tail-wake-secret";
    let now_ms = || {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_millis() as u64)
    };
    let s = Scratch::new("lapse");
    let b =
        Broker::open_guarded_with(s.path("b.log"), SECRET.to_vec(), Durability::Relaxed).unwrap();
    b.set_liveness_poll(NO_POLL);
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();
    let god = mint(SECRET, "rw:/>").unwrap();
    let mut w = Client::connect(&sock).unwrap();
    w.attach(&god.filter, &god.tag).unwrap();
    let soon = now_ms() + window_ms;
    let ro = mint(SECRET, &format!("ro,exp={soon}:/m/>")).unwrap();
    let mut r = Client::connect(&sock).unwrap();
    if let Err(e) = r.attach(&ro.filter, &ro.tag) {
        assert!(now_ms() >= soon, "attach refused before its lapse: {e}");
        return false;
    }
    let mut sub = r.subscribe(0, "/m/>").unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    // The park, or the lapse: a tail the lapse ended first never parks.
    until("the tail parked or its capability lapsed", || {
        b.stats().parked_tails == 1 || now_ms() >= soon
    });
    if b.stats().parked_tails != 1 {
        return false;
    }
    // A guarded broker authorizes a group as a subject.
    w.commit("/w/group/g", 0).unwrap();
    w.commit("/w/group/g", 0).unwrap();
    if now_ms() >= soon {
        return false;
    }
    // The tail was parked before the first commit and its park is bounded by the lapse,
    // which had not come when the second commit's ack (and so the first's batch) was
    // done: it was parked past both hidden records.
    assert_eq!(b.stats().tail_broadcasts, 0, "the commits broadcast");
    let err = sub
        .recv()
        .expect_err("a tail parked past a commit outlived its capability");
    assert!(
        broker_refusal(&err).is_some_and(BrokerRefusal::is_expired),
        "a parked stream ended at its deadline must read as expired: {err}"
    );
    assert!(now_ms() >= soon, "refused before its deadline");
    assert_eq!(b.stats().parked_tails, 0);
    true
}

/// Filter-indexed selective tail wakeups (`cost study B4 step 2`): with 1 matching
/// subscriber (`/m/>`) and 16 disjoint subscribers (`/n0/>`..`/n15/>`), 200 lone
/// deliveries (`publish` + `commit`) resume ONLY the 1 matching tail (`200` wakeups
/// total instead of `17 * 200 = 3,400`), emit `0` shared broadcasts, and record `200`
/// `selective_tail_wakes`. When `/n11/hi` is then published at offset `400`, `/n11/>`
/// skips `[0 .. 400)` in `O(1)` and delivers `(400, "/n11/hi")` with 1 wakeup.
#[test]
fn selective_tail_wake_resumes_only_matching_subscribers_and_skips_quiet_prefixes() {
    use astream_broker::{OpenOptions, Prepared};
    const K: usize = 16;
    const N: u64 = 200;
    let s = Scratch::new("sel16");
    let mut opts = OpenOptions::new(Durability::Relaxed);
    opts.selective_tail_wake = true;
    let b = Broker::open_opts(s.path("b.log"), opts, || Ok(Prepared::Nothing)).unwrap();
    assert!(b.selective_tail_wake());
    b.set_liveness_poll(NO_POLL);
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();
    let (mut m, mut others) = tails(&b, &sock, K);
    let mut p = Client::connect(&sock).unwrap();
    let mut cm = Client::connect(&sock).unwrap();
    let s0 = b.stats();
    for i in 0..N {
        let (off, _) = p.publish(1, i + 1, "/m/x", b"m").unwrap();
        assert_eq!(next(&mut m), (off, "/m/x".to_string()));
        assert_eq!(
            settled_wakeups(&b, &s0, K + 1, i + 1),
            i + 1,
            "message {i}: only the 1 matching subscriber woke"
        );
        cm.commit("g", off).unwrap();
    }
    let (_, deduped) = p.publish(1, N, "/m/x", b"m").unwrap();
    assert!(deduped);
    let s1 = b.stats();
    assert_eq!(s1.visible_head, 2 * N);
    assert_eq!(s1.tail_broadcasts - s0.tail_broadcasts, 0);
    assert_eq!(s1.selective_tail_wakes - s0.selective_tail_wakes, N);
    assert_eq!(s1.tail_wakeups - s0.tail_wakeups, N);

    // Now publish to `/n11/hi` at offset 400: only `/n11/>` wakes and skips `0..400`.
    let (off11, _) = p.publish(2, 1, "/n11/hi", b"hello").unwrap();
    assert_eq!(off11, 2 * N);
    assert_eq!(next(&mut others[11]), (off11, "/n11/hi".to_string()));
    assert_eq!(settled_wakeups(&b, &s1, K + 1, 1), 1);
    let (_, dedup2) = p.publish(2, 1, "/n11/hi", b"hello").unwrap();
    assert!(dedup2);
    let s2 = b.stats();
    assert_eq!(s2.selective_tail_wakes - s1.selective_tail_wakes, 1);
    assert_eq!(s2.tail_broadcasts - s1.tail_broadcasts, 0);
}

/// Selective tail wakeups match wildcards (`*`, `>`) accurately and can be toggled live
/// (`false -> true -> false`) while tails are parked with zero lost wakeups.
#[test]
fn selective_tail_wake_honors_wildcards_and_live_runtime_toggle() {
    let s = Scratch::new("seltog");
    let (b, _h, sock) = serve(&s, NO_POLL);
    assert!(!b.selective_tail_wake());

    let mut exact = subscribe(&sock, "/m/a");
    let mut star = subscribe(&sock, "/m/*");
    let mut root_wild = subscribe(&sock, "/*/>");
    let mut other = subscribe(&sock, "/z/>");
    until("4 tails parked", || b.stats().parked_tails == 4);

    let mut c = Client::connect(&sock).unwrap();
    let s0 = b.stats();
    assert_eq!(c.publish(1, 1, "/m/a", b"1").unwrap(), (0, false));
    assert_eq!(next(&mut exact), (0, "/m/a".to_string()));
    assert_eq!(next(&mut star), (0, "/m/a".to_string()));
    assert_eq!(next(&mut root_wild), (0, "/m/a".to_string()));
    assert_eq!(settled_wakeups(&b, &s0, 4, 4), 4);
    fence(&mut c);
    assert_eq!(b.stats().tail_broadcasts - s0.tail_broadcasts, 1);

    // Toggle selective mode ON while all 4 tails are parked: all 4 wake once to re-park
    // on their per-subscriber Condvars.
    let s_pre_on = b.stats();
    b.set_selective_tail_wake(true);
    assert!(b.selective_tail_wake());
    assert_eq!(settled_wakeups(&b, &s_pre_on, 4, 4), 4);

    // `/m/b` matches `/m/*` and `/*/>` (2 subscribers), not `/m/a` or `/z/>`.
    let s1 = b.stats();
    assert_eq!(c.publish(1, 2, "/m/b", b"2").unwrap(), (1, false));
    assert_eq!(next(&mut star), (1, "/m/b".to_string()));
    assert_eq!(next(&mut root_wild), (1, "/m/b".to_string()));
    assert_eq!(settled_wakeups(&b, &s1, 4, 2), 2);
    let (_, d) = c.publish(1, 2, "/m/b", b"2").unwrap();
    assert!(d);
    assert_eq!(b.stats().selective_tail_wakes - s1.selective_tail_wakes, 2);
    assert_eq!(b.stats().tail_broadcasts - s1.tail_broadcasts, 0);

    // `/z/only` matches `/*/>` and `/z/>` (2 subscribers), not `/m/a` or `/m/*`.
    let s2 = b.stats();
    assert_eq!(c.publish(1, 3, "/z/only", b"3").unwrap(), (2, false));
    assert_eq!(next(&mut root_wild), (2, "/z/only".to_string()));
    assert_eq!(next(&mut other), (2, "/z/only".to_string()));
    assert_eq!(settled_wakeups(&b, &s2, 4, 2), 2);
    let (_, d) = c.publish(1, 3, "/z/only", b"3").unwrap();
    assert!(d);
    assert_eq!(b.stats().selective_tail_wakes - s2.selective_tail_wakes, 2);

    // Toggle selective mode OFF live: all 4 re-park on `shared.tail`, and subsequent
    // publishes resume broadcasting to all 4.
    let s_pre_off = b.stats();
    b.set_selective_tail_wake(false);
    assert!(!b.selective_tail_wake());
    assert_eq!(settled_wakeups(&b, &s_pre_off, 4, 4), 4);

    let s3 = b.stats();
    assert_eq!(c.publish(1, 4, "/z/two", b"4").unwrap(), (3, false));
    assert_eq!(next(&mut root_wild), (3, "/z/two".to_string()));
    assert_eq!(next(&mut other), (3, "/z/two".to_string()));
    assert_eq!(settled_wakeups(&b, &s3, 4, 4), 4);
    let (_, d) = c.publish(1, 4, "/z/two", b"4").unwrap();
    assert!(d);
    assert_eq!(b.stats().tail_broadcasts - s3.tail_broadcasts, 1);
}

/// Under selective tail wakeups, an idle subscriber skips past both hidden records and
/// non-matching deliverable records at its liveness poll and reports an up-to-date
/// `Event::Mark` cursor, and still exits promptly on shutdown or principal revocation.
#[test]
fn selective_tail_wake_advances_idle_marks_and_honors_shutdown() {
    use astream_broker::{OpenOptions, Prepared};
    let s = Scratch::new("selmark");
    let mut opts = OpenOptions::new(Durability::Relaxed);
    opts.selective_tail_wake = true;
    let b = Broker::open_opts(s.path("b.log"), opts, || Ok(Prepared::Nothing)).unwrap();
    b.set_liveness_poll(Duration::from_millis(20));
    b.set_idle_mark(Duration::from_millis(40));
    let sock = s.path("b.sock");
    let mut h = b.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/m/>")
        .unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    assert_eq!(
        sub.recv_event().unwrap(),
        Some(Event::Mark {
            next: 0,
            head: 0,
            durable: Some(0)
        })
    );
    let mut c = Client::connect(&sock).unwrap();
    for i in 1..=5 {
        c.publish(1, i, "/other/noise", b"n").unwrap();
    }
    c.commit("g", 4).unwrap();
    let deadline = Instant::now() + HANG;
    loop {
        match sub.recv_event().unwrap() {
            Some(Event::Mark {
                next: 6, head: 6, ..
            }) => break,
            Some(Event::Mark { next, head, .. }) => assert!(next <= head && head <= 6),
            other => panic!("expected only marks, got {other:?}"),
        }
        assert!(Instant::now() < deadline, "mark never advanced to 6");
    }
    assert_eq!(b.stats().selective_tail_wakes, 0);
    assert_eq!(b.stats().tail_broadcasts, 0);
    h.shutdown();
    until("tail left wait on shutdown", || b.stats().parked_tails == 0);
}

/// When retention compacts across `[0 .. 15)` while a selective subscriber on `/n/>` is
/// parked through 20 non-matching `/m/x` publishes, `/n/>`'s `safe_skip_to` (`20`)
/// advances both its cursor and its `Told` ledger past `[0 .. 20)` without emitting a
/// false `Event::Gap` when `/n/hi` arrives at offset `20`.
#[cfg(feature = "retention")]
#[test]
fn selective_tail_wake_skips_compacted_nonmatching_prefix_without_false_gap() {
    use astream_broker::{OpenOptions, Prepared};
    let s = Scratch::new("selret");
    let mut opts = OpenOptions::new(Durability::Relaxed);
    opts.selective_tail_wake = true;
    let b = Broker::open_opts(s.path("b.log"), opts, || Ok(Prepared::Nothing)).unwrap();
    b.set_liveness_poll(NO_POLL);
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();

    let mut m = subscribe(&sock, "/m/>");
    let mut n_client = Client::connect(&sock).unwrap();
    assert!(n_client.gap_notices().unwrap());
    let mut n_sub = n_client.subscribe(0, "/n/>").unwrap();
    n_sub.set_read_timeout(Some(HANG)).unwrap();
    assert_eq!(
        n_sub.recv_event().unwrap(),
        Some(Event::Mark {
            next: 0,
            head: 0,
            durable: Some(0)
        })
    );
    until("both tails parked", || b.stats().parked_tails == 2);

    let mut p = Client::connect(&sock).unwrap();
    let s0 = b.stats();
    // Each message is counted once `/m/>` has parked again, as in the tests above: a
    // tail that finds the next record already visible when it comes back from a
    // delivery reads it without parking, so a count taken only after all 20 is short
    // of 20 whenever the tail fell behind the publisher (a descheduled thread on a
    // loaded host) and its wait for 20 never ends. Counted this way each message is
    // one wakeup of the one matching tail, and `/n/>` is still parked at its cursor.
    for i in 0..20u64 {
        let (off, _) = p.publish(1, i + 1, "/m/x", b"m").unwrap();
        assert_eq!(next(&mut m), (off, "/m/x".to_string()));
        assert_eq!(
            settled_wakeups(&b, &s0, 2, i + 1),
            i + 1,
            "message {i}: only the 1 matching subscriber woke"
        );
    }

    // Compact `[0 .. 15)` while `n_sub` is still parked at cursor 0.
    assert_eq!(b.retain_before(15).unwrap(), 15);
    assert_eq!(b.stats().parked_tails, 2);

    // Publish `/n/hi` at offset 20: `n_sub` wakes, skips `0..20`, and receives
    // `(20, "/n/hi")` directly with NO false `Event::Gap`!
    let (off, _) = p.publish(2, 1, "/n/hi", b"ok").unwrap();
    assert_eq!(off, 20);
    match n_sub.recv_event().unwrap() {
        Some(Event::Delivery {
            offset: 20,
            subject,
            body,
        }) => {
            assert_eq!(subject, "/n/hi");
            assert_eq!(body, b"ok");
        }
        other => panic!("expected Delivery(20, /n/hi) without Gap, got {other:?}"),
    }
    assert_eq!(n_sub.take_gap(), None);
}
