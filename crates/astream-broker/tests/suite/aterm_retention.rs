// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Claim `broker.retention-rules`, END TO END ON THE BROKER aterm RUNS: guarded, Ordered at
//! aterm's 100 ms horizon with aterm's escalation table (`guarded_durability::aterm_table`
//! and `aterm_horizon`, aterm-link `durability::escalation` and `ORDERED_HORIZON`), and
//! Relaxed with the same table, where the table holds the head on every platform —
//! retaining its log by aterm's four rules (aterm-link `broker_rules::default_rules`)
//! verbatim but for their byte bounds, which are scaled down so a test's records reach them
//! (`aterm_fixture::scaled`). The table, the horizon and the rules are read from
//! `tests/fixtures/aterm-broker.escalate` and `aterm-broker.retain`, which aterm-link's
//! `astream_fixture_tests` holds equal to aterm's own, so they are what aterm runs. Each
//! cut is the RETENTION TICK's, the state-carrying compaction the broker runs by itself,
//! driven here on a hand clock (`Broker::retention_tick_at`). An uncarried cut, which
//! taints the log so every `Retire`
//! is refused, is made only by a plain `retain_before` on a log no rules retain (on a
//! retained log astream carries the state of every cut, `BrokerLog::compact_begin`): aterm's
//! broker reaches it only when its rules could not be set at the open.
//!
//! What the rules must keep for aterm, each with its own negative control:
//!
//! - (i) a person's mail is held for its seven days whoever reads: unread person-lane mail
//!   is readable at day 6 and gone after day 7, while a node's mail goes with the cut once
//!   its inbox group commits past it. LIVE CONTROL: a reader template that names the
//!   person lane's node releases the person's mail at the node's read, before day 6.
//! - (ii) a halt and a presence row outlive day 7 and a restart in `Last`. PLANTED CONTROL:
//!   a compaction that carries no quiet subject's `Last` row loses them.
//! - (iii) a binding, a will and a person's inbox commit cut out of the file are restored
//!   by the reopen: the principal attaches settled, the open fires the will, and the
//!   person's inbox resumes past the mail they read. The rules are set at once after that
//!   reopen, while the writer commits the will it fired, with no flush first, as aterm sets
//!   them. PLANTED CONTROL: a reopen that restores no carried group commit re-delivers the
//!   read mail.
//! - (iv) after the tick's cut, `Retire` of a closed session's `ev` face succeeds and gives
//!   the producer's subject budget back, by `retire_subject` (aterm's mirror) and by the
//!   conditional `retire` (aterm's bridge), and after a plain `retain_before` on the same
//!   retaining broker too. LIVE CONTROL: a plain `retain_before` on an unretained broker,
//!   the uncarried cut, gives `is_retire_cut`.
//! - (v) while an escalated batch is held for its full flush, the tick never cuts above the
//!   subscriber-visible head. PLANTED CONTROL: the tick's ceiling taken from the log's
//!   head cuts above it.
//! - (vi) a fetch of the read mail below the cut answers `retained-from=`, never a clamp
//!   (the control, a Fetch that clamps, is `broker.retention-rules`' own wire test's).
//!
//! And what the MESH's bus log must keep, under its rules (aterm-link
//! `broker_rules::mesh_rules`, read from `tests/fixtures/aterm-mesh-bus.retain`): aterm's
//! broker rules with one more before their mail rule, the alab fleet's mail, which a second
//! reader, the person carry's group, holds, and which forgets (`Rule::forgetting`):
//!
//! - (vii) a person's post to an alab node that its inbox has read is held until the carry
//!   has read it too, and goes at the next tick once it has. LIVE CONTROLS: under aterm's
//!   broker rules, and under the mesh's for another fleet's post, the inbox's read lets it
//!   go at the first tick.
//! - (viii) an alab mail lane retention has given up whole leaves `Last` and gives its
//!   producer's subject budget one back, live and after a restart, and the tick says so; a
//!   lane with a record still held stays, charged, until that record goes. LIVE CONTROLS:
//!   the same lane under aterm's broker rules stays in `Last`, charged; and under the mesh's
//!   rules another fleet's lane given up whole, a presence row, a halt (the default rule's),
//!   and a lane a pending will targets stay.
//!
//! Every wait for something that must happen is a one-minute hang detector, never a
//! budget; nothing sleeps. The tick's thread runs too (every broker given rules has one):
//! its interval is an hour, and the ticks a batch past a class's bytes asks for run by the
//! wall clock, which stays within the test's seconds of the hand clock's day 0 and behind
//! every later hand tick, so they age nothing a hand tick's assertion reads.

#![cfg(all(unix, feature = "cap", feature = "retention"))]

use super::aterm_fixture::{scaled, ATERM_RETAIN, MESH_RETAIN};
use super::guarded_durability::{aterm_horizon, aterm_table, serve_like_aterm, SECRET};
use astream_broker::{
    broker_refusal, incarnation_base, mint, producer_id_of, will_seq, Broker, BrokerHandle, Client,
    Durability, Event, Retention, RetentionTick, Tier,
};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const MINUTE: Duration = Duration::from_secs(60); // a hang detector, never a budget
const HOUR_MS: u64 = 3_600_000;
const DAY_MS: u64 = 24 * HOUR_MS;

/// aterm's rules' bounds, scaled: the bulk stream keeps a few dozen test records, and
/// mail and the rest far more than any test writes, so only ages and reads give them up.
const EV_BYTES: u64 = 4 * 1024;
const MAIL_BYTES: u64 = 256 * 1024;
const DEFAULT_BYTES: u64 = 256 * 1024;

const FLEET: &str = "F";
const NODE: &str = "n-a1b2c3d4e5f60718";
const OTHER: &str = "n-8f7e6d5c4b3a2910";
const PERSON: &str = "h-x";
const EV_BODY: &[u8] = b"v=1 t=1 ev=0123456789abcdef0123456789abcdef0123456789abcdef";

/// aterm's four rules (aterm-link `broker_rules::default_rules`, read from
/// `tests/fixtures/aterm-broker.retain`), filter for filter, class for class, reader for
/// reader and age for age; only the bytes are the arguments.
fn aterm_rules(ev: u64, mail: u64, default: u64) -> Retention {
    scaled(ATERM_RETAIN, ev, mail, default)
}

/// [`aterm_rules`] with the mail rule's reader template rewritten to `reader`: the
/// fixture's one `read=` replaced, everything else the fixture's.
fn rules_with_reader(reader: &str, ev: u64, mail: u64, default: u64) -> Retention {
    let mut rewritten = 0usize;
    let text: Vec<String> = ATERM_RETAIN
        .lines()
        .map(|line| {
            if line.trim_start().starts_with('#') {
                return line.to_string();
            }
            let words: Vec<String> = line
                .split_ascii_whitespace()
                .map(|w| {
                    if w.starts_with("read=") {
                        rewritten += 1;
                        format!("read={reader}")
                    } else {
                        w.to_string()
                    }
                })
                .collect();
            words.join(" ")
        })
        .collect();
    assert_eq!(rewritten, 1, "aterm's rules name one reader template");
    scaled(&text.join("\n"), ev, mail, default)
}

fn rules() -> Retention {
    aterm_rules(EV_BYTES, MAIL_BYTES, DEFAULT_BYTES)
}

/// The two tiers aterm serves its guarded broker at, with its table: its default, Ordered
/// at its horizon (aterm-link `durability::ORDERED_HORIZON`, read from
/// `tests/fixtures/aterm-broker.escalate`), and a named `relaxed`.
fn arms() -> [Durability; 2] {
    [
        Durability::Ordered {
            horizon: Some(aterm_horizon()),
        },
        Durability::Relaxed,
    ]
}

// aterm's subjects (aterm-link `subject`).
fn session_ev(node: &str, sid: &str) -> String {
    format!("/f/{FLEET}/pub/{node}/{sid}/ev")
}
fn session_presence(node: &str, sid: &str) -> String {
    format!("/f/{FLEET}/pub/{node}/{sid}/presence")
}
fn node_presence(node: &str) -> String {
    format!("/f/{FLEET}/pub/{node}/node/presence")
}
fn post_lane(node: &str) -> String {
    format!("/f/{FLEET}/in/{node}/s-a/{OTHER}/task")
}
fn person_lane(node: &str) -> String {
    format!("/f/{FLEET}/in/p/{PERSON}/{node}")
}
fn person_mail() -> String {
    format!("/f/{FLEET}/in/p/{PERSON}/>")
}
fn node_mail(node: &str) -> String {
    format!("/f/{FLEET}/in/{node}/>")
}
fn person_halt() -> String {
    format!("/f/{FLEET}/fleet/{PERSON}/halt")
}
fn inbox_group(node: &str) -> String {
    format!("/f/{FLEET}/cur/{node}/node/inbox")
}
fn person_inbox_group() -> String {
    format!("/f/{FLEET}/cur/p/{PERSON}/inbox")
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(f());
    });
    rx.recv_timeout(MINUTE)
        .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
}

static NEXT: AtomicU64 = AtomicU64::new(0);

/// An exclusive scratch directory under `/tmp` (a Darwin `TMPDIR` pushes a socket path
/// past `SUN_LEN`), removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asar-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A broker opened as aterm opens its fabric broker, its rules set as aterm sets them (at
/// once after the open, no flush first), served on a socket of its own each open.
/// Fields drop in order: the handle, the broker, then the scratch directory.
struct World {
    handle: Option<BrokerHandle>,
    broker: Arc<Broker>,
    durability: Durability,
    opens: u32,
    rules: Option<Retention>,
    scratch: Scratch,
}

impl World {
    fn open(tag: &str, durability: Durability, rules: Retention) -> World {
        let scratch = Scratch::new(tag);
        let rules = Some(rules);
        let (broker, handle) = Self::serve(&scratch, 0, durability, rules.as_ref());
        World {
            handle: Some(handle),
            broker,
            durability,
            opens: 1,
            rules,
            scratch,
        }
    }

    fn log(scratch: &Scratch) -> String {
        scratch.0.join("b.log").to_string_lossy().into_owned()
    }

    fn sock_of(scratch: &Scratch, n: u32) -> String {
        scratch
            .0
            .join(format!("{n}.sock"))
            .to_string_lossy()
            .into_owned()
    }

    fn sock(&self) -> String {
        Self::sock_of(&self.scratch, self.opens - 1)
    }

    fn serve(
        scratch: &Scratch,
        n: u32,
        durability: Durability,
        rules: Option<&Retention>,
    ) -> (Arc<Broker>, BrokerHandle) {
        let (broker, handle) = serve_like_aterm(
            &Self::log(scratch),
            &Self::sock_of(scratch, n),
            durability,
            aterm_table(),
        );
        broker.set_retention_interval(Duration::from_secs(3600));
        if let Some(rules) = rules {
            broker
                .set_retention(rules.clone())
                .expect("aterm's rules are set at once after the open, with no flush first");
        }
        (Arc::new(broker), handle)
    }

    /// The broker aterm serves when its rules could not be set at the open: unretained.
    fn unretained(tag: &str, durability: Durability) -> World {
        let scratch = Scratch::new(tag);
        let (broker, handle) = Self::serve(&scratch, 0, durability, None);
        World {
            handle: Some(handle),
            broker,
            durability,
            opens: 1,
            rules: None,
            scratch,
        }
    }

    /// Stop the broker cleanly and open its log again, the rules set again at once. The
    /// old broker is dropped (its tick and writer joined, its log closed cleanly) before
    /// the new one opens the log, whose lock it holds until then.
    fn restart(self) -> World {
        let World {
            handle,
            broker,
            durability,
            opens,
            rules,
            scratch,
        } = self;
        if let Some(mut handle) = handle {
            handle.shutdown();
        }
        let old = Arc::try_unwrap(broker)
            .unwrap_or_else(|_| panic!("the broker is still shared at its restart"));
        drop(old);
        let (broker, handle) = Self::serve(&scratch, opens, durability, rules.as_ref());
        World {
            handle: Some(handle),
            broker,
            durability,
            opens: opens + 1,
            rules,
            scratch,
        }
    }

    /// A connection holding the god capability: unbound, the whole tree.
    fn god(&self) -> Client {
        let cap = mint(SECRET, "rw:/>").unwrap();
        let mut c = Client::connect(self.sock()).unwrap();
        c.attach(&cap.filter, &cap.tag).unwrap();
        c
    }

    /// A connection bound to `principal` (aterm's node grant): its first attach binds it.
    fn bound(&self, principal: &str) -> Client {
        self.bound_in(FLEET, principal)
    }

    /// [`bound`](Self::bound) to `principal` in `fleet`.
    fn bound_in(&self, fleet: &str, principal: &str) -> Client {
        let cap = mint(SECRET, &format!("rw,p={principal}:/f/{fleet}/>")).unwrap();
        let mut c = Client::connect(self.sock()).unwrap();
        c.attach(&cap.filter, &cap.tag).unwrap();
        c
    }

    /// One retention tick at `now` on the hand clock, under the hang detector.
    fn tick(&self, now: u64) -> RetentionTick {
        let b = Arc::clone(&self.broker);
        within_a_minute("a retention tick", move || b.retention_tick_at(now))
            .unwrap_or_else(|e| panic!("the tick at {now}: {e}"))
    }

    fn base(&self) -> u64 {
        self.broker.stats().log.base.0
    }
}

/// `n` records on `subject` from `c` as producer `pid`, sequences from `seq`; their offsets.
fn flood(c: &mut Client, pid: u64, seq: &mut u64, subject: &str, n: usize) -> Vec<u64> {
    (0..n)
        .map(|_| {
            *seq += 1;
            c.publish(pid, *seq, subject, EV_BODY).unwrap().0
        })
        .collect()
}

/// The offsets a fetch of `filter` from offset 0 returns, or the `retained-from=` it is
/// refused with. Any other answer fails.
fn read_from_zero(c: &mut Client, filter: &str) -> Result<Vec<u64>, u64> {
    match c.fetch(0, filter, 64) {
        Ok((page, _)) => Ok(page.iter().map(|r| r.0).collect()),
        Err(e) => match broker_refusal(&e).and_then(|r| r.retained_from()) {
            Some(from) => Err(from),
            None => panic!("a fetch of {filter} from 0: {e}"),
        },
    }
}

/// (i) and (vi): mail is held by aterm's rules — a person's for seven days whoever reads,
/// a node's until its inbox reads it — and the read mail answers `retained-from=`.
///
/// A node's mail and a person's are published, then enough of the bulk stream that the
/// prefix rule's cut passes both. At the first tick (day 0) both are held below the cut,
/// unread. The node's inbox group then commits past both, which is what its drain does.
/// At day 6 the node's mail is gone with the cut (a fetch of it from 0 answers
/// `retained-from=` above it: never a clamp), and the person's is still read from 0: the
/// node's read is not the person's, and the person's own inbox group is not the rule's
/// reader. After day 7 the person's mail is gone too.
///
/// LIVE CONTROL: the same run under a reader template that names the person lane's node
/// (`/f/{2}/cur/{6}/node/inbox`) gives the person's mail up at the node's read, so day
/// 6's read of it answers `retained-from=`: the day-6 assertion is what catches a reader
/// that releases a person's mail early.
#[test]
fn a_persons_mail_is_held_seven_days_and_a_nodes_goes_once_its_inbox_reads_it() {
    for durability in arms() {
        for (early, rules) in [
            (false, rules()),
            (
                true,
                rules_with_reader(
                    "/f/{2}/cur/{6}/node/inbox",
                    EV_BYTES,
                    MAIL_BYTES,
                    DEFAULT_BYTES,
                ),
            ),
        ] {
            let what = format!("{durability:?}, early reader {early}");
            let w = World::open("mail", durability, rules);
            let t0 = now_ms();
            let mut god = w.god();
            let mut seq = 0;
            let (nm, _) = god
                .publish(1, 1, &post_lane(NODE), b"v=1 kind=task")
                .unwrap();
            let (pm, _) = god
                .publish(2, 1, &person_lane(NODE), b"v=1 kind=ask")
                .unwrap();
            let ev = session_ev(NODE, "s-a");
            flood(&mut god, 3, &mut seq, &ev, 64);
            let day0 = w.tick(t0);
            assert!(
                day0.base > pm,
                "{what}: the cut passes both mails: {day0:?}"
            );
            assert_eq!(
                read_from_zero(&mut god, &node_mail(NODE)),
                Ok(vec![nm]),
                "{what}: the node's unread mail is held below the cut"
            );
            assert_eq!(
                read_from_zero(&mut god, &person_mail()),
                Ok(vec![pm]),
                "{what}: so is the person's"
            );

            god.commit(&inbox_group(NODE), pm).unwrap();
            flood(&mut god, 3, &mut seq, &ev, 64);
            let day6 = w.tick(t0 + 6 * DAY_MS);
            assert!(day6.base > day0.base, "{what}: {day6:?}");
            let person = read_from_zero(&mut god, &person_mail());
            if early {
                assert!(
                    matches!(person, Err(from) if from > pm),
                    "{what}: the control releases the person's mail at the node's read: \
                     {person:?}"
                );
                continue;
            }
            match read_from_zero(&mut god, &node_mail(NODE)) {
                Err(from) => assert!(from > nm, "{what}: retained-from={from}"),
                Ok(page) => panic!("{what}: the node's read mail is still read: {page:?}"),
            }
            assert_eq!(
                person,
                Ok(vec![pm]),
                "{what}: the person's unread mail is read at day 6"
            );

            let day7 = w.tick(t0 + 7 * DAY_MS + HOUR_MS);
            match read_from_zero(&mut god, &person_mail()) {
                Err(from) => assert!(from > pm, "{what}: retained-from={from}"),
                Ok(page) => panic!("{what}: the person's mail outlived its week: {page:?}"),
            }
            assert!(day7.base >= day6.base, "{what}: {day7:?}");
        }
    }
}

/// The rows a `Last` of `filter` answers: `(subject, body)`, in the broker's order.
fn last_rows(c: &mut Client, filter: &str) -> Vec<(String, Vec<u8>)> {
    let (page, _) = c.last(filter, "", 64).unwrap();
    page.into_iter().map(|r| (r.1, r.2)).collect()
}

/// (ii): a person's halt and a node's and a session's presence rows outlive day 7, the
/// cut that takes every record below the visible head with it, and a restart: `Last`
/// still answers each, which is how aterm reads a halt and a presence row.
///
/// The halt is the default rule's, which holds it for its week only; the presence rows
/// are the last-value rule's. Past day 7 neither the file nor the held store keeps the
/// halt's record: the state the cut carries (`<log>.state`, every quiet subject's latest
/// row) is what answers it. PLANTED CONTROL (scratch-reverted): a compaction that carries
/// no `Last` row loses the halt here.
#[test]
fn a_halt_and_presence_rows_outlive_day_seven_and_a_restart() {
    for durability in arms() {
        let what = format!("{durability:?}");
        let w = World::open("rows", durability, rules());
        let t0 = now_ms();
        let mut god = w.god();
        let mut seq = 0;
        god.publish(4, 1, &person_halt(), b"v=1 halt=on by=h-x")
            .unwrap();
        god.publish(5, 1, &node_presence(NODE), b"v=1 state=live")
            .unwrap();
        god.publish(5, 2, &session_presence(NODE, "s-a"), b"v=1 state=idle")
            .unwrap();
        flood(&mut god, 3, &mut seq, &session_ev(NODE, "s-a"), 8);
        // Every record is first seen by this tick, so each is a week old at day 8 (a record
        // first seen by the day-8 tick itself would be new there).
        let head = w.broker.visible_head();
        w.tick(t0);
        let tick = w.tick(t0 + 8 * DAY_MS);
        assert_eq!(
            tick.base, head,
            "{what}: the week cut takes it all: {tick:?}"
        );
        let want_halt = vec![(person_halt(), b"v=1 halt=on by=h-x".to_vec())];
        let want_presence = vec![
            (node_presence(NODE), b"v=1 state=live".to_vec()),
            (session_presence(NODE, "s-a"), b"v=1 state=idle".to_vec()),
        ];
        let presence = format!("/f/{FLEET}/pub/{NODE}/*/presence");
        let sorted = |c: &mut Client, f: &str| {
            let mut rows = last_rows(c, f);
            rows.sort();
            rows
        };
        assert_eq!(sorted(&mut god, &person_halt()), want_halt, "{what}");
        assert_eq!(sorted(&mut god, &presence), want_presence, "{what}");
        drop(god);
        let w = w.restart();
        let mut god = w.god();
        assert_eq!(w.base(), head, "{what}: the base read back");
        assert_eq!(
            sorted(&mut god, &person_halt()),
            want_halt,
            "{what}: the halt after a restart"
        );
        assert_eq!(
            sorted(&mut god, &presence),
            want_presence,
            "{what}: presence after a restart"
        );
    }
}

/// The next delivery on `sub`: marks and gap notices are skipped, each under the hang
/// detector (a stream kept alive by marks would never time out by its read timeout).
fn next_delivery(sub: &mut astream_broker::Subscription, deadline: Instant) -> (u64, String) {
    loop {
        assert!(Instant::now() < deadline, "no delivery within a minute");
        match sub.recv_event().unwrap() {
            Some(Event::Delivery {
                offset, subject, ..
            }) => return (offset, subject),
            Some(Event::Mark { .. } | Event::Gap(_)) => {}
            None => panic!("the broker closed the subscription"),
        }
    }
}

/// (iii): what the tick's cut takes out of the file and carries is restored by the reopen —
/// a node's binding, its pending will, and a person's inbox commit.
///
/// The node attaches with aterm's bound grant (a hidden `/a/bind`), registers its presence
/// will (a hidden `/a/will`) and says it is live; the person's inbox commits past the one
/// mail they read (a hidden `/a/commit`, escalated by the table's group rule). The tick at
/// day 2 cuts past all three; the person's mail, unread by the rule's reader and inside its
/// week, stays held. The node's principal is then revoked, so its connection's close drops
/// its live will instead of firing it (`WillDrop`): only the reopen can fire it, and only
/// from what the cut carried. Reopened, with the rules set at once (no flush first) while
/// the writer commits the will the open fired:
/// - the principal attaches settled, with no writer round trip (the binding was carried);
/// - the open fired the will: the node's presence row reads gone;
/// - the person's inbox resumes past the mail they read: its first delivery is a mail
///   published after the reopen, not the read one.
///
/// PLANTED CONTROL (scratch-reverted): an open that restores no carried group commit makes
/// the person's inbox start from 0, and the held, read mail is delivered first.
#[test]
fn bindings_wills_and_an_inbox_commit_outlive_the_ticks_cut_and_a_reopen() {
    for durability in arms() {
        let what = format!("{durability:?}");
        let w = World::open("state", durability, rules());
        let t0 = now_ms();
        let mut god = w.god();
        let mut seq = 0;
        let pid = producer_id_of(NODE);
        let inc = incarnation_base(1).unwrap();
        let mut node = w.bound(NODE);
        node.will(
            pid,
            will_seq(1).unwrap(),
            &node_presence(NODE),
            b"v=1 state=gone",
        )
        .unwrap();
        node.publish(pid, inc + 1, &node_presence(NODE), b"v=1 state=live")
            .unwrap();
        let (pm, _) = god
            .publish(2, 1, &person_lane(NODE), b"v=1 kind=ask")
            .unwrap();
        let commit = god.commit(&person_inbox_group(), pm).unwrap();
        flood(&mut god, 3, &mut seq, &session_ev(OTHER, "s-a"), 64);
        let tick = w.tick(t0 + 2 * DAY_MS);
        assert!(
            tick.base > commit,
            "{what}: the cut passes the commit: {tick:?}"
        );
        assert_eq!(
            read_from_zero(&mut god, &person_mail()),
            Ok(vec![pm]),
            "{what}: the person's mail is held"
        );

        let settled = w.broker.stats().wills_settled;
        assert!(w.broker.revoke_principal(NODE), "{what}");
        drop(node);
        let b = Arc::clone(&w.broker);
        within_a_minute("the closed connection's will to be dropped", move || {
            while b.stats().wills_settled <= settled {
                thread::yield_now();
            }
        });
        drop(god);
        let w = w.restart();

        let before = w.broker.stats();
        let node = w.bound(NODE);
        let after = w.broker.stats();
        assert_eq!(
            (
                after.writer_round_trips - before.writer_round_trips,
                after.binds_settled - before.binds_settled
            ),
            (0, 1),
            "{what}: the principal attaches settled from the carried binding"
        );
        drop(node);
        let mut god = w.god();
        // A barrier behind the will the open queued: its ack means the writer has run it.
        god.publish(9, 1, &format!("/f/{FLEET}/sentinel"), b"s")
            .unwrap();
        assert_eq!(
            last_rows(&mut god, &node_presence(NODE)),
            vec![(node_presence(NODE), b"v=1 state=gone".to_vec())],
            "{what}: the open fired the carried will"
        );

        let (pm2, _) = god
            .publish(2, 2, &person_lane(NODE), b"v=1 kind=ask again")
            .unwrap();
        let reader = w.god();
        let mut sub = reader
            .subscribe_group(&person_inbox_group(), &person_mail())
            .unwrap();
        sub.set_read_timeout(Some(MINUTE)).unwrap();
        let first = next_delivery(&mut sub, Instant::now() + MINUTE);
        assert_eq!(
            first,
            (pm2, person_lane(NODE)),
            "{what}: the person's inbox resumes past the mail they read (at {pm})"
        );
    }
}

/// How a test cuts the log in (iv).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cut {
    /// The retention tick's, on the broker aterm runs.
    Tick,
    /// A plain `retain_before`, on that same retaining broker: astream carries the state
    /// of every cut on a log its rules retain (`BrokerLog::compact_begin`).
    PlainOnRetained,
    /// A plain `retain_before` on an unretained broker (the one aterm serves when its
    /// rules could not be set): the uncarried cut, which taints the log.
    PlainOnUnretained,
}

/// (iv): after the tick's cut, aterm's `Retire` of a closed session's `ev` face succeeds and
/// gives the subject budget back.
///
/// God's record at offset 0 first, then the node attaches (its bind at 1) and publishes
/// two sessions' `ev` faces. The tick at day 8 cuts past every one of them; `Last` keeps
/// each face's row, charged to the node, in the carried state. `retire_subject` (the
/// mirror's, on a closed session's face) and the conditional `retire` (the bridge's, at
/// the row's offset on the log's identity) each succeed, appending a marked retire, and the
/// node's budget falls by one each. A plain `retain_before(1)` on the same retaining broker
/// is carried too, and the retire succeeds after it as well.
///
/// LIVE CONTROL: on an unretained broker, the same records and one `retain_before(1)` (it
/// drops only god's record, below every binding, as an aterm test's cut on an unretained
/// broker did): the mirror's retire is refused `is_retire_cut`, the budget unchanged.
#[test]
fn a_closed_faces_retire_succeeds_after_the_ticks_cut_and_gives_the_budget_back() {
    for durability in arms() {
        for cut in [Cut::Tick, Cut::PlainOnRetained, Cut::PlainOnUnretained] {
            let what = format!("{durability:?}, {cut:?}");
            let w = if cut == Cut::PlainOnUnretained {
                World::unretained("retire", durability)
            } else {
                World::open("retire", durability, rules())
            };
            let t0 = now_ms();
            let mut god = w.god();
            let mut seq = 0;
            flood(&mut god, 3, &mut seq, &session_ev(OTHER, "s-z"), 1);
            let pid = producer_id_of(NODE);
            let mut node = w.bound(NODE);
            let (closed, kept) = (session_ev(NODE, "s-a"), session_ev(NODE, "s-b"));
            let mut nseq = 0;
            flood(&mut node, pid, &mut nseq, &closed, 2);
            let kept_off = *flood(&mut node, pid, &mut nseq, &kept, 2).last().unwrap();
            let budget = |c: &mut Client| c.subject_budget(pid).unwrap().unwrap().subjects;
            assert_eq!(budget(&mut node), 2, "{what}: two faces charged");
            match cut {
                Cut::Tick => {
                    w.tick(t0);
                    let tick = w.tick(t0 + 8 * DAY_MS);
                    assert!(
                        tick.base > kept_off,
                        "{what}: the cut passes both faces: {tick:?}"
                    );
                }
                Cut::PlainOnRetained | Cut::PlainOnUnretained => {
                    assert_eq!(w.broker.retain_before(1).unwrap(), 1, "{what}");
                }
            }
            if cut == Cut::PlainOnUnretained {
                let e = node.retire_subject(pid, &closed).unwrap_err();
                assert!(
                    broker_refusal(&e).is_some_and(|r| r.is_retire_cut()),
                    "{what}: {e}"
                );
                assert_eq!(budget(&mut node), 2, "{what}: nothing given back");
                continue;
            }
            let (off, absent) = node.retire_subject(pid, &closed).unwrap();
            assert!(!absent, "{what}: the closed face was in Last (at {off})");
            assert_eq!(budget(&mut node), 1, "{what}: one subject given back");
            let log = w.broker.log_identity();
            let (off, moot) = node.retire(pid, &kept, kept_off, log).unwrap();
            assert!(
                !moot,
                "{what}: the conditional retire at the row's offset (at {off})"
            );
            assert_eq!(budget(&mut node), 0, "{what}: and the other");
        }
    }
}

/// Whether `b`, opened at `durability`, holds an escalated record's ack for a full flush
/// (`guarded_durability::holds`): Relaxed with aterm's table everywhere, Ordered where it is
/// served Ordered (Apple, the log on the boot volume).
fn holds_the_head(b: &Broker, durability: Durability) -> bool {
    let served = b.served_durability();
    durability == Durability::Relaxed || served.served == Tier::Ordered
}

/// (v): while an escalated batch is held for its full flush, the tick never cuts above the
/// subscriber-visible head.
///
/// The writer is parked between the batch's acks and its flush (`pause_next_flush`) with
/// one escalated record in it, a person's mail: committed, its ack withheld, the visible
/// head below it. The mail class's bytes are scaled below one mail here, so that mail
/// alone takes its class past them and the rules' cut wants it, as the bulk stream's week
/// wants every `ev` record below it: only the ceiling keeps the cut off it. A tick at day 8
/// runs in that window (the batch lock is free there) and cuts exactly to the visible
/// head, never to the log's head above it. Resumed, the mail is acked and read. On a tier
/// that holds no
/// head (Ordered served Strict, off Apple) there is no window to hold, and the arm is
/// skipped there by name.
///
/// PLANTED CONTROL (scratch-reverted): `retention_tick_run`'s ceiling taken from
/// `log.head()` alone cuts to the log's head, and `tick.base <= visible` fails.
#[test]
fn the_tick_never_cuts_above_the_visible_head_while_an_escalated_batch_is_held() {
    for durability in arms() {
        let what = format!("{durability:?}");
        let w = World::open("held", durability, aterm_rules(EV_BYTES, 64, DEFAULT_BYTES));
        if !holds_the_head(&w.broker, durability) {
            eprintln!(
                "{what}: served {:?}, which holds no head",
                w.broker.served_durability()
            );
            continue;
        }
        let t0 = now_ms();
        let mut god = w.god();
        let mut seq = 0;
        flood(&mut god, 3, &mut seq, &session_ev(NODE, "s-a"), 8);
        w.tick(t0);
        let pause = w.broker.pause_next_flush();
        let mut asker = w.god();
        let lane = person_lane(NODE);
        let asked = thread::spawn(move || asker.publish(2, 1, &lane, b"v=1 kind=ask"));
        let pause = within_a_minute("the escalated batch to reach its flush", move || {
            assert!(pause.wait(), "the writer stopped before the flush");
            pause
        });
        let visible = w.broker.visible_head();
        assert_eq!(
            w.broker.head(),
            visible + 1,
            "{what}: PRECONDITION the escalated record is committed and unseen"
        );
        let tick = w.tick(t0 + 8 * DAY_MS);
        assert!(
            tick.base <= visible,
            "{what}: the tick cut to {} above the visible head {visible}",
            tick.base
        );
        assert_eq!(tick.base, visible, "{what}: and to it");
        pause.resume();
        let (pm, _) =
            within_a_minute("the escalated record's ack", move || asked.join().unwrap()).unwrap();
        assert_eq!(pm, visible, "{what}");
        let (page, _) = god.fetch(pm, &person_mail(), 8).unwrap();
        assert_eq!(
            page.iter().map(|r| r.0).collect::<Vec<_>>(),
            vec![pm],
            "{what}: the mail is read at the base"
        );
    }
}

/// The mesh bus log's five rules (aterm-link `broker_rules::mesh_rules`, read from
/// `tests/fixtures/aterm-mesh-bus.retain`), at this file's scaled bytes.
fn mesh_rules() -> Retention {
    scaled(MESH_RETAIN, EV_BYTES, MAIL_BYTES, DEFAULT_BYTES)
}

/// The fleet whose mail the mesh's carry reads (`/f/alab/in/>`).
const MESH: &str = "alab";

/// The person carry's node (aterm-link's `n-carry`), and its group, the alab mail rule's
/// second reader: `/f/alab/cur/n-carry/node/carry`.
const CARRY: &str = "n-carry";
fn carry_group(fleet: &str) -> String {
    format!("/f/{fleet}/cur/{CARRY}/node/carry")
}

/// A lane to `node`'s session `sid` from `from`, of `kind`: `/f/<F>/in/<node>/<sid>/<from>/<kind>`.
fn lane(fleet: &str, node: &str, sid: &str, from: &str, kind: &str) -> String {
    format!("/f/{fleet}/in/{node}/{sid}/{from}/{kind}")
}

/// The subjects `Last` answers of `filter`, in the broker's order.
fn last_subjects(c: &mut Client, filter: &str) -> Vec<String> {
    last_rows(c, filter).into_iter().map(|(s, _)| s).collect()
}

/// (vii): under the mesh's rules a person's post to an alab node is held until BOTH of its
/// readers have read it: the addressed node's inbox group (the mail push, or the local
/// bridge) and the person carry's group, which carries the post to the person's other nodes.
///
/// Andrew's post to node `n-q`'s session `s-q`, `/f/alab/in/n-q/s-q/h-andrew/ask`, is read by
/// `n-q`'s inbox group, then the bulk stream floods past its bytes, so the tick's cut passes
/// the post. The carry has not read it: it is held below the cut and read from 0, and Hello
/// advertises the alab mail rule forgetting. The carry's group then commits past it, and
/// after the next tick the post is gone (`retained-from=` above it), and its lane with it
/// (`Last` answers nothing of it).
///
/// LIVE CONTROLS: the same run under aterm's broker rules (`aterm-broker.retain`, the inbox
/// group the one reader), and under the mesh's rules for the same post in another fleet
/// (`f1`, whose mail falls to the mail rule after alab's), give the post up at the first
/// tick, the inbox having read it.
#[test]
fn a_persons_post_is_held_until_the_carry_has_read_it_too() {
    for durability in arms() {
        for (mesh, fleet) in [(true, MESH), (true, "f1"), (false, MESH)] {
            let what = format!("{durability:?}, mesh rules {mesh}, fleet {fleet}");
            let held = mesh && fleet == MESH;
            let post = lane(fleet, "n-q", "s-q", "h-andrew", "ask");
            let lanes = format!("/f/{fleet}/in/n-q/>");
            let lanes = lanes.as_str();
            let w = World::open(
                "carry",
                durability,
                if mesh { mesh_rules() } else { rules() },
            );
            let t0 = now_ms();
            let mut god = w.god();
            let advertised = god.retention_rules().expect("Hello advertises the rules");
            assert_eq!(
                advertised.rules()[2].forgets(),
                mesh,
                "{what}: the third rule as Hello advertises it"
            );
            assert!(
                !advertised.rules()[3..].iter().any(|r| r.forgets()),
                "{what}: and no other"
            );
            let (pm, _) = god.publish(2, 1, &post, b"v=1 kind=ask").unwrap();
            god.commit(&format!("/f/{fleet}/cur/n-q/node/inbox"), pm)
                .unwrap();
            let mut seq = 0;
            flood(&mut god, 3, &mut seq, &session_ev(NODE, "s-a"), 64);
            let day0 = w.tick(t0);
            assert!(day0.base > pm, "{what}: the cut passes the post: {day0:?}");
            let read = read_from_zero(&mut god, lanes);
            if !held {
                assert!(
                    matches!(read, Err(from) if from > pm),
                    "{what}: the control gives the post up at the inbox's read: {read:?}"
                );
                continue;
            }
            assert_eq!(read, Ok(vec![pm]), "{what}: held for the carry");
            assert_eq!(last_subjects(&mut god, lanes), vec![post.clone()], "{what}");

            god.commit(&carry_group(MESH), pm).unwrap();
            w.tick(t0 + HOUR_MS);
            match read_from_zero(&mut god, lanes) {
                Err(from) => assert!(from > pm, "{what}: retained-from={from}"),
                Ok(page) => panic!("{what}: the post outlived both reads: {page:?}"),
            }
            assert_eq!(
                last_subjects(&mut god, lanes),
                Vec::<String>::new(),
                "{what}: and its lane is forgotten"
            );
        }
    }
}

/// (viii): under the mesh's rules an alab mail lane retention has given up whole leaves
/// `Last`, and its producer's subject budget gets the lane back, live and after a restart;
/// the tick says it forgot it.
///
/// The person carry, bound as aterm binds a node (`n-carry`, in alab), writes two lanes to an
/// alab node's sessions and registers a will on the second (its connection open, so the will
/// can still append), and both lanes are read by both their readers. A lane in another fleet
/// (`F`) read by its inbox, a presence row and a halt (the default rule's) are written beside
/// them, then the bulk stream. The week cut (the hand
/// clock's day 8, every record first seen at day 0) takes every record: the first lane is
/// forgotten, `RetentionTick::forgotten` is 1, `Last` of the lanes answers the second lane
/// alone and the carry's budget is one lower. After a restart (the carry's will firing on
/// its lane at the close or the open) `Last` and the budget read the same, and a tick
/// forgets nothing more.
///
/// Every cut is the hand tick's: the ticks a batch asks for run by the wall clock, where no
/// record is a week old, and the bytes stay within every class's, so no tick of the ticker's
/// thread cuts, or forgets, before the hand tick at day 8 (the count is that tick's alone).
///
/// LIVE CONTROLS: under aterm's broker rules, the same run forgets nothing, both lanes stay
/// in `Last` and the budget keeps both, across the restart; and under the mesh's rules the
/// other fleet's lane (given up whole, by a rule that does not forget), the presence row,
/// the halt and the lane the will targets stay.
#[test]
fn a_mail_lane_retention_gave_up_whole_leaves_last_and_its_producers_budget() {
    let (read, willed) = (
        lane(MESH, NODE, "s-a", PERSON, "ask"),
        lane(MESH, NODE, "s-b", PERSON, "ask"),
    );
    let other = lane(FLEET, NODE, "s-a", PERSON, "ask");
    let lanes = format!("/f/{MESH}/in/{NODE}/>");
    let pid = producer_id_of(CARRY);
    let inc = incarnation_base(1).unwrap();
    let want_rows = vec![
        (person_halt(), b"v=1 halt=on by=h-x".to_vec()),
        (node_presence(NODE), b"v=1 state=live".to_vec()),
    ];
    for durability in arms() {
        for mesh in [true, false] {
            let what = format!("{durability:?}, mesh rules {mesh}");
            let w = World::open(
                "forget",
                durability,
                if mesh { mesh_rules() } else { rules() },
            );
            let t0 = now_ms();
            let mut carry = w.bound_in(MESH, CARRY);
            let (r_off, _) = carry.publish(pid, inc + 1, &read, b"v=1 kind=ask").unwrap();
            let (w_off, _) = carry
                .publish(pid, inc + 2, &willed, b"v=1 kind=ask")
                .unwrap();
            carry
                .will(pid, will_seq(1).unwrap(), &willed, b"v=1 kind=gone")
                .unwrap();
            let mut god = w.god();
            god.publish(4, 1, &person_halt(), b"v=1 halt=on by=h-x")
                .unwrap();
            god.publish(5, 1, &node_presence(NODE), b"v=1 state=live")
                .unwrap();
            let (o_off, _) = god.publish(6, 1, &other, b"v=1 kind=ask").unwrap();
            god.commit(&format!("/f/{MESH}/cur/{NODE}/node/inbox"), w_off)
                .unwrap();
            god.commit(&carry_group(MESH), w_off).unwrap();
            god.commit(&inbox_group(NODE), o_off).unwrap();
            let mut seq = 0;
            flood(&mut god, 3, &mut seq, &session_ev(NODE, "s-a"), 8);
            let budget = |c: &mut Client| c.subject_budget(pid).unwrap().unwrap().subjects;
            assert_eq!(
                budget(&mut carry),
                2,
                "{what}: two lanes charged to the carry"
            );
            assert!(r_off < w_off, "{what}");
            let head = w.broker.visible_head();
            let day0 = w.tick(t0);
            assert_eq!(day0.forgotten, 0, "{what}: nothing is below the base yet");
            let tick = w.tick(t0 + 8 * DAY_MS);
            assert_eq!(
                tick.base, head,
                "{what}: the week cut takes it all: {tick:?}"
            );
            let rows = |c: &mut Client| {
                let mut rows = last_rows(c, &person_halt());
                rows.extend(last_rows(c, &node_presence(NODE)));
                rows
            };
            let (want_lanes, want_budget) = if mesh {
                assert_eq!(tick.forgotten, 1, "{what}: the read lane alone: {tick:?}");
                (vec![willed.clone()], 1)
            } else {
                assert_eq!(tick.forgotten, 0, "{what}: aterm's rules forget nothing");
                (vec![read.clone(), willed.clone()], 2)
            };
            assert_eq!(last_subjects(&mut god, &lanes), want_lanes, "{what}");
            assert_eq!(budget(&mut carry), want_budget, "{what}: the budget");
            assert_eq!(
                rows(&mut god),
                want_rows,
                "{what}: the halt and presence stay"
            );
            assert_eq!(
                last_subjects(&mut god, &node_mail(NODE)),
                vec![other.clone()],
                "{what}: the other fleet's lane stays"
            );

            drop((carry, god));
            let w = w.restart();
            let mut god = w.god();
            // A barrier behind the will the open may queue: its ack means the writer ran it.
            god.publish(9, 1, &format!("/f/{FLEET}/sentinel"), b"s")
                .unwrap();
            let mut carry = w.bound_in(MESH, CARRY);
            assert_eq!(
                last_subjects(&mut god, &lanes),
                want_lanes,
                "{what}: after a restart"
            );
            assert_eq!(
                budget(&mut carry),
                want_budget,
                "{what}: the budget, restarted"
            );
            assert_eq!(rows(&mut god), want_rows, "{what}: restarted");
            let after = w.tick(t0 + 9 * DAY_MS);
            assert_eq!(after.forgotten, 0, "{what}: nothing more: {after:?}");
        }
    }
}

/// (viii), the held lane: under the mesh's rules an alab lane with a record retention still
/// holds stays in `Last`, charged, whatever else of its producer's goes, until that record
/// goes.
///
/// The carry writes two lanes to an alab node; the node's inbox reads both, the carry's group
/// the first alone. A caller's cut to the visible head (`retain_before`, which plans by the rules
/// on the last tick's clock) passes both: the first, read by both readers, is given up, the
/// second held for the carry. After the next tick `Last` answers the second lane alone, and
/// the carry's budget keeps it; once the carry's group reads it, the next tick gives it up and
/// forgets it, and the budget is empty, after a restart too. The assertions read the state
/// after a hand tick, never one tick's count: here the cut is the caller's, after which a tick
/// of the ticker's thread may forget first.
///
/// LIVE CONTROL: the first lane, the same in all but the carry's read, is forgotten at the
/// tick that keeps the second.
#[test]
fn a_mail_lane_with_a_record_still_held_stays_charged_until_that_record_goes() {
    let (gone, held) = (
        lane(MESH, NODE, "s-a", PERSON, "ask"),
        lane(MESH, NODE, "s-b", PERSON, "ask"),
    );
    let lanes = format!("/f/{MESH}/in/{NODE}/>");
    let pid = producer_id_of(CARRY);
    let inc = incarnation_base(1).unwrap();
    for durability in arms() {
        let what = format!("{durability:?}");
        let w = World::open("held-lane", durability, mesh_rules());
        let t0 = now_ms();
        let mut carry = w.bound_in(MESH, CARRY);
        let (g_off, _) = carry.publish(pid, inc + 1, &gone, b"v=1 kind=ask").unwrap();
        let (h_off, _) = carry.publish(pid, inc + 2, &held, b"v=1 kind=ask").unwrap();
        let mut god = w.god();
        god.commit(&format!("/f/{MESH}/cur/{NODE}/node/inbox"), h_off)
            .unwrap();
        god.commit(&carry_group(MESH), g_off).unwrap();
        let budget = |c: &mut Client| c.subject_budget(pid).unwrap().unwrap().subjects;
        assert_eq!(budget(&mut carry), 2, "{what}");
        w.tick(t0);
        let visible = w.broker.visible_head();
        assert!(w.broker.retain_before(visible).unwrap() > 0, "{what}");
        assert!(w.base() > h_off, "{what}: the cut passes both lanes");
        w.tick(t0 + HOUR_MS);
        assert_eq!(
            read_from_zero(&mut god, &held),
            Ok(vec![h_off]),
            "{what}: the carry's unread record is held"
        );
        assert_eq!(
            last_subjects(&mut god, &lanes),
            vec![held.clone()],
            "{what}: the read lane is forgotten, the held one stays"
        );
        assert_eq!(budget(&mut carry), 1, "{what}: and stays charged");

        god.commit(&carry_group(MESH), h_off).unwrap();
        w.tick(t0 + 2 * HOUR_MS);
        assert_eq!(
            last_subjects(&mut god, &lanes),
            Vec::<String>::new(),
            "{what}: once its record went, the lane too"
        );
        assert_eq!(budget(&mut carry), 0, "{what}: the budget given back");

        drop((carry, god));
        let w = w.restart();
        let mut god = w.god();
        let mut carry = w.bound_in(MESH, CARRY);
        assert_eq!(
            last_subjects(&mut god, &lanes),
            Vec::<String>::new(),
            "{what}: after a restart"
        );
        assert_eq!(budget(&mut carry), 0, "{what}: restarted");
    }
}
