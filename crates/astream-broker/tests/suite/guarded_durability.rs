// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Claim `broker.guarded-durability`: a GUARDED broker takes the durability dial
//! (`Broker::open_guarded_with`, and `Broker::open_opts` with `guard`), and the guard
//! and the tier stay orthogonal. A Relaxed guarded broker enforces the capability guard
//! exactly as a Strict one does — an un-attached connection, an out-of-grant publish or
//! subscribe and a forged capability are all refused, and an empty secret is refused at
//! every tier — while its acks follow the batch's page-cache write, not its fsync.
//! `open_guarded` stays the Strict shorthand: a Strict guarded broker still acks only
//! after the fsync.
//!
//! "Acks without the per-batch fsync" is witnessed through the log's documented
//! fault-injection seam (`InjectedFaults`, the one `broker.group-commit-durability`
//! uses): with every fsync of the log made to fail, a Relaxed guarded broker still
//! acks, delivers and recovers what it acked, and a Strict guarded broker answers the
//! same publish `commit failed` with nothing promoted. No sleeps: every step
//! synchronizes on an ack, a refusal or a delivery.
//!
//! THE BROKERS aterm OPENS. aterm opens its fabric broker through `Broker::open_opts`
//! with a guard (aterm-link `durability::open`), and which table it hands that open
//! depends on the aterm:
//!
//! - aterm MAIN, since ordered/5: `Durability::options` hands every weak tier its
//!   escalation table (aterm-link `durability::escalation`) and a named `strict` none;
//!   `Durability::tier` opens a named `ordered` as astream Ordered at aterm's horizon
//!   (`durability::ORDERED_HORIZON`) and a named `relaxed` as Relaxed, guarded with the
//!   table; and `durability::default_for` makes guarded + Ordered with that table the
//!   default of a bare guarded broker — the one `aterm fabric on` runs — on every
//!   platform, leaving to astream where it is served: Ordered on Apple with the log on the
//!   boot volume and a barrier the device accepts at the open, Strict elsewhere, with the
//!   reason. The table and the horizon are read here from
//!   `tests/fixtures/aterm-broker.escalate` (`aterm_table`, `aterm_horizon`), which
//!   aterm-link's `astream_fixture_tests` holds equal to aterm's own: neither side moves
//!   without failing aterm's test until the other moves with it.
//!   `a_guarded_broker_with_aterms_table_escalates_what_a_person_would_miss` opens that
//!   table, rule for rule.
//! - an aterm BEFORE ordered/5 (0.107.0 and older) handed it NO table. 0.106.0 and
//!   0.107.0 served `ordered` as astream Strict: guarded + Strict, or guarded + Relaxed
//!   with nothing escalated, so a person's halt or mail on their `relaxed` broker was
//!   acked on the page-cache write like any other record; older ones open Strict only.
//!   `every_guarded_open_takes_every_tier` opens exactly that, beside
//!   `open_guarded_with`, at every tier.
//!
//! One other test module opens a guarded broker with a table, through `serve_like_aterm`
//! and `aterm_table` here: `aterm_retention`, which holds aterm's retention rules to that
//! broker and drives no `h-` producer. The `ordered_tier` brokers are unguarded, and an
//! unguarded broker binds nobody, so their `PrincipalPrefix` rule never matches anything
//! (`escalation.rs`). The crash simulation has no guard layer at all. So the principal
//! rule — the one that catches a person's records by WHO wrote them — is exercised end to
//! end only here: a bound `h-` grant
//! attaches, the attach's bind goes through the writer, and the bound producer's publish
//! in a later batch is flushed in full before its ack, while its will registration (a
//! hidden record by the same bound producer) is not. Every kind of record aterm's
//! table is about goes through real capabilities on one such broker, and each rule is
//! dropped in turn to show it is the rule that escalates its own record.

#![cfg(all(unix, feature = "cap"))]

use astream_broker::{
    producer_id_of, Broker, BrokerHandle, BrokerLog, Client, Durability, Escalate, Escalation,
    FlushCounts, InjectedFaults, OpenOptions, Prepared, ServedReason, Tier,
};
use astream_cap::{mint, Capability};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);
pub(super) const SECRET: &[u8] = b"guarded-durability-secret";

/// Exclusive short scratch ownership, removed after every broker and socket
/// handle has dropped, including on unwind. Never remove a preexisting path.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A log and socket under one exclusively created, private directory. A fixed
/// short prefix keeps Unix socket paths below sockaddr limits.
fn paths(_tag: &str) -> (Cleanup, String, String) {
    use std::os::unix::fs::DirBuilderExt;
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::path::PathBuf::from(format!("/tmp/asgdur-{pid}-{n}"));
    let mut builder = std::fs::DirBuilder::new();
    builder
        .mode(0o700)
        .create(&dir)
        .expect("exclusive scratch directory");
    let log = dir.join("bus.log").to_string_lossy().into_owned();
    let sock = dir.join("bus.sock").to_string_lossy().into_owned();
    (Cleanup(dir), log, sock)
}

/// A guarded broker over `log` at `durability`, served on `sock`.
fn serve(log: &str, sock: &str, durability: Durability) -> (Broker, BrokerHandle) {
    let broker = Broker::open_guarded_with(log, SECRET.to_vec(), durability).unwrap();
    let handle = broker.serve(sock).unwrap();
    (broker, handle)
}

/// A connection that has attached `cap`.
fn attached(sock: &str, cap: &Capability) -> Client {
    let mut c = Client::connect(sock).unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    c
}

/// THE GUARD DOES NOT READ THE TIER. Every refusal `broker.cap-enforced-on-attach`
/// proves of `open_guarded` holds on a Relaxed guarded broker: no attach, no
/// publish; a grant's own subtree publishes and is delivered, a sibling's is refused
/// for both verbs; a capability minted under another secret is refused at the
/// attach itself.
#[test]
fn a_relaxed_guarded_broker_enforces_the_guard() {
    let (_tmp, log, sock) = paths("guard");
    let (_b, mut h) = serve(&log, &sock, Durability::Relaxed);
    let cap = mint(SECRET, "/a/g/s1/>").unwrap();

    // No attach at all: reachability is not access.
    let err = Client::connect(&sock)
        .unwrap()
        .publish(1, 1, "/a/g/s1/out", b"anon")
        .unwrap_err();
    assert!(
        err.to_string().contains("unauthorized"),
        "un-attached: {err}"
    );

    // Within the grant: acked at a dense offset.
    let mut a = attached(&sock, &cap);
    assert_eq!(a.publish(1, 1, "/a/g/s1/out", b"hi").unwrap(), (0, false));

    // Outside the grant: refused, and nothing landed.
    let err = attached(&sock, &cap)
        .publish(2, 1, "/a/g/s2/out", b"nope")
        .unwrap_err();
    assert!(err.to_string().contains("unauthorized"), "sibling: {err}");

    // A forged capability (another secret) is refused at the attach.
    let forged = mint(b"some-other-secret", "/a/g/s1/>").unwrap();
    let err = Client::connect(&sock)
        .unwrap()
        .attach(&forged.filter, &forged.tag)
        .unwrap_err();
    assert!(err.to_string().contains("unauthorized"), "forged: {err}");

    // Subscribe: the sibling's subtree is refused (at the request or the first
    // recv), the grant's own is delivered — and holds exactly the one record.
    let refused = match attached(&sock, &cap).subscribe(0, "/a/g/s2/>") {
        Err(_) => true,
        Ok(mut s) => s.recv().is_err(),
    };
    assert!(refused, "a subscribe outside the grant was served");
    let mut sub = attached(&sock, &cap).subscribe(0, "/a/g/s1/>").unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (0, "/a/g/s1/out".to_string(), b"hi".to_vec())
    );
    drop(sub);
    drop(a);
    h.shutdown();
}

/// An empty secret is refused at EVERY tier, Ordered included, by both guarded opens
/// that take a tier: `open_guarded_with`, and `open_opts` with `guard` (the open aterm
/// calls, here with aterm's table). HMAC under an empty key is computable by anyone,
/// whatever an ack promises. Each refusal comes before the log is created.
#[test]
fn a_guarded_open_refuses_an_empty_secret_at_every_tier() {
    for durability in [Durability::Strict, ORDERED, Durability::Relaxed] {
        for how in ["open_guarded_with", "open_opts"] {
            let (_tmp, log, _sock) = paths("empty");
            let opened = if how == "open_guarded_with" {
                Broker::open_guarded_with(&log, Vec::new(), durability)
            } else {
                let mut opts = OpenOptions::new(durability);
                opts.guard = Some(Vec::new());
                opts.escalation = Escalation::new(aterm_table());
                Broker::open_opts(&log, opts, || Ok(Prepared::Nothing))
            };
            let err = opened
                .err()
                .expect("a guarded broker opened with an empty secret");
            assert_eq!(
                err.kind(),
                std::io::ErrorKind::InvalidInput,
                "{how} {durability:?}: {err}"
            );
            assert!(
                !std::path::Path::new(&log).exists(),
                "{how} {durability:?}: the log was created before the refusal"
            );
        }
    }
}

/// RELAXED ACKS WITHOUT THE BATCH FSYNC. With every fsync of the log failing, a
/// Relaxed guarded broker acks a pipelined batch and a lone publish, moves its head,
/// delivers the records to a guarded subscriber, and a reopen recovers exactly them:
/// the page-cache write was the whole of the ack. (The reopen's own fsync is the
/// open's, not a batch's, and the fault was armed on the broker that is gone.)
#[test]
fn a_relaxed_guarded_broker_acks_without_the_batch_fsync() {
    let (_tmp, log, sock) = paths("relaxed");
    let cap = mint(SECRET, "/a/g/>").unwrap();
    {
        let (b, mut h) = serve(&log, &sock, Durability::Relaxed);
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: false,
        });
        let mut p = attached(&sock, &cap);
        for s in 1..=4u64 {
            p.send_publish(7, s, "/a/g/x", format!("r{s}").as_bytes())
                .unwrap();
        }
        for s in 1..=4u64 {
            assert_eq!(
                p.recv_publish_ack().unwrap(),
                (s - 1, false),
                "pipelined publish {s} was not acked at Relaxed"
            );
        }
        assert_eq!(p.publish(7, 5, "/a/g/x", b"r5").unwrap(), (4, false));
        assert_eq!(b.head(), 5, "every Relaxed ack was promoted");
        let mut sub = attached(&sock, &cap).subscribe(0, "/a/g/>").unwrap();
        for off in 0..5 {
            assert_eq!(sub.recv().unwrap().unwrap().0, off, "delivered in order");
        }
        drop(sub);
        drop(p);
        h.shutdown();
    }
    let recovered = BrokerLog::open(&log).unwrap();
    let bodies: Vec<Vec<u8>> = recovered
        .read_from(astream_wire::Offset::ZERO)
        .iter()
        .map(|r| r.body.clone())
        .collect();
    assert_eq!(
        bodies,
        (1..=5)
            .map(|s| format!("r{s}").into_bytes())
            .collect::<Vec<_>>(),
        "a reopen recovers exactly the Relaxed acks"
    );
    drop(recovered);
}

/// STRICT IS UNCHANGED. `open_guarded` and `open_guarded_with(Strict)` alike answer
/// a publish `commit failed` while the fsync fails — nothing promoted, the head
/// unmoved — and land it once the fault clears: a Strict guarded ack still means
/// fsync'd.
#[test]
fn a_strict_guarded_broker_still_acks_only_after_the_fsync() {
    let cap = mint(SECRET, "/a/g/>").unwrap();
    for name in ["open_guarded", "open_guarded_with"] {
        let (_tmp, log, sock) = paths("strict");
        let b = if name == "open_guarded" {
            Broker::open_guarded(&log, SECRET.to_vec()).unwrap()
        } else {
            Broker::open_guarded_with(&log, SECRET.to_vec(), Durability::Strict).unwrap()
        };
        let mut h = b.serve(&sock).unwrap();
        let mut p = attached(&sock, &cap);
        assert_eq!(p.publish(7, 1, "/a/g/x", b"d1").unwrap(), (0, false));
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: false,
        });
        let err = p.publish(7, 2, "/a/g/x", b"lost").unwrap_err();
        assert!(
            err.to_string().contains("commit failed"),
            "{name}: a Strict guarded publish acked without its fsync: {err}"
        );
        assert_eq!(
            b.head(),
            1,
            "{name}: nothing promoted while the fsync fails"
        );
        b.inject_faults(InjectedFaults::default());
        assert_eq!(
            p.publish(7, 2, "/a/g/x", b"d2").unwrap(),
            (1, false),
            "{name}: the same key lands once the disk does"
        );
        drop(p);
        h.shutdown();
    }
}

// ---------------------------------------------------------------------------------
// aterm's brokers: guarded at Ordered or Relaxed with its escalation table (aterm main
// since ordered/5), and guarded at every tier with no table (an aterm before it).
// ---------------------------------------------------------------------------------

/// aterm's escalation table and Ordered horizon, as text (`parse_escalation_file`): the
/// fixture aterm-link's `astream_fixture_tests` holds equal to `durability::escalation`
/// and `durability::ORDERED_HORIZON`.
const ATERM_ESCALATE: &str = include_str!("../fixtures/aterm-broker.escalate");

/// The escalation table aterm opens its weak tiers with, rule for rule and in its order
/// (aterm-link `durability::escalation`, read from `ATERM_ESCALATE`): the records a
/// person would miss after a power loss.
pub(super) fn aterm_table() -> Vec<Escalate> {
    let table = astream_broker::parse_escalation(ATERM_ESCALATE)
        .unwrap_or_else(|e| panic!("tests/fixtures/aterm-broker.escalate: {e}"));
    table.rules().to_vec()
}

/// The horizon aterm opens Ordered at (aterm-link `durability::ORDERED_HORIZON`, read from
/// `ATERM_ESCALATE`), for `aterm_retention`'s brokers.
#[cfg(feature = "retention")]
pub(super) fn aterm_horizon() -> std::time::Duration {
    match astream_broker::parse_escalation_file(ATERM_ESCALATE) {
        Ok((_, Some(horizon))) => horizon,
        Ok((_, None)) => panic!("tests/fixtures/aterm-broker.escalate names no horizon"),
        Err(e) => panic!("tests/fixtures/aterm-broker.escalate: {e}"),
    }
}

/// Ordered with NO horizon. aterm opens Ordered at a 100 ms horizon (aterm-link
/// `durability::ORDERED_HORIZON`, `aterm_horizon`), but the horizon only ADDS full
/// flushes on a timer: it never reads the table, which the broker matches as each
/// record is staged. With a horizon running, "an ordinary record is not durable at its
/// ack" would race that timer, so here a full flush happens only where an escalation
/// causes one (the convention `ordered_tier` keeps for the same reason).
pub(super) const ORDERED: Durability = Durability::Ordered { horizon: None };

/// aterm's person and node principals: a human (`h-`) and a machine (`n-`).
const PERSON: &str = "h-andrew";
const NODE: &str = "n-a1b2c3d4";

/// A broker opened the way aterm opens its fabric broker: `Broker::open_opts`, guarded
/// by `SECRET`, with `rules` as its escalation table (aterm's on its weak tiers since
/// ordered/5; empty before it, and on a named `strict`), served on `sock`.
pub(super) fn serve_like_aterm(
    log: &str,
    sock: &str,
    durability: Durability,
    rules: Vec<Escalate>,
) -> (Broker, BrokerHandle) {
    let mut opts = OpenOptions::new(durability);
    opts.guard = Some(SECRET.to_vec());
    opts.escalation = Escalation::new(rules);
    let broker = Broker::open_opts(log, opts, || Ok(Prepared::Nothing)).unwrap();
    let handle = broker.serve(sock).unwrap();
    (broker, handle)
}

/// Whether `b` HOLDS an ordinary ack short of a full flush: the tiers on which the
/// table can be seen at all. Relaxed always does, and Strict never does (every batch is
/// a full flush). Ordered does on Apple with the log on the boot volume (`/tmp` is).
/// Anywhere else Ordered is served Strict, never weaker, with the reason, and that
/// serving is what gets asserted instead. Also checks that all `rules` reached the
/// broker (the size `Hello` reports).
fn holds(b: &Broker, durability: Durability, rules: usize) -> bool {
    let served = b.served_durability();
    assert_eq!(
        usize::from(served.rules),
        rules,
        "the table the open was handed"
    );
    let told = (served.requested, served.served, served.reason);
    if durability == Durability::Relaxed {
        assert_eq!(told, (Tier::Relaxed, Tier::Relaxed, ServedReason::None));
        true
    } else if durability == Durability::Strict {
        assert_eq!(told, (Tier::Strict, Tier::Strict, ServedReason::None));
        false
    } else if cfg!(target_vendor = "apple") {
        assert_eq!(told, (Tier::Ordered, Tier::Ordered, ServedReason::None));
        true
    } else {
        assert_eq!(told, (Tier::Ordered, Tier::Strict, ServedReason::NotApple));
        false
    }
}

/// Whether the record acked at `offset` was ESCALATED: durable at its ack (the durable
/// head already above its offset) at the cost of exactly one full flush. On a tier that
/// holds, an ordinary record is neither: the durable head stays at or below it and no
/// full flush runs (these brokers have no horizon, and nothing here calls
/// `flush_durable`). Served Strict, every batch is one full flush, so every record reads
/// as escalated. Anything in between (durable with no flush, a flush that left it
/// uncovered, a failed flush) is no broker this file describes, and fails here.
///
/// Read after the ack arrives: a broker that answered first and flushed a moment later
/// reads here as "not escalated" unless this thread is the slower one. The race-free
/// order is `broker::tests::held_head`'s; this corroborates it on aterm's configuration.
fn escalated(b: &Broker, before: FlushCounts, offset: u64) -> bool {
    let after = b.flush_counts();
    assert_eq!(
        after.failed, before.failed,
        "offset {offset}: a flush failed"
    );
    let durable = b.durable_head() > offset;
    match (durable, after.full - before.full) {
        (true, 1) => true,
        (false, 0) => false,
        (durable, full) => {
            panic!("offset {offset}: durable at its ack {durable}, with {full} full flush(es)")
        }
    }
}

/// What a broker did with each kind of record aterm's table is about: `true` when
/// it was escalated (see [`escalated`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Kinds {
    /// The hidden `/a/bind` record a person's first attach appends.
    bind: bool,
    /// The person's own publish, on a subject no subject rule names.
    person: bool,
    /// The person's will registration: a hidden `/a/will` record by the same BOUND
    /// producer, in a later batch.
    will: bool,
    /// A node's publish on a lane no rule names.
    node: bool,
    /// The same node's mail onto a person's lane.
    mail: bool,
    /// The unbound god cap's publish on the fleet face.
    fleet: bool,
    /// The node's record on its own halt subject.
    halt: bool,
    /// A group commit on a person's inbox (a hidden `/a/commit`, producer 0).
    commit: bool,
}

/// What aterm's whole table escalates on a tier that holds: everything a person
/// would miss, and none of these three:
///
/// - the bind. Its producer is not bound yet when the record is staged (the log stages
///   `/a/bind`, THEN records the binding it carries), so the principal rule has nobody
///   to read, and no subject rule names `/a/...`. The person's publish right after it
///   is flushed in full, and that flush covers the bind. This says nothing about hidden
///   subjects;
/// - the person's will registration. Its producer IS bound to `h-andrew`, so only the
///   hidden-subject exclusion (`escalation.rs`: hidden records never match the subject
///   or principal rules) keeps the principal rule from dragging every `/a/will` a person
///   registers into a full flush. This is the field that checks that exclusion;
/// - a node's own chatter.
pub(super) const ATERM: Kinds = Kinds {
    bind: false,
    person: true,
    will: false,
    node: false,
    mail: true,
    fleet: true,
    halt: true,
    commit: true,
};

/// Served Strict: every batch is a full flush, so every record is durable at its ack.
pub(super) const STRICT: Kinds = Kinds {
    bind: true,
    person: true,
    will: true,
    node: true,
    mail: true,
    fleet: true,
    halt: true,
    commit: true,
};

/// Open a broker the way aterm does, with `rules` at `durability`, and drive one record
/// of each kind through real capabilities, each in its own batch ([`drive_on`]).
fn drive(durability: Durability, rules: Vec<Escalate>) -> (bool, Kinds) {
    let (_tmp, log, sock) = paths("aterm");
    let count = rules.len();
    let (b, mut h) = serve_like_aterm(&log, &sock, durability, rules);
    let out = drive_on(&b, &sock, durability, count);
    h.shutdown();
    out
}

/// Drive one record of each kind through real capabilities, each in its own batch, on `b`
/// (served on `sock`, opened at `durability` with a table of `rules` rules; nothing written
/// to it yet). Returns whether the tier holds (see [`holds`]) and what was escalated.
pub(super) fn drive_on(
    b: &Broker,
    sock: &str,
    durability: Durability,
    rules: usize,
) -> (bool, Kinds) {
    let sock = sock.to_string();
    let holds = holds(b, durability, rules);

    // The guard is on: reachability is not access.
    let err = Client::connect(&sock)
        .unwrap()
        .publish(1, 1, "/f/F/fleet/x", b"anon")
        .unwrap_err();
    assert!(
        err.to_string().contains("unauthorized"),
        "un-attached: {err}"
    );

    // A PERSON. The bound grant's first attach binds the person's producer id through
    // the writer: one round trip, nothing settled from the broker's copy, one hidden
    // `/a/bind` record, visible at the attach's ack.
    let grant = mint(SECRET, &format!("rw,p={PERSON}:/f/F/in/n/*/{PERSON}/*")).unwrap();
    let (stats, head, before) = (b.stats(), b.head(), b.flush_counts());
    let mut person = Client::connect(&sock).unwrap();
    let (_, acked_head) = person.attach(&grant.filter, &grant.tag).unwrap();
    let after = b.stats();
    assert_eq!(
        after.writer_round_trips,
        stats.writer_round_trips + 1,
        "the person's bind went to the writer"
    );
    assert_eq!(
        after.binds_settled, stats.binds_settled,
        "a first bind is settled by nothing"
    );
    assert_eq!(
        (acked_head, b.head()),
        (head + 1, head + 1),
        "one /a/bind record, visible at the attach's ack"
    );
    let bind = escalated(b, before, head);
    // In a LATER batch (the binding promoted, not staged beside it), the bound
    // producer's publish on a lane no subject rule names: only the principal rule can
    // tell it is a person's.
    let before = b.flush_counts();
    let (off, _) = person
        .publish(
            producer_id_of(PERSON),
            1,
            &format!("/f/F/in/n/s/{PERSON}/ask"),
            b"a person's word",
        )
        .unwrap();
    let person_record = escalated(b, before, off);
    // The SAME bound producer registers its last will, in a batch of its own: one hidden
    // `/a/will` record, at the head the registration found. Its principal is `h-andrew`
    // by now, so only the hidden-subject exclusion keeps it out of the principal rule.
    // Under the key the person already published, so the goodbye the drop below fires is
    // the no-op its dedup makes it, and nothing lands after these readings.
    let (head, before) = (b.head(), b.flush_counts());
    let (_, will_head) = person
        .will(
            producer_id_of(PERSON),
            1,
            &format!("/f/F/in/n/s/{PERSON}/gone"),
            b"a person's goodbye",
        )
        .unwrap();
    assert_eq!(
        (will_head, b.head()),
        (head + 1, head + 1),
        "one /a/will record, visible at the registration's ack"
    );
    let will = escalated(b, before, head);

    // A NODE, bound too, but `n-` is a machine: its own chatter rides the tier...
    let grant = mint(SECRET, &format!("rw,p={NODE}:/f/F/in/*/*/{NODE}/*")).unwrap();
    let mut node = attached(&sock, &grant);
    let before = b.flush_counts();
    let (off, _) = node
        .publish(
            producer_id_of(NODE),
            1,
            &format!("/f/F/in/n/s/{NODE}/note"),
            b"machine chatter",
        )
        .unwrap();
    let node_record = escalated(b, before, off);
    // ...and its mail onto a person's lane is caught by WHERE it goes.
    let before = b.flush_counts();
    let (off, _) = node
        .publish(
            producer_id_of(NODE),
            2,
            &format!("/f/F/in/p/{PERSON}/{NODE}/mail"),
            b"mail for a person",
        )
        .unwrap();
    let mail = escalated(b, before, off);
    // ...and so is its record on its own halt subject.
    let grant = mint(SECRET, &format!("rw,p={NODE}:/f/F/halt/{NODE}")).unwrap();
    let mut halting = attached(&sock, &grant);
    let before = b.flush_counts();
    let (off, _) = halting
        .publish(
            producer_id_of(NODE),
            3,
            &format!("/f/F/halt/{NODE}"),
            b"a halt",
        )
        .unwrap();
    let halt = escalated(b, before, off);

    // THE GOD CAP: unbound, so the principal rule has nobody to read; its write on the
    // fleet face is caught by the subject rule alone.
    let root = mint(SECRET, "/f/F/>").unwrap();
    let mut god = attached(&sock, &root);
    let before = b.flush_counts();
    let (off, _) = god.publish(9, 1, "/f/F/fleet/x", b"halt").unwrap();
    let fleet = escalated(b, before, off);
    // A PERSON'S INBOX COMMIT: a hidden `/a/commit` by producer 0, which only the group
    // rule sees, whoever commits it.
    let before = b.flush_counts();
    let off = god.commit("/f/F/cur/p/x", off + 1).unwrap();
    let commit = escalated(b, before, off);

    drop((person, node, halting, god));
    (
        holds,
        Kinds {
            bind,
            person: person_record,
            will,
            node: node_record,
            mail,
            fleet,
            halt,
            commit,
        },
    )
}

/// The broker aterm serves since ordered/5 (aterm-link `Durability::options`): guarded,
/// with aterm's whole table (`aterm_table`, the fixture), at Ordered and at Relaxed. A
/// bound `h-` grant attaches and its bind goes through the writer; the bound producer's
/// publish in a later batch is durable at its ack, for one full flush, and its will
/// registration after that is not. A bound `n-` grant's publish on its own lane is not
/// escalated, while its mail onto a person's lane is, and so is its record on its own halt
/// subject. The unbound god cap's publish on
/// `/f/F/fleet/x` is, by the subject rule (it has no principal), and so is a group commit
/// on `/f/F/cur/p/x`. Off Apple, Ordered is served Strict, and that serving is asserted
/// instead.
///
/// The same table at STRICT stands in, on every host, for that off-Apple serving: the
/// write path reads the tier SERVED (`decide_served`), so a broker asked for Strict and
/// one whose Ordered was served Strict flush every batch in full alike, and every record
/// reads as durable at its ack. Only the reason differs, which `holds` checks apart.
#[test]
fn a_guarded_broker_with_aterms_table_escalates_what_a_person_would_miss() {
    for durability in [Durability::Strict, ORDERED, Durability::Relaxed] {
        let (holds, got) = drive(durability, aterm_table());
        let want = if holds { ATERM } else { STRICT };
        assert_eq!(got, want, "{durability:?}");
    }
}

/// A relayed record lands escalated as it would have if published here, though its origin never
/// attached to this broker: its id derives from the owner its subject names. A table escalating
/// one node's records leaves another's alone, the negative control.
#[cfg(feature = "relay")]
#[test]
fn a_relayed_record_is_escalated_on_a_broker_its_origin_never_attached_to() {
    use astream_broker::{identity_principal, origin};
    let (seed, other_seed) = ([1; 32], [2; 32]);
    let principal = identity_principal(&origin::public_key(&seed));
    let other = identity_principal(&origin::public_key(&other_seed));
    let (_tmp, log, sock) = paths("relayed");
    let rules = vec![Escalate::PrincipalPrefix(principal.clone())];
    let (b, h) = serve_like_aterm(&log, &sock, ORDERED, rules);
    if !holds(&b, ORDERED, 1) {
        return;
    }
    b.set_origin_keys([origin::public_key(&seed), origin::public_key(&other_seed)]);
    let cap = mint(SECRET, "rw,relay,p=n-carrier:/>").unwrap();
    let mut carrier = attached(&sock, &cap);

    let subject = format!("/m/{other}/cpu");
    let before = b.flush_counts();
    let (off, _) = carrier
        .relay(
            astream_cap::producer_id_of(&other),
            1,
            &subject,
            &origin::seal(&other_seed, &subject, 1, b"not named"),
        )
        .unwrap();
    assert!(!escalated(&b, before, off), "no rule names this node");

    let subject = format!("/m/{principal}/cpu");
    let before = b.flush_counts();
    let (off, _) = carrier
        .relay(
            astream_cap::producer_id_of(&principal),
            1,
            &subject,
            &origin::seal(&seed, &subject, 1, b"named"),
        )
        .unwrap();
    assert!(escalated(&b, before, off), "the node's rule covers it");
    drop(h);
}

/// EVERY GUARDED OPEN TAKES EVERY TIER. `open_guarded_with(log, secret, tier)` and
/// `open_opts` with `guard = Some(secret)` and NO table — the open an aterm before
/// ordered/5 (0.107.0 and older) made, at astream Strict for its `strict` and `ordered`
/// and at Relaxed for its `relaxed`, and the one aterm main makes for a named `strict` —
/// each open at Strict, Ordered and Relaxed. Each reports the tier asked for and the tier
/// served (Ordered served Strict off Apple, with the reason) and no rules; each is
/// guarded (an un-attached publish refused, the grant's own subtree acked at offset 0, a
/// sibling's refused); and each ack keeps its tier's promise with nothing escalated:
/// served Strict, durable at its ack for one full flush; Ordered or Relaxed, neither (a
/// person's record on such an aterm's `relaxed` broker rode the page cache like any
/// other).
#[test]
fn every_guarded_open_takes_every_tier() {
    let cap = mint(SECRET, "/a/g/s1/>").unwrap();
    for durability in [Durability::Strict, ORDERED, Durability::Relaxed] {
        for how in ["open_guarded_with", "open_opts"] {
            let (_tmp, log, sock) = paths("every");
            let (b, mut h) = if how == "open_guarded_with" {
                serve(&log, &sock, durability)
            } else {
                serve_like_aterm(&log, &sock, durability, Vec::new())
            };
            let holds = holds(&b, durability, 0);

            let err = Client::connect(&sock)
                .unwrap()
                .publish(1, 1, "/a/g/s1/out", b"anon")
                .unwrap_err();
            assert!(
                err.to_string().contains("unauthorized"),
                "{how} {durability:?}: un-attached: {err}"
            );

            let mut a = attached(&sock, &cap);
            let before = b.flush_counts();
            assert_eq!(
                a.publish(1, 1, "/a/g/s1/out", b"hi").unwrap(),
                (0, false),
                "{how} {durability:?}: the grant's own subtree"
            );
            assert_eq!(
                escalated(&b, before, 0),
                !holds,
                "{how} {durability:?}: durable at its ack only where served Strict"
            );

            let err = a.publish(1, 2, "/a/g/s2/out", b"nope").unwrap_err();
            assert!(
                err.to_string().contains("unauthorized"),
                "{how} {durability:?}: sibling: {err}"
            );
            assert_eq!(
                b.head(),
                1,
                "{how} {durability:?}: the refusal landed nothing"
            );
            drop(a);
            h.shutdown();
        }
    }
}

/// NEGATIVE CONTROLS: each rule is the one that escalates its record, and no other.
/// Drop `PrincipalPrefix("h-")` and the person's publish is no longer durable at its
/// ack: on a guarded broker the binding is what makes it a person's, and no other rule
/// names its subject. Drop any subject rule or the group rule, and exactly its own
/// record goes back to riding the tier. Everything else is unchanged in each case.
#[test]
fn each_rule_of_aterms_table_is_the_one_that_escalates_its_record() {
    /// The one record a rule alone escalates, as its field of [`Kinds`].
    type Record = fn(&mut Kinds) -> &mut bool;
    let cases: [(Escalate, Record); 5] = [
        (Escalate::PrincipalPrefix("h-".into()), |k| &mut k.person),
        (Escalate::Subject("/f/*/fleet/>".into()), |k| &mut k.fleet),
        (Escalate::Subject("/f/*/halt/>".into()), |k| &mut k.halt),
        (Escalate::Subject("/f/*/in/p/>".into()), |k| &mut k.mail),
        (Escalate::Group("/f/*/cur/p/>".into()), |k| &mut k.commit),
    ];
    for durability in [ORDERED, Durability::Relaxed] {
        for (dropped, its_record) in &cases {
            let rules: Vec<Escalate> = aterm_table().into_iter().filter(|r| r != dropped).collect();
            assert_eq!(rules.len(), 4, "{dropped:?} is one of aterm's rules");
            let (holds, got) = drive(durability, rules);
            let mut want = if holds { ATERM } else { STRICT };
            if holds {
                *its_record(&mut want) = false;
            }
            assert_eq!(got, want, "{durability:?} without {dropped:?}");
        }
    }
}
