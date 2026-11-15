// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Claim `broker.guarded-at-rest`: THE BROKER aterm OPENS, SEALED AT REST. aterm's fabric
//! broker is guarded, served at Ordered with its 100 ms horizon (or a named `relaxed` or
//! `strict`), escalates by its table, retains its log by its four rules with a
//! state-carrying compaction, and keeps its health sidecar (aterm-link `durability::open`,
//! `broker_rules::default_rules`, `broker_health`). Here that broker is opened with an
//! at-rest key, bound (`OpenOptions::at_rest_key`, `require_bound_at_rest`), and every
//! property is held to the same broker opened without one:
//!
//! - the table escalates exactly what it does on a plaintext log, rule for rule
//!   (`guarded_durability::drive_on`, the same expectations), at Strict, Ordered (no
//!   horizon, so a full flush happens only where an escalation causes one) and Relaxed;
//! - at Ordered { 100 ms }, Relaxed and Strict, guarded, with aterm's rules
//!   (`aterm_fixture::scaled`) and the health sidecar kept: a person's mail is durable at
//!   its ack; a retention tick cuts below the person's mail and a presence row, which the
//!   held store and the carried state keep; the health sidecar names the log; a clean
//!   stop and a reopen read the held mail, the presence row and every retained record back,
//!   under the same identity.
//!
//! NEGATIVE CONTROLS, live: the SENTINEL SCAN of the log, `<log>.state` and `<log>.held`
//! finds each sentinel in the clear under the keyless arm, and none under the keyed one
//! (`<log>.health` holds none under either: counts and an identity only); with
//! `require_bound_at_rest` a deleted `<log>.seal` refuses the open, which opens again once
//! it is back; a keyless open of the sealed log refuses it.
//!
//! The table, the horizon and the rules are aterm's own fixtures
//! (`tests/fixtures/aterm-broker.escalate`, `aterm-broker.retain`), which aterm-link's
//! `astream_fixture_tests` holds equal to aterm's. Every wait for something that must
//! happen is an ack; nothing sleeps. The retention tick runs on a hand clock
//! (`Broker::retention_tick_at`); the tick's own thread runs too, at an hour.

#![cfg(all(unix, feature = "cap", feature = "at-rest", feature = "retention"))]

use super::aterm_fixture::{scaled, ATERM_RETAIN};
use super::guarded_durability::{
    aterm_horizon, aterm_table, drive_on, ATERM, ORDERED, SECRET, STRICT,
};
use astream_broker::{
    mint, read_health, Broker, BrokerHandle, Client, Durability, HealthWriter, OpenOptions,
    Prepared,
};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const KEY: [u8; 32] = [0x7b; 32];

/// aterm's rules' byte bounds, scaled so a test's records reach the bulk stream's.
const EV_BYTES: u64 = 4 * 1024;
const MAIL_BYTES: u64 = 256 * 1024;
const DEFAULT_BYTES: u64 = 256 * 1024;

const NODE: &str = "n-a1b2c3d4e5f60718";
const PERSON: &str = "h-x";

/// The sentinels: one per file the scan reads.
const LOG_SENTINEL: &[u8] = b"v=1 SENTINEL-RETAINED-IN-THE-LOG";
const MAIL_SENTINEL: &[u8] = b"v=1 SENTINEL-MAIL-HELD-BELOW-THE-CUT";
const PRESENCE_SENTINEL: &[u8] = b"v=1 SENTINEL-PRESENCE-CARRIED";
const EV_BODY: &[u8] = b"v=1 t=1 ev=0123456789abcdef0123456789abcdef0123456789abcdef";

static NEXT: AtomicU64 = AtomicU64::new(0);

/// An exclusive scratch directory under `/tmp` (a socket path stays under `SUN_LEN`),
/// removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asgar-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn log(&self) -> String {
        self.0.join("b.log").to_string_lossy().into_owned()
    }

    fn sock(&self, n: u32) -> String {
        self.0
            .join(format!("{n}.sock"))
            .to_string_lossy()
            .into_owned()
    }

    fn file(&self, sfx: &str) -> PathBuf {
        self.0.join(format!("b.log{sfx}"))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// The options aterm opens its fabric broker with at `durability` (aterm-link
/// `Durability::options` and `durability::open`): guarded, its table on a weak tier and none
/// on a named `strict`, its health sidecar kept; and, `keyed`, sealed at rest and bound.
fn aterm_opts(durability: Durability, keyed: bool, table: bool) -> OpenOptions {
    let mut opts = OpenOptions::new(durability);
    opts.guard = Some(SECRET.to_vec());
    if table {
        opts.escalation = astream_broker::Escalation::new(aterm_table());
    }
    opts.health_every = Some(Duration::from_secs(3600));
    if keyed {
        opts.at_rest_key = Some(KEY);
        opts.require_bound_at_rest = true;
    }
    opts
}

/// Open `log` with `opts`, its retention rules set at once as aterm sets them, served on
/// `sock`.
fn serve(log: &str, sock: &str, opts: OpenOptions) -> (Broker, BrokerHandle) {
    let broker = Broker::open_opts(log, opts, || Ok(Prepared::Nothing)).unwrap();
    broker.set_retention_interval(Duration::from_secs(3600));
    broker
        .set_retention(scaled(ATERM_RETAIN, EV_BYTES, MAIL_BYTES, DEFAULT_BYTES))
        .unwrap();
    let handle = broker.serve(sock).unwrap();
    (broker, handle)
}

/// A connection holding the god capability: unbound, the whole tree.
fn god(sock: &str) -> Client {
    let cap = mint(SECRET, "rw:/>").unwrap();
    let mut c = Client::connect(sock).unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    c
}

/// THE TABLE IS UNCHANGED BY THE SEAL: aterm's broker, sealed at rest and bound, escalates
/// exactly what the plaintext one does (`guarded_durability`'s
/// `a_guarded_broker_with_aterms_table_escalates_what_a_person_would_miss`, the same drive
/// and the same expectations), at Strict, Ordered and Relaxed.
#[test]
fn a_sealed_guarded_broker_with_aterms_table_escalates_what_a_person_would_miss() {
    for durability in [Durability::Strict, ORDERED, Durability::Relaxed] {
        let s = Scratch::new("tbl");
        let (log, sock) = (s.log(), s.sock(0));
        let mut opts = aterm_opts(durability, true, true);
        opts.health_every = None;
        let b = Broker::open_opts(&log, opts, || Ok(Prepared::Nothing)).unwrap();
        let mut h = b.serve(&sock).unwrap();
        let (holds, got) = drive_on(&b, &sock, durability, aterm_table().len());
        h.shutdown();
        let want = if holds { ATERM } else { STRICT };
        assert_eq!(got, want, "{durability:?}, sealed");
        drop(b);
        assert!(s.file(".seal").exists(), "{durability:?}: bound");
    }
}

/// Which files hold their sentinel: the log `LOG_SENTINEL`, `.held` the held mail's,
/// `.state` the carried presence row's; and whether ANY sentinel is in any of the three,
/// or in `.health`.
fn scan(s: &Scratch) -> ([bool; 3], bool, bool) {
    let read = |sfx: &str| std::fs::read(s.file(sfx)).unwrap_or_default();
    let (log, held, state, health) = (read(""), read(".held"), read(".state"), read(".health"));
    let all = [LOG_SENTINEL, MAIL_SENTINEL, PRESENCE_SENTINEL];
    let any = [&log, &held, &state]
        .iter()
        .any(|f| all.iter().any(|n| contains(f, n)));
    (
        [
            contains(&log, LOG_SENTINEL),
            contains(&held, MAIL_SENTINEL),
            contains(&state, PRESENCE_SENTINEL),
        ],
        any,
        all.iter().any(|n| contains(&health, n)),
    )
}

/// aterm's broker, keyless or sealed, at `durability`: what it is checked to hold.
fn arm(durability: Durability, keyed: bool) {
    let what = format!("{durability:?}, keyed {keyed}");
    let table = durability != Durability::Strict;
    let s = Scratch::new("arm");
    let log = s.log();
    let (b, mut h) = serve(&log, &s.sock(0), aterm_opts(durability, keyed, table));
    let mut c = god(&s.sock(0));
    let t0 = now_ms();

    // A person's mail: escalated on every weak tier (the table's `/f/*/in/p/>`), a full
    // flush per batch at Strict, so durable at its ack either way.
    let mail_subject = format!("/f/F/in/p/{PERSON}/{NODE}");
    let (mail, _) = c.publish(2, 1, &mail_subject, MAIL_SENTINEL).unwrap();
    assert!(
        b.durable_head() > mail,
        "{what}: a person's mail durable at its ack"
    );
    let presence = format!("/f/F/pub/{NODE}/node/presence");
    let (row, _) = c.publish(5, 1, &presence, PRESENCE_SENTINEL).unwrap();
    let ev = format!("/f/F/pub/{NODE}/s-a/ev");
    for seq in 1..=96u64 {
        c.publish(3, seq, &ev, EV_BODY).unwrap();
    }
    let tick = b.retention_tick_at(t0).unwrap();
    assert!(
        tick.base > mail.max(row),
        "{what}: the cut passes the mail and the row: {tick:?}"
    );
    let (newest, _) = c.publish(3, 1000, &ev, LOG_SENTINEL).unwrap();
    for sfx in [".state", ".held", ".health"] {
        assert!(s.file(sfx).exists(), "{what}: {sfx}");
    }
    assert_eq!(s.file(".seal").exists(), keyed, "{what}: `.seal`");

    // The health sidecar names the log its serving writer serves.
    let read = read_health(&log).unwrap().expect("the health sidecar");
    assert_eq!(read.writer, HealthWriter::Serving, "{what}");
    assert_eq!(read.health.identity, b.log_identity(), "{what}");

    let held = |c: &mut Client| {
        let (page, _) = c.fetch(0, "/f/F/in/>", 64).unwrap();
        page.into_iter().map(|r| (r.0, r.2)).collect::<Vec<_>>()
    };
    let rows = |c: &mut Client| {
        let (page, _) = c.last(&presence, "", 8).unwrap();
        page.into_iter().map(|r| (r.0, r.2)).collect::<Vec<_>>()
    };
    let want_held = vec![(mail, MAIL_SENTINEL.to_vec())];
    let want_rows = vec![(row, PRESENCE_SENTINEL.to_vec())];
    assert_eq!(held(&mut c), want_held, "{what}: the held mail");
    assert_eq!(rows(&mut c), want_rows, "{what}: the presence row");
    let (base, head, identity) = (b.stats().log.base.0, b.head(), b.log_identity());
    drop(c);
    h.shutdown();
    drop(b);
    assert_eq!(
        read_health(&log).unwrap().map(|r| r.writer),
        Some(HealthWriter::Gone),
        "{what}: the last word after a clean stop"
    );

    // THE SENTINEL SCAN.
    let (found, any, in_health) = scan(&s);
    if keyed {
        assert!(
            !any,
            "{what}: a sentinel in the clear in the log, .state or .held: {found:?}"
        );
    } else {
        assert_eq!(
            found, [true; 3],
            "{what}: NC: the scan sees each sentinel in the clear"
        );
    }
    assert!(!in_health, "{what}: a record in the health sidecar");

    // The reopen reads it all back, under the same identity. (Its rules, set again at once,
    // may cut the bulk stream further at the tick their bytes ask for: the base only rises.)
    let (b, mut h) = serve(&log, &s.sock(1), aterm_opts(durability, keyed, table));
    let mut c = god(&s.sock(1));
    assert_eq!(
        (b.head(), b.log_identity()),
        (head, identity),
        "{what}: the reopen"
    );
    assert!(b.stats().log.base.0 >= base, "{what}: the base went back");
    assert_eq!(held(&mut c), want_held, "{what}: the held mail, reopened");
    assert_eq!(
        rows(&mut c),
        want_rows,
        "{what}: the presence row, reopened"
    );
    let (page, _) = c.fetch(newest, &ev, 1).unwrap();
    assert_eq!(
        page.into_iter().map(|r| r.2).collect::<Vec<_>>(),
        vec![LOG_SENTINEL.to_vec()],
        "{what}: the newest record, reopened"
    );
    drop(c);
    h.shutdown();
    drop(b);
    if !keyed {
        return;
    }

    // NEGATIVE CONTROLS on the sealed arm: a keyless open refuses it; bound, a deleted
    // `.seal` refuses the open, which opens again once it is back.
    let err = Broker::open_opts(&log, aterm_opts(durability, false, table), || {
        Ok(Prepared::Nothing)
    })
    .err()
    .expect("a keyless open read the sealed log");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{what}: {err}");
    let aside = s.0.join("seal-aside");
    std::fs::rename(s.file(".seal"), &aside).unwrap();
    let err = Broker::open_opts(&log, aterm_opts(durability, true, table), || {
        Ok(Prepared::Nothing)
    })
    .err()
    .expect("a bound open read a log whose `.seal` was deleted");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{what}: {err}");
    assert!(err.to_string().contains(".seal"), "{what}: {err}");
    std::fs::rename(&aside, s.file(".seal")).unwrap();
    let b = Broker::open_opts(&log, aterm_opts(durability, true, table), || {
        Ok(Prepared::Nothing)
    })
    .unwrap();
    assert_eq!(b.head(), head, "{what}: opens again with its `.seal`");
}

/// aterm's broker at Ordered { 100 ms } (its default, the horizon from aterm's fixture),
/// Relaxed and Strict, keyless and sealed: escalation, retention carrying state, the held
/// store, the health sidecar and the reopen hold alike, and the sealed arm leaves no
/// sentinel in the clear (see the module docs).
#[test]
fn aterms_broker_sealed_at_rest_retains_reopens_and_leaves_nothing_in_the_clear() {
    let ordered = Durability::Ordered {
        horizon: Some(aterm_horizon()),
    };
    for durability in [ordered, Durability::Relaxed, Durability::Strict] {
        for keyed in [false, true] {
            arm(durability, keyed);
        }
    }
}
