//! Claim `cap.expiry-enforced`: a capability can carry an EXPIRY, the expiry is
//! inside the signed material, and a guarded broker stops honouring the
//! capability at that instant -- at the attach door and on every later request.
//!
//! The gap this closes: a capability had no key distribution, rotation or
//! revocation surface of its own. A
//! minted capability was valid for as long as the broker's secret was, so the
//! only way to withdraw one was to rotate the secret and reissue EVERY other
//! capability with it. An expiry is the smallest honest revocation surface: a
//! grant that stops working on its own, with no new crypto, no new wire field
//! and no broker state -- because the tag is already an HMAC over the whole
//! grant string, so `exp=` is signed for free and cannot be stripped, shortened
//! or extended without the secret.
//!
//! The pure half (the grammar, the half-open boundary, all four predicates
//! refusing, and the tamper cases) is unit-tested in `astream-cap`, which reads
//! no clock. This file is the BROKER half: the wall clock is read at the
//! connection boundary, so the enforcement is only real if it is proven against
//! a broker that reads one.
#![cfg(all(unix, feature = "cap"))]

use astream_broker::proto::ERR_UNAUTHORIZED;
use astream_broker::{broker_refusal, Broker, BrokerHandle, BrokerRefusal, Client};
use astream_cap::{mint, Capability};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

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

fn fresh(secret: &[u8]) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/asexp_{pid}_{n}.sock");
    let log = format!("/tmp/asexp_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

/// Unix milliseconds, as the BROKER reads them. The test needs the same clock to
/// write a deadline the broker will agree with.
fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as u64)
}

/// The broker's own refusal inside `err`, which a refused request must carry.
fn refusal_of(err: &std::io::Error) -> &BrokerRefusal {
    broker_refusal(err).unwrap_or_else(|| panic!("not a broker refusal: {err}"))
}

/// An expiry already in the past is refused AT THE DOOR, and the refusal says
/// `expired` rather than `does not verify` -- the two failures need different
/// remedies, and an operator told "does not verify" would go and rotate a secret
/// that is perfectly fine.
#[test]
fn an_expired_capability_is_refused_at_the_attach_door() {
    let secret = b"expiry-secret";
    let (_tmp, _b, _h, sock) = fresh(secret);
    // 1970-01-01T00:00:00.001Z: expired on any machine whose clock is set.
    let cap = mint(secret, "rw,exp=1:/a/stream/s1/>").unwrap();

    let mut c = Client::connect(&sock).unwrap();
    let err = c
        .attach(&cap.filter, &cap.tag)
        .expect_err("an expired capability must not attach");
    let msg = err.to_string();
    assert!(msg.contains("expired"), "refusal should name expiry: {msg}");
    assert!(
        !msg.contains("does not verify"),
        "an expired capability is GENUINE; that message means a bad secret: {msg}"
    );

    // And it authorizes nothing, because it never entered the keyring.
    assert!(c.publish(1, 1, "/a/stream/s1/out", b"nope").is_err());
}

/// A client tells an EXPIRED capability from every other unauthorized refusal BY
/// TYPE, with no wire change: `BrokerRefusal::is_expired` reads code 8 under the
/// words astream owns (`proto::CAP_EXPIRED_PREFIX`). Every refusal below is code 8,
/// so the code alone cannot tell them apart.
///
/// The never-granted capability carries the SAME lapsed `exp=1`, minted under
/// another secret. The broker never granted it, so it is a forgery here, and it must
/// not read as an expiry: the reading is the broker's verdict, not the deadline
/// written in the grant string.
#[test]
fn a_lapsed_grant_reads_as_expired_and_no_other_unauthorized_refusal_does() {
    let secret = b"expiry-secret";
    let (_tmp, _b, _h, sock) = fresh(secret);

    let lapsed = mint(secret, "rw,exp=1:/a/stream/s1/>").unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let err = c
        .attach(&lapsed.filter, &lapsed.tag)
        .expect_err("a lapsed capability must not attach");
    let r = refusal_of(&err);
    assert_eq!(r.code, ERR_UNAUTHORIZED, "{r}");
    assert!(
        r.is_expired(),
        "a lapsed grant's refusal must read as expired: {r}"
    );
    // The expired grant never entered the keyring, so this connection holds nothing.
    // Its next request is refused because nothing covers it, which is not an expiry.
    let err = c
        .publish(1, 1, "/a/stream/s1/out", b"nope")
        .expect_err("an unattached connection must not publish");
    assert!(!refusal_of(&err).is_expired(), "{err}");

    let never = mint(b"another-secret", "rw,exp=1:/a/stream/s1/>").unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let err = c
        .attach(&never.filter, &never.tag)
        .expect_err("a capability this broker never granted must not attach");
    let r = refusal_of(&err);
    assert_eq!(r.code, ERR_UNAUTHORIZED, "{r}");
    assert!(
        !r.is_expired(),
        "a never-granted capability is not an expired one: {r}"
    );

    // A live grant asked for what it does not cover: unauthorized, not expired.
    let live = mint(secret, "rw:/a/stream/s1/>").unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.attach(&live.filter, &live.tag)
        .expect("a live grant attaches");
    let err = c
        .publish(1, 1, "/a/stream/s2/out", b"elsewhere")
        .expect_err("a subject outside the grant must be refused");
    let r = refusal_of(&err);
    assert_eq!(r.code, ERR_UNAUTHORIZED, "{r}");
    assert!(!r.is_expired(), "{r}");
}

/// The same grant, dated forward, is an ordinary working capability -- so the
/// refusal above is the expiry and not the field's mere presence.
#[test]
fn a_capability_dated_forward_works_exactly_as_one_without_an_expiry() {
    let secret = b"expiry-secret";
    let (_tmp, _b, _h, sock) = fresh(secret);
    let far = now_ms() + 60 * 60 * 1000; // an hour out
    let dated = mint(secret, &format!("rw,exp={far}:/a/stream/s1/>")).unwrap();
    let eternal = mint(secret, "rw:/a/stream/s1/>").unwrap();

    for (name, cap) in [("dated", &dated), ("eternal", &eternal)] {
        let mut c = Client::connect(&sock).unwrap();
        c.attach(&cap.filter, &cap.tag)
            .unwrap_or_else(|e| panic!("{name} should attach: {e}"));
        let (_off, _dup) = c
            .publish(
                1,
                CTR.fetch_add(1, Ordering::Relaxed) + 1,
                "/a/stream/s1/out",
                b"hi",
            )
            .unwrap_or_else(|e| panic!("{name} should publish: {e}"));
        let mut sub = c.subscribe(0, "/a/stream/s1/out").unwrap();
        sub.recv()
            .unwrap_or_else(|e| panic!("{name} should read: {e}"));
    }
}

/// THE PROPERTY AN EXPIRY IS FOR: a connection that attached while its
/// capability was live STOPS being authorized when the deadline passes. An
/// attach-time check alone would let a long-lived subscriber outlive its own
/// expiry forever, which is precisely the hole this closes.
///
/// It waits for an OBSERVED refusal rather than sleeping a fixed span: the loop
/// ends the moment the broker says no, so a slow machine makes it slower, never
/// flakier, and a broker that never refuses fails it on the bound.
#[test]
fn a_live_connection_loses_authority_when_its_capability_expires() {
    let secret = b"expiry-secret";
    let (_tmp, _b, _h, sock) = fresh(secret);
    let soon = now_ms() + 400;
    let cap = mint(secret, &format!("rw,exp={soon}:/a/stream/s1/>")).unwrap();

    let mut c = Client::connect(&sock).unwrap();
    c.attach(&cap.filter, &cap.tag)
        .expect("attaches while live");
    // Live now: the connection is genuinely authorized before the deadline.
    c.publish(1, 1, "/a/stream/s1/out", b"before")
        .expect("publishes before its expiry");

    let deadline = now_ms() + 30_000;
    let mut seq = 2u64;
    let refusal = loop {
        match c.publish(1, seq, "/a/stream/s1/out", b"after") {
            Err(e) => break e,
            Ok(_) => {
                assert!(
                    now_ms() < deadline,
                    "the capability expired at {soon} and the broker still authorized \
                     publishes 30s later: the per-request check is not running"
                );
                seq += 1;
                std::thread::yield_now();
            }
        }
    };
    assert!(
        refusal.to_string().contains("unauthorized"),
        "the refusal should be an authorization failure: {refusal}"
    );
    // The grant still COVERS the request; only its time is up. So the refusal names
    // the expiry, as the attach door does, rather than "does not grant".
    assert!(
        refusal_of(&refusal).is_expired(),
        "a request refused because its grant lapsed must read as expired: {refusal}"
    );
    assert!(
        now_ms() >= soon,
        "it must not be refused BEFORE its deadline"
    );
}

/// Over the wire, as in the library: a bearer who edits the deadline holds
/// something the broker refuses, because the proof of possession is computed
/// over the grant string the expiry lives in.
#[test]
fn an_edited_deadline_does_not_survive_the_attach_proof() {
    let secret = b"expiry-secret";
    let (_tmp, _b, _h, sock) = fresh(secret);
    let honest = mint(secret, "rw,exp=1:/a/stream/s1/>").unwrap();

    // Same tag, a deadline the bearer wrote themselves.
    let forged = Capability {
        filter: format!("rw,exp={}:/a/stream/s1/>", now_ms() + 60_000),
        tag: honest.tag,
    };
    let mut c = Client::connect(&sock).unwrap();
    let msg = c
        .attach(&forged.filter, &forged.tag)
        .expect_err("an extended deadline must not attach")
        .to_string();
    assert!(
        msg.contains("does not verify"),
        "an edited grant is FORGERY, and should read as one: {msg}"
    );
}
