//! Capability enforcement on the paths a single per-request check does not cover.
//!
//! - A subscription is ONE request that then streams for as long as the connection
//!   lives, so authorizing it once at subscribe time let it outlive the capability
//!   that authorized it. It must end, with an error that says why, at the deadline.
//! - A guarded broker whose secret is EMPTY guards nothing: HMAC under an empty key
//!   is computable by anyone, so anyone can mint any capability. It must not open.

#![cfg(all(unix, feature = "cap"))]

use astream_broker::{Broker, BrokerHandle, Client};
use astream_cap::mint;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

static CTR: AtomicU64 = AtomicU64::new(0);
const SECRET: &[u8] = b"core-cap-hardening";

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

fn paths() -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ascore_cap_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let sock = format!("/tmp/ascore_cap_{pid}_{n}.sock");
    (Cleanup::new(&[&log, &sock]), log, sock)
}

fn fresh() -> (Cleanup, Broker, BrokerHandle, String) {
    let (tmp, log, sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as u64)
}

/// A writer holding a non-expiring capability for the whole tree.
fn writer(sock: &str) -> Client {
    let god = mint(SECRET, "rw:/>").unwrap();
    let mut w = Client::connect(sock).unwrap();
    w.attach(&god.filter, &god.tag).unwrap();
    w
}

/// A subscription under traffic stops delivering once its capability expires: every
/// record is either delivered before the deadline or refused with `expired`.
#[test]
fn a_streaming_subscription_ends_when_its_capability_expires() {
    let (_tmp, _b, mut h, sock) = fresh();
    let mut w = writer(&sock);
    let soon = now_ms() + 400;
    let cap = mint(SECRET, &format!("ro,exp={soon}:/a/s/>")).unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&cap.filter, &cap.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();

    w.publish(1, 0, "/a/s/x", b"before").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"before");

    let bound = now_ms() + 10_000;
    let mut seq = 1u64;
    let refusal = loop {
        w.publish(1, seq, "/a/s/x", b"more").unwrap();
        seq += 1;
        match sub.recv() {
            Ok(Some(_)) => assert!(
                now_ms() < bound,
                "the capability expired at {soon} and the subscription still delivers"
            ),
            Ok(None) => panic!("the subscription ended without saying why"),
            Err(e) => break e.to_string(),
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(refusal.contains("expired"), "{refusal}");
    assert!(now_ms() >= soon, "refused before its deadline");
    drop(sub);
    h.shutdown();
}

/// A PARKED subscription (no traffic) ends at the deadline too, not whenever the
/// next matching record happens to arrive.
#[test]
fn a_parked_subscription_ends_at_its_capabilitys_expiry() {
    let (_tmp, _b, mut h, sock) = fresh();
    let soon = now_ms() + 300;
    let cap = mint(SECRET, &format!("ro,exp={soon}:/a/s/>")).unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&cap.filter, &cap.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();
    sub.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let err = sub
        .recv()
        .expect_err("a subscription with nothing to deliver outlived its capability");
    assert!(err.to_string().contains("expired"), "{err}");
    assert!(now_ms() >= soon, "refused before its deadline");
    drop(sub);
    h.shutdown();
}

/// A capability with no expiry keeps its subscription open indefinitely, and a
/// subscription authorized by SEVERAL grants lasts as long as the latest of them.
#[test]
fn a_subscription_lasts_as_long_as_the_latest_grant_that_authorizes_it() {
    let (_tmp, _b, mut h, sock) = fresh();
    let mut w = writer(&sock);
    let short = mint(SECRET, &format!("ro,exp={}:/a/s/>", now_ms() + 200)).unwrap();
    let long = mint(SECRET, "ro:/a/>").unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&short.filter, &short.tag).unwrap();
    r.attach(&long.filter, &long.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();
    std::thread::sleep(Duration::from_millis(500)); // past the short grant's deadline
    w.publish(1, 0, "/a/s/x", b"still").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"still");
    drop(sub);
    h.shutdown();
}

#[test]
fn open_guarded_refuses_an_empty_secret() {
    let (_tmp, log, _sock) = paths();
    let err = Broker::open_guarded(&log, Vec::new())
        .err()
        .expect("a guarded broker opened with an empty secret");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{err}");
}
