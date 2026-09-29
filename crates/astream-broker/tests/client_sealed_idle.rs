//! Regression: a SEALED subscription has the idle window the design promises a direct
//! consumer.
//!
//! §6.3 tells a direct consumer to drain with `client::drain` and to bound the idle
//! window with `Subscription::set_read_timeout`, and §8.6 tells a fabric node to use
//! the sealed/identity transport. `set_read_timeout` existed only for
//! `Subscription<UnixStream>` and `Subscription<TcpStream>`, so on the transport the
//! design mandates there was no way to bound the read at all: `take` waited in
//! `read_frame` for a delivery that never came, and the turn never returned. The CLI
//! sidestepped it by cloning the raw `TcpStream` out of the sealed wrapper; the
//! library helper had nothing.
//!
//! Before the fix this file does not compile (`no method named set_read_timeout`).
//! Run it with `cargo test -p astream-broker --features aead --test client_sealed_idle`.
//!
//! No sleeps: the drain loop re-drains until the records are in hand, and the test
//! COMPLETING is the assertion — a subscription with no idle window parks in the read
//! and never returns.
#![cfg(feature = "aead")]

use astream_broker::client::{drain, take};
use astream_broker::{Broker, BrokerHandle, Client};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

const KEY: [u8; 32] = [
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00,
    0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0,
];

const LANE: &str = "/f/F/in/p/h-andrew/>";
const SUBJ: &str = "/f/F/in/p/h-andrew/turn";
const GROUP: &str = "/f/F/cur/p/h-andrew/inbox";

/// The idle window. It bounds reads expected to find nothing; the loop below re-drains
/// rather than assert on one window.
const IDLE: Duration = Duration::from_millis(250);

/// How many idle windows the drain loop may burn before it is declared hung. Generous
/// on purpose (~50s), not a performance assertion.
const MAX_ROUNDS: usize = 200;

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<PathBuf>);

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

fn sealed_broker(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = std::env::temp_dir().join(format!("asr2sealed_{tag}_{pid}_{n}.log"));
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&log]);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();
    (tmp, broker, h, addr)
}

/// The §6.3 direct consumer, on the transport §8.6 mandates: subscribe, bound the idle
/// window, drain per turn. An empty inbox answers empty instead of parking.
#[test]
fn a_sealed_group_subscription_can_bound_its_idle_window() {
    let (_tmp, _b, _h, addr) = sealed_broker("idle");

    let mut prod = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    prod.publish(1, 1, SUBJ, b"one").unwrap();
    prod.publish(1, 2, SUBJ, b"two").unwrap();

    let mut sub = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe_group(GROUP, LANE)
        .unwrap();
    // The method under test: without it there is no way to bound this read.
    sub.set_read_timeout(Some(IDLE)).unwrap();
    let mut committer = Client::connect_tcp_sealed(&addr, KEY).unwrap();

    let mut got: Vec<(u64, String, Vec<u8>)> = Vec::new();
    let mut rounds = 0;
    while got.len() < 2 {
        got.extend(drain(&mut sub, &mut committer, GROUP, 64).unwrap());
        rounds += 1;
        assert!(rounds < MAX_ROUNDS, "the sealed drain never caught up");
    }
    assert_eq!(got[0].2, b"one".to_vec());
    assert_eq!(got[1].2, b"two".to_vec());

    // The empty turn: this returns because the idle window exists. Before the fix the
    // consumer had no window to set and this call never came back.
    assert!(drain(&mut sub, &mut committer, GROUP, 64)
        .unwrap()
        .is_empty());

    // Clearing it is the same call; the read is unbounded again (not exercised here —
    // an unbounded read on an empty inbox is the park this test exists to rule out).
    sub.set_read_timeout(None).unwrap();

    // The commit landed on the sealed connection too.
    let mut again = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe_group(GROUP, LANE)
        .unwrap();
    again.set_read_timeout(Some(IDLE)).unwrap();
    assert!(take(&mut again, 64).unwrap().is_empty());
}

/// The generic escape hatch, for a stream type with no `set_read_timeout` of its own:
/// `get_ref` reaches the socket under the subscription. Here it reaches the `TcpStream`
/// under the sealed record layer — the same handle the CLI had to clone out of the
/// wrapper before it could bound a read.
#[test]
fn get_ref_reaches_the_socket_under_a_sealed_subscription() {
    let (_tmp, _b, _h, addr) = sealed_broker("getref");
    let sub = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe_group(GROUP, LANE)
        .unwrap();
    sub.get_ref()
        .get_ref()
        .set_read_timeout(Some(IDLE))
        .unwrap();
}
