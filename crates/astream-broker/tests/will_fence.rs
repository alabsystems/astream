//! Round-4 regression: AN ACK IS NOT AN INCARNATION, AND MUST NOT FENCE A WILL.
//!
//! Round 2 aligned `client::ack` with `asb ack` on `ACK_SEQ_BASE | offset`, which put
//! every ack at or above 2^63. That record is an ordinary visible publish, so it went
//! into the per-producer high water the LAST-WILL FENCE reads — and a will sits at its
//! incarnation's reserved top, `(inc << 32) | 0xFFFF_FFFF`, twelve orders of magnitude
//! below. One ack therefore fenced that producer's will for good: the goodbye never
//! landed when the connection died, the refusal reached nobody (a firing is
//! fire-and-forget), and every later open re-attempted and re-failed it, so a dead node
//! read `live` forever. A guarded broker binds one producer id per principal, so a node
//! that acks its inbox and registers a presence will has no way to avoid the pairing.
//!
//! Both tests here FAIL on the pre-fix code: the first because the goodbye never
//! arrives, the second because the registration is accepted.
//!
//! No sleeps as synchronisation: each step blocks on an ack or on a delivery. The
//! subscription's read timeout is a HANG DETECTOR with a deliberately generous
//! deadline, not a performance assertion.
#![cfg(unix)]

use astream_broker::{ack, Broker, Client, ACK_SEQ_BASE};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr4wf_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr4wf_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    let _ = std::fs::remove_file(format!("{}.replica", p.log));
    p
}

impl Drop for Paths {
    /// Remove the socket, the log and every `<path>.*` sidecar beside them (the
    /// broker's `.hw`, `.base`, `.replica`, …) on success and on panic alike. A test
    /// binds its `Paths` before serving on them, so this runs after the broker is gone.
    fn drop(&mut self) {
        remove_with_sidecars(&self.sock);
        remove_with_sidecars(&self.log);
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

/// The design's incarnation rule: a will publishes at the incarnation's reserved top.
fn will_seq(inc: u64) -> u64 {
    (inc << 32) | 0xFFFF_FFFF
}
fn live_seq(inc: u64, n: u64) -> u64 {
    (inc << 32) | n
}

const PID: u64 = 7;
const PRESENCE: &str = "/f/F/pub/n1/node/presence";

/// A node registers its presence will, says `state=live`, ACKS ONE INBOX MESSAGE under
/// the same producer id — the shape a bound grant forces — and then dies. The goodbye
/// must still land.
#[test]
fn an_ack_does_not_fence_the_acking_producers_will() {
    let p = fresh("ackwill");
    let broker = Broker::open(&p.log).unwrap();
    let mut h = broker.serve(&p.sock).unwrap();

    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/f/>")
        .unwrap();
    // Hang detector, not a performance assertion: every record this test waits for is
    // already durable when the wait starts.
    sub.set_read_timeout(Some(Duration::from_secs(30))).unwrap();

    {
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"state=gone inc=1")
            .unwrap();
        c.publish(PID, live_seq(1, 1), PRESENCE, b"state=live inc=1")
            .unwrap();
        // One ack, under the producer id that holds the will: `ACK_SEQ_BASE | 3`.
        let (_, deduped) = ack(&mut c, PID, "g", 3, "/f/F/pub/n1/answers", b"answer").unwrap();
        assert!(!deduped);
    } // the connection dies with no goodbye of its own

    let mut seen: Vec<(String, Vec<u8>)> = Vec::new();
    while seen.len() < 3 {
        match sub.recv() {
            Ok(Some(r)) => seen.push((r.1, r.2)),
            Ok(None) => panic!("the subscription closed before the goodbye landed: {seen:?}"),
            // The read timeout above is the hang detector: reaching it means the will
            // never fired, which is the defect.
            Err(e) => panic!("the will did not fire, so no goodbye ever arrived ({e}): {seen:?}"),
        }
    }
    assert_eq!(
        seen.last().map(|(s, b)| (s.as_str(), b.as_slice())),
        Some((PRESENCE, b"state=gone inc=1".as_slice())),
        "the will did not fire: one ack had fenced it. Saw {seen:?}"
    );
    h.shutdown();
}

/// A will may not be registered in the reserved ack half. The fence does not reach
/// there — that is the whole point of the fix above — so a will registered there could
/// never be fenced by a later record, and a goodbye its producer had already outlived
/// would fire over a live node's `state=live`. Refused where the client is listening.
#[test]
fn a_will_in_the_reserved_ack_half_is_refused_where_the_client_can_hear_it() {
    let p = fresh("willhalf");
    let broker = Broker::open(&p.log).unwrap();
    let mut h = broker.serve(&p.sock).unwrap();

    let mut c = Client::connect(&p.sock).unwrap();
    let err = c
        .will(PID, ACK_SEQ_BASE | 4, PRESENCE, b"state=gone")
        .expect_err("a will in the ack half was accepted");
    let msg = err.to_string();
    assert!(
        msg.contains("reserved for acks"),
        "refused, but not for the reason that matters: {msg}"
    );
    // One below the reservation is an ordinary will, and it still fires.
    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/f/>")
        .unwrap();
    sub.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    c.will(PID, ACK_SEQ_BASE - 1, PRESENCE, b"state=gone")
        .unwrap();
    drop(c);
    let r = sub.recv().unwrap().expect("no goodbye");
    assert_eq!(
        (r.1.as_str(), r.2.as_slice()),
        (PRESENCE, b"state=gone".as_slice())
    );
    h.shutdown();
}
