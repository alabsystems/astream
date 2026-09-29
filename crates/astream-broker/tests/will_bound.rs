//! A WILL'S TARGET SUBJECT IS RESERVED AT REGISTRATION, AND THE
//! RESERVATION IS DURABLE.
//!
//! `stage_will_register` checked the per-producer distinct-subject bound against the
//! subject the will would publish to, and then staged a record on the hidden
//! `/a/will` subject — which is outside the bound entirely. So the target was
//! validated and never RESERVED: every live connection read the same count, N of them
//! registering wills for N distinct new subjects all passed, and the firings (exempt
//! from the bound, because a firing's refusal reaches nobody) took the producer one
//! subject past `MAX_SUBJECTS_PER_PRODUCER` per accepted connection. Repeated waves
//! grew the last-value index without limit — the exact resource the bound caps.
//!
//! The round-2 test covered one will at a full producer. One will is what the defect
//! survives: the count is only wrong once a SECOND registration is outstanding. The
//! FIRST test here holds two outstanding registrations, which is that shape. The second
//! pins the other half — that a SINGLE registration's reservation is rebuilt from the
//! log on open — and holds one will, on one connection. It is not an instance of the
//! two-outstanding shape, and the restart path is in fact where the coverage narrows:
//! `reserve_pending_will_subjects` rebuilds from `pending_wills()`, which holds at most
//! one will per producer, so two live reservations under one producer become one across
//! a restart (disclosed in `will_reserved`'s rustdoc and in the claim text).
//!
//! No sleeps as synchronisation: each step blocks on the `Will`/`publish` ack, on a
//! subscriber delivery, or on a joined broker shutdown.
#![cfg(unix)]

use astream_broker::store::{BrokerLog, Durability, MAX_SUBJECTS_PER_PRODUCER};
use astream_broker::{Broker, Client};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr3will_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr3will_{tag}_{pid}_{n}.log"),
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

/// The design's incarnation rule: a will publishes at the RESERVED TOP of its
/// incarnation's sequence space.
fn will_seq(inc: u64) -> u64 {
    (inc << 32) | 0xFFFF_FFFF
}

const PID: u64 = 7;

/// Fill `PID`'s distinct-subject budget to `MAX_SUBJECTS_PER_PRODUCER - spare`.
fn seed(log_path: &str, spare: usize) {
    let mut log = BrokerLog::open_with(log_path, Durability::Relaxed).unwrap();
    for i in 0..MAX_SUBJECTS_PER_PRODUCER - spare {
        log.publish(PID, i as u64, format!("/f/F/s/{i:05}"), b"x".to_vec())
            .unwrap();
    }
    assert_eq!(
        log.subjects_per_producer(PID),
        MAX_SUBJECTS_PER_PRODUCER - spare
    );
}

/// TWO LIVE REGISTRATIONS FOR TWO DISTINCT NEW SUBJECTS SPEND TWO UNITS OF BUDGET.
/// The producer is two subjects short of the cap; two wills fit exactly, a third does
/// not, and the two that fit fire and land — reaching the cap, never passing it.
///
/// Before the fix the third registration was accepted too (and a fourth, and a
/// hundredth): each one saw only the LANDED subjects, so the budget the two
/// outstanding wills had already spoken for was handed out again per connection.
#[test]
fn two_outstanding_wills_cannot_be_registered_past_the_distinct_subject_bound() {
    let p = fresh("multi");
    seed(&p.log, 2);

    let b = Broker::open(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();

    // Two connections, one producer, two DISTINCT new subjects. Both fit: 4094 landed
    // + 2 reserved = the cap exactly.
    let mut c1 = Client::connect(&p.sock).unwrap();
    c1.will(PID, will_seq(1), "/f/F/w/one", b"one gone")
        .unwrap();
    let mut c2 = Client::connect(&p.sock).unwrap();
    c2.will(PID, will_seq(2), "/f/F/w/two", b"two gone")
        .unwrap();

    // Re-registering a subject this producer already holds a will for spends nothing
    // more — the reservation is per subject, not per registration.
    c2.will(PID, will_seq(2), "/f/F/w/two", b"two gone, again")
        .unwrap();

    // The third is over the cap, and the client is told NOW, while it is listening.
    let head = b.head();
    let mut c3 = Client::connect(&p.sock).unwrap();
    let e = c3
        .will(PID, will_seq(3), "/f/F/w/three", b"three gone")
        .expect_err("a third will was accepted: the budget two wills hold was handed out again");
    assert!(e.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"), "{e}");
    assert_eq!(b.head(), head, "a refused registration appends nothing");
    drop(c3);

    // Both accepted wills still fire, in order: each delivery is the synchronisation
    // point (a delivered record is a committed one), so `c1`'s firing lands before
    // `c2` is dropped and the fence cannot suppress it.
    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(b.visible_head(), "/f/F/w/*")
        .unwrap();
    drop(c1);
    assert_eq!(sub.recv().unwrap().unwrap().2, b"one gone".to_vec());
    drop(c2);
    assert_eq!(sub.recv().unwrap().unwrap().2, b"two gone, again".to_vec());
    drop(sub);
    h.shutdown();

    // The cap is REACHED, not passed, and nothing of the budget is left over.
    let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
    assert_eq!(
        log.subjects_per_producer(PID),
        MAX_SUBJECTS_PER_PRODUCER,
        "two wills landed two subjects; the producer must sit exactly on its cap"
    );
    let err = log
        .publish(PID, 90_000, "/f/F/w/four".into(), b"x".to_vec())
        .expect_err("a producer on its cap took another subject");
    assert!(
        err.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"),
        "{err}"
    );
}

/// THE RESERVATION SURVIVES A RESTART. A reservation that lived only in RAM would give
/// the producer its spent budget back at the next open — the same hole, one restart
/// later. It is rebuilt from the log's own `/a/will` records.
///
/// The log is a REPLICA so the will stays REGISTERED AND UNFIRED across the restart
/// with no race to arrange: a replica never fires the wills it holds (they are the
/// leader's, and they fire there), neither when a connection ends nor on open. That is
/// the deterministic way to reach the state the reservation has to survive.
#[test]
fn a_registered_wills_reservation_is_rebuilt_from_the_log_on_open() {
    let p = fresh("restart");
    seed(&p.log, 1);

    {
        let b = Broker::open_replica(&p.log).unwrap();
        let mut h = b.serve(&p.sock).unwrap();
        let mut c = Client::connect(&p.sock).unwrap();
        // The producer's last free subject, spoken for by a will.
        c.will(PID, will_seq(1), "/f/F/w/one", b"one gone").unwrap();
        drop(c); // the firing is refused here: this log is a replication target
        h.shutdown();
    }

    let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
    assert_eq!(
        log.pending_wills().len(),
        1,
        "the log must still hold the registered will — otherwise this proves nothing"
    );
    assert_eq!(
        log.subjects_per_producer(PID),
        MAX_SUBJECTS_PER_PRODUCER - 1,
        "the will did not fire, so its subject has not landed"
    );

    // ONE subject of budget is left and the registered will holds it: a SECOND new
    // subject is refused, on the fresh open, with no connection in sight.
    let err = log
        .publish(PID, 90_000, "/f/F/w/two".into(), b"x".to_vec())
        .expect_err("the restart handed back the budget the registered will holds");
    assert!(
        err.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"),
        "{err}"
    );

    // The reserved subject itself is still publishable — a reservation is not a lock,
    // and it is charged once: publishing it discharges the reservation and lands the
    // subject, leaving the producer exactly on its cap.
    log.publish(PID, 90_001, "/f/F/w/one".into(), b"x".to_vec())
        .expect("a producer must be able to publish the subject its own will reserved");
    assert_eq!(log.subjects_per_producer(PID), MAX_SUBJECTS_PER_PRODUCER);
    let err = log
        .publish(PID, 90_002, "/f/F/w/three".into(), b"x".to_vec())
        .expect_err("a producer on its cap took another subject");
    assert!(
        err.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"),
        "{err}"
    );
}
