//! Claim `broker.inbox-drain-ack-exactly-once` (fabric R6): the inbox loop as two
//! library helpers over the built primitives — `client::drain`, the two-connection
//! durable-group drain whose commit lands AFTER the records are in the caller's hands,
//! and `client::ack`, the read-process-write ack that appends the answer and advances
//! the cursor in ONE durable record.
//!
//! The crash is modelled the way the broker's own tests model it: the client
//! connections are dropped at the point of interest and reopened. No sleeps —
//! `Subscription::set_read_timeout` bounds the one place a test asserts that NOTHING
//! more is delivered.
#![cfg(unix)]

use astream_broker::client::{ack, drain, take};
use astream_broker::{Broker, BrokerHandle, Client};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

/// The idle window `take` stops on. Every drain below asks for a count it KNOWS is
/// there, so this bounds exactly one read in the file: the assertion that a fully
/// committed group delivers NOTHING. A bound on a read expected to find nothing is
/// not a sleep hiding a race — there is no ordering here for it to hide.
const IDLE: Duration = Duration::from_millis(250);

const LANE: &str = "/f/F/in/n1/s1/>";
const GROUP: &str = "/f/F/cur/n1/node/inbox";

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asdrain_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asdrain_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
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

fn serve(p: &Paths) -> (Broker, BrokerHandle) {
    let broker = Broker::open(&p.log).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// A group subscription with an idle bound, so `take` stops instead of parking.
fn group_sub(sock: &str) -> astream_broker::Subscription {
    let sub = Client::connect(sock)
        .unwrap()
        .subscribe_group(GROUP, LANE)
        .unwrap();
    sub.set_read_timeout(Some(IDLE)).unwrap();
    sub
}

fn bodies(records: &[(u64, String, Vec<u8>)]) -> Vec<String> {
    records
        .iter()
        .map(|(_, _, b)| String::from_utf8_lossy(b).into_owned())
        .collect()
}

/// The drain's crash semantics, both sides of the commit: a consumer that dies
/// BEFORE the commit sees the same records again; one that dies AFTER never does.
#[test]
fn a_crash_before_the_commit_redelivers_and_after_it_does_not() {
    let p = fresh("crash");
    let (_b, _h) = serve(&p);
    let mut w = Client::connect(&p.sock).unwrap();
    for i in 1..=3u64 {
        w.publish(1, i, "/f/F/in/n1/s1/h-a/ask", format!("m{i}").as_bytes())
            .unwrap();
    }

    // (1) CRASH BEFORE THE COMMIT: take two records on the group subscription and
    //     drop it, with no committer ever opened.
    {
        let mut sub = group_sub(&p.sock);
        let taken = take(&mut sub, 2).unwrap();
        assert_eq!(bodies(&taken), vec!["m1", "m2"]);
    }

    // (2) A new drain sees them AGAIN — at-least-once, never lost.
    {
        let mut sub = group_sub(&p.sock);
        let mut committer = Client::connect(&p.sock).unwrap();
        let got = drain(&mut sub, &mut committer, GROUP, 2).unwrap();
        assert_eq!(
            bodies(&got),
            vec!["m1", "m2"],
            "redelivered after the crash"
        );
    }

    // (3) CRASH AFTER THE COMMIT: the next drain resumes past them.
    {
        let mut sub = group_sub(&p.sock);
        let mut committer = Client::connect(&p.sock).unwrap();
        let got = drain(&mut sub, &mut committer, GROUP, 1).unwrap();
        assert_eq!(
            bodies(&got),
            vec!["m3"],
            "committed records never come back"
        );
    }

    // (4) And once everything is committed, a fresh drain finds nothing at all.
    {
        let mut sub = group_sub(&p.sock);
        let mut committer = Client::connect(&p.sock).unwrap();
        assert!(drain(&mut sub, &mut committer, GROUP, 8)
            .unwrap()
            .is_empty());
    }
}

/// The ack is ONE read-process-write record: a retry is deduped, appends nothing, and
/// the cursor moved exactly once.
#[test]
fn a_retried_ack_is_deduped_appends_nothing_and_moves_the_cursor_once() {
    let p = fresh("ack");
    let (_b, _h) = serve(&p);
    let mut w = Client::connect(&p.sock).unwrap();
    let (r, _) = w
        .publish(1, 1, "/f/F/in/n1/s1/h-a/ask", b"which branch?")
        .unwrap();
    w.publish(1, 2, "/f/F/in/n1/s1/h-a/ask", b"and then?")
        .unwrap();

    let mut sub = group_sub(&p.sock);
    let got = take(&mut sub, 1).unwrap();
    assert_eq!(got[0].0, r);

    // The ack: the answer record AND the cursor advance, atomically.
    let mut c = Client::connect(&p.sock).unwrap();
    let (ack_off, deduped) = ack(
        &mut c,
        42,
        GROUP,
        r,
        "/f/F/in/p/h-a/n1/ack",
        b"v=1 state=handled",
    )
    .unwrap();
    assert!(!deduped);
    let head_after = c.last("/f/>", "", 0).unwrap().1 .1;

    // The RETRY — the shape of a killed turn re-running its ack.
    let (retry_off, retry_deduped) = ack(
        &mut c,
        42,
        GROUP,
        r,
        "/f/F/in/p/h-a/n1/ack",
        b"v=1 state=handled",
    )
    .unwrap();
    assert_eq!((retry_off, retry_deduped), (ack_off, true));
    assert_eq!(
        c.last("/f/>", "", 0).unwrap().1 .1,
        head_after,
        "the retry appended nothing"
    );

    // The cursor moved exactly once: a new group subscription resumes at the SECOND
    // record, never re-delivering the acked one and never skipping past it.
    let mut sub2 = group_sub(&p.sock);
    let got = take(&mut sub2, 1).unwrap();
    assert_eq!(bodies(&got), vec!["and then?"]);

    // The ack record itself is on the log, once, on the sender's lane.
    let (page, _) = c.last("/f/F/in/p/h-a/n1/ack", "", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].0, ack_off);
}

/// The request/reply shape the fabric is built on: an `ask` published at offset `R`
/// is answered by a record on the ASKER's lane carrying `re=R`, and the asker's own
/// drain finds it. The correlation id is the broker-assigned offset — dense, unique
/// and unforgeable, not a client-chosen header.
#[test]
fn an_answer_correlated_by_the_asks_offset_is_found_by_the_askers_drain() {
    let p = fresh("askreply");
    let (_b, _h) = serve(&p);
    let asker_group = "/f/F/cur/p/h-a/inbox";
    let asker_lane = "/f/F/in/p/h-a/>";

    // The asker asks on the answerer's lane; the offset it gets back IS the id.
    let mut asker = Client::connect(&p.sock).unwrap();
    let (r, _) = asker
        .publish(1, 1, "/f/F/in/n1/s1/h-a/ask", b"v=1 text=which%20branch")
        .unwrap();

    // The answerer drains its lane, sees the ask, and answers on the asker's lane.
    let mut sub = group_sub(&p.sock);
    let mut committer = Client::connect(&p.sock).unwrap();
    let got = drain(&mut sub, &mut committer, GROUP, 1).unwrap();
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].0, r);
    let mut answerer = Client::connect(&p.sock).unwrap();
    answerer
        .publish(
            2,
            1,
            "/f/F/in/p/h-a/s1/answer",
            format!("v=1 re={r} text=audit-2").as_bytes(),
        )
        .unwrap();

    // The asker's own drain finds the answer, carrying the ask's offset.
    let asker_sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe_group(asker_group, asker_lane)
        .unwrap();
    asker_sub.set_read_timeout(Some(IDLE)).unwrap();
    let mut asker_sub = asker_sub;
    let mut asker_committer = Client::connect(&p.sock).unwrap();
    let got = drain(&mut asker_sub, &mut asker_committer, asker_group, 1).unwrap();
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].1, "/f/F/in/p/h-a/s1/answer");
    assert_eq!(
        String::from_utf8_lossy(&got[0].2),
        format!("v=1 re={r} text=audit-2")
    );
}

/// COUNTERFACTUAL: the exchange replays with the ask swapped, offline. The
/// substitution is visible in the fork's snapshot; the recorded answer is unchanged
/// (no producer is re-run); and the LIVE log still holds the original ask.
#[test]
fn the_exchange_replays_with_a_swapped_ask_and_the_live_log_is_untouched() {
    let p = fresh("fork");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let (r, _) = c
        .publish(1, 1, "/f/F/in/n1/s1/h-a/ask", b"v=1 text=which%20branch")
        .unwrap();
    c.publish(
        2,
        1,
        "/f/F/in/p/h-a/s1/answer",
        format!("v=1 re={r} text=audit-2").as_bytes(),
    )
    .unwrap();

    let mut fork = Client::connect(&p.sock)
        .unwrap()
        .fork_subscribe(
            r,
            "/f/F/in/n1/s1/h-a/ask",
            b"v=1 text=which%20fixture",
            "/f/F/in/>",
        )
        .unwrap();
    assert_eq!(
        fork.recv().unwrap().unwrap(),
        (
            r,
            "/f/F/in/n1/s1/h-a/ask".to_string(),
            b"v=1 text=which%20fixture".to_vec()
        ),
        "the ask is swapped in the alternate timeline"
    );
    assert_eq!(
        String::from_utf8_lossy(&fork.recv().unwrap().unwrap().2),
        format!("v=1 re={r} text=audit-2"),
        "the RECORDED answer is unchanged: a fork is recorded divergence, not a re-run"
    );
    assert_eq!(fork.recv().unwrap(), None, "a fork ends after its snapshot");

    // The live log is untouched.
    let (page, _) = c.last("/f/F/in/n1/s1/h-a/ask", "", 8).unwrap();
    assert_eq!(
        String::from_utf8_lossy(&page[0].2),
        "v=1 text=which%20branch"
    );
}
