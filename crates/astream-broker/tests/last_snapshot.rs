//! `Last` answers a MULTI-ROUND walk as of ONE head.
//!
//! `last_page` continues a page that the scan bound cut on a non-matching entry, and it
//! drops the log lock between rounds — that release is the point of `LAST_SCAN_MAX`. It
//! used to re-read `shared.head` on every round and report the LAST round's, so rows
//! collected in round 1 went out paired with a head that later rounds had already
//! walked past. A publisher that superseded such a subject in the gap turned the
//! last-value verb into a not-last-value verb, permanently: the cursor had passed the
//! subject, and the reader's paired `Subscribe { from: mark.next }` started ABOVE the
//! superseding record, so nothing ever corrected it.
//!
//! Both tests below occupy the between-rounds window instead of racing for it, through
//! `Broker::on_last_scan_round` — the hook runs on the broker's own connection thread
//! with the log lock released, and the walk does not resume until the publish it makes
//! has been acked. There is no sleep here and no polling: every step blocks on an ack
//! or on the closing `Mark`.
#![cfg(unix)]

use astream_broker::broker::LAST_SCAN_MAX;
use astream_broker::store::{BrokerLog, Durability, MAX_SUBJECTS_PER_PRODUCER};
use astream_broker::{Broker, Client};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr3last_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr3last_{tag}_{pid}_{n}.log"),
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

/// The filter's literal prefix is `/f/F/in/`, and every filler below sits under it
/// without matching it — so the walk is cut by the SCAN bound on a non-matching entry
/// and `last_page` continues, which is the only way to get a second round.
const FILTER: &str = "/f/F/in/*/*/n-1/*";
/// Sorts BEFORE the fillers (`a` < `n`): collected in round 1.
const EARLY: &str = "/f/F/in/a/b/n-1/ask";
/// Sorts AFTER the fillers (`z` > `n`): not reached until round 2.
const LATE: &str = "/f/F/in/z/b/n-1/ask";
const MATCH_PID: u64 = 900_001;

/// One filler per index entry, more than `LAST_SCAN_MAX` of them, then `subject` at its
/// starting value. Returns that record's offset, which is also the number of fillers.
fn build_log(path: &str, subject: &str) -> u64 {
    let n = LAST_SCAN_MAX + 1024;
    let mut log = BrokerLog::open_with(path, Durability::Relaxed).unwrap();
    for i in 0..n {
        // Spread over producers so MAX_SUBJECTS_PER_PRODUCER is not what stops us.
        let pid = (i / (MAX_SUBJECTS_PER_PRODUCER / 2)) as u64 + 1;
        log.publish(
            pid,
            i as u64,
            format!("/f/F/in/n-{i:06}/s-7/h-andrew/ask"),
            b"x".to_vec(),
        )
        .unwrap();
    }
    let (off, _) = log
        .publish(MATCH_PID, 1, subject.to_string(), b"old".to_vec())
        .unwrap();
    off.0
}

/// Install the hook that publishes `subject`'s NEW value in the gap after round 0, and
/// hand back the cell its offset lands in. The publish goes through its own connection
/// and blocks on the ack, so by the time round 1 re-takes the log lock the record is
/// committed and `shared.head` has already moved past it.
fn supersede_between_rounds(b: &Broker, sock: &str, subject: &'static str) -> Arc<AtomicU64> {
    let new_off = Arc::new(AtomicU64::new(u64::MAX));
    let cell = new_off.clone();
    let sock = sock.to_string();
    b.on_last_scan_round(move |round| {
        if round != 0 {
            return;
        }
        let mut w = Client::connect(&sock).expect("second connection for the superseding write");
        let (off, deduped) = w.publish(MATCH_PID, 2, subject, b"new").expect("supersede");
        assert!(!deduped, "the superseding write must be a real record");
        cell.store(off, Ordering::Relaxed);
    });
    new_off
}

/// A ROW FROM AN EARLY ROUND IS NEVER PAIRED WITH A LATER ROUND'S HEAD.
///
/// `EARLY` is collected in round 1. Between the rounds its value is superseded. The
/// answer must not report a head above that superseding record while still carrying the
/// row it replaced — that row would be a stale value sold as the last value, and one
/// the reader's `Subscribe { from: mark.next }` would then skip forever.
#[test]
fn last_never_pairs_an_early_rounds_row_with_a_later_rounds_head() {
    let p = fresh("early");
    let old_off = build_log(&p.log, EARLY);

    let b = Broker::open(&p.log).unwrap();
    let new_off = supersede_between_rounds(&b, &p.sock, EARLY);
    let mut h = b.serve(&p.sock).unwrap();
    let head_at_request = b.visible_head();

    let mut c = Client::connect(&p.sock).unwrap();
    let (page, (next, head), resume) = c.last_page(FILTER, "", 64).unwrap();
    let new_off = new_off.load(Ordering::Relaxed);

    assert_ne!(new_off, u64::MAX, "the between-rounds hook never fired");
    assert_eq!(resume, "", "the walk ran the prefix range out");
    assert_eq!(next, head, "Last's Mark reports one head");
    assert_eq!(
        page.len(),
        1,
        "the one matching subject must still be answered: {page:?}"
    );
    let (off, subject, body) = &page[0];
    assert_eq!(subject, EARLY);

    // THE GUARANTEE: every row is its subject's newest record strictly below the head
    // the answer reports. The row is `EARLY`'s value at `old_off`, so `new_off` — the
    // record that superseded it — must not be below the reported head.
    assert!(
        new_off >= head || *off == new_off,
        "Last returned {subject} at offset {off} ({}) but reported head {head}, and \
         {subject} was superseded at offset {new_off} < {head}: that row is not the \
         last value as of the head it is paired with, and a `Subscribe {{ from: \
         {next} }}` starts above the record that would have corrected it",
        String::from_utf8_lossy(body),
    );
    assert_eq!(
        head, head_at_request,
        "the head is pinned on the first scan round and every later round reads \
         against it; a head that moved means the rounds were spliced, not pinned"
    );
    assert_eq!(*off, old_off);

    drop(c);
    h.shutdown();
}

/// THE PIN'S DELIBERATE COST, AND THAT IT COSTS NOTHING END TO END.
///
/// `LATE` is not reached until round 2. Superseding it in the gap puts its newest
/// offset AT the pinned head, and `last_matching` skips a subject whose newest offset
/// is not below `visible` — so it is OMITTED from the page rather than answered. That
/// is the trade `last_page`'s rustdoc records, and it is fail-closed: the answer's
/// `Mark.next` is the pinned head, so the very record that displaced it is delivered by
/// the read the reader pairs with the snapshot.
///
/// Before the pin this page instead came back holding `LATE` at its NEW value under a
/// head from round 2 — a different answer, from a walk that was never a snapshot.
#[test]
fn a_subject_superseded_past_the_pinned_head_is_omitted_and_arrives_on_the_tail() {
    let p = fresh("late");
    build_log(&p.log, LATE);

    let b = Broker::open(&p.log).unwrap();
    let new_off = supersede_between_rounds(&b, &p.sock, LATE);
    let mut h = b.serve(&p.sock).unwrap();
    let head_at_request = b.visible_head();

    let mut c = Client::connect(&p.sock).unwrap();
    let (page, (next, head), resume) = c.last_page(FILTER, "", 64).unwrap();
    let new_off = new_off.load(Ordering::Relaxed);

    assert_ne!(new_off, u64::MAX, "the between-rounds hook never fired");
    assert_eq!(resume, "", "the walk ran the prefix range out");
    assert!(
        page.is_empty(),
        "a subject whose newest record is at or above the pinned head must be omitted, \
         not answered from a later round's head: the answer reports head {head} and \
         carries {page:?}, read against a head this walk only reached after the write \
         at offset {new_off} landed between its rounds"
    );
    assert_eq!(
        head, head_at_request,
        "the head is pinned on the first scan round, so a write that lands between \
         rounds does not raise the head this answer reports"
    );

    // Nothing was lost: the read that pairs with the snapshot starts at the pinned head
    // and delivers the record that displaced the omitted subject.
    let (tail, _) = c.fetch(next, FILTER, 64).unwrap();
    assert_eq!(
        tail,
        vec![(new_off, LATE.to_string(), b"new".to_vec())],
        "the omitted subject must arrive on the read paired with the snapshot"
    );

    drop(c);
    h.shutdown();
}
