//! Claim `broker.barrier-count-by-last` (fabric R7): an ACKNOWLEDGED BROADCAST is
//! built out of the primitives that already exist — a publish, a producer-deduped
//! reply, and one `Last` query — not out of a new verb.
//!
//! The issuer publishes a barrier and gets offset `B` in its `PublishAck`. A member's
//! answer is an ordinary record on `/f/<F>/pub/<owner>/ack/<B>`. The count is one
//! query, `Last{/f/<F>/pub/*/*/ack/<B>}`, over the same log, discarding any row whose
//! own offset is below `B` (it cannot be an answer to a question that did not exist
//! yet). "Who is missing" is the presence roster minus the acked set.
//!
//! What this is NOT: a distributed barrier primitive. Nothing in the broker blocks,
//! waits or counts — the count is entirely the issuer's, computed from a page it
//! reads whenever it likes, and a member that never acks is simply absent from that
//! page. There is no timeout here and no liveness inference; see the claim text.
//!
//! Everything here synchronizes on acks and known offsets — no sleeps.
#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, Client};
use std::collections::BTreeSet;
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
        sock: format!("/tmp/asbarrier_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asbarrier_{tag}_{pid}_{n}.log"),
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

/// One fleet member: an aterm session, addressed `<node>/<sid>` under `/f/F/pub/`,
/// publishing under its own producer id (§3.2 — the broker derives that id from the
/// principal in the member's grant; this test runs the unguarded broker, so the ids
/// are simply distinct, one per member).
struct Member {
    owner: String,
    producer_id: u64,
    client: Client,
}

impl Member {
    fn new(sock: &str, node: &str, sid: &str, producer_id: u64) -> Member {
        Member {
            owner: format!("{node}/{sid}"),
            producer_id,
            client: Client::connect(sock).unwrap(),
        }
    }

    fn presence(&mut self, seq: u64) -> u64 {
        let subject = format!("/f/F/pub/{}/presence", self.owner);
        let (off, dup) = self
            .client
            .publish(self.producer_id, seq, &subject, b"state=live")
            .unwrap();
        assert!(!dup, "a fresh presence row is not a retry");
        off
    }

    /// Answer the barrier at `b`. Returns `(offset, deduped)` exactly as the broker
    /// reported it, so a caller can assert on a retry.
    fn ack(&mut self, seq: u64, b: u64, body: &[u8]) -> (u64, bool) {
        let subject = format!("/f/F/pub/{}/ack/{b}", self.owner);
        self.client
            .publish(self.producer_id, seq, &subject, body)
            .unwrap()
    }
}

/// The owner segment of an `ack`/`presence` subject: `/f/F/pub/<node>/<sid>/…` →
/// `<node>/<sid>`. A count of members is a count of DISTINCT owners, and the owner
/// is the address — nothing in the body is trusted for identity (§3.3).
fn owner_of(subject: &str) -> String {
    let seg: Vec<&str> = subject.split('/').collect();
    format!("{}/{}", seg[4], seg[5])
}

/// THE COUNT (§5.4), in full: the acked set is the distinct owners of the `Last` page
/// over the barrier's ack subtree, MINUS any row whose own offset is below `b`.
fn acked_owners(page: &[(u64, String, Vec<u8>)], b: u64) -> BTreeSet<String> {
    page.iter()
        .filter(|(off, _, _)| *off >= b)
        .map(|(_, subject, _)| owner_of(subject))
        .collect()
}

fn owners(page: &[(u64, String, Vec<u8>)]) -> BTreeSet<String> {
    page.iter()
        .map(|(_, subject, _)| owner_of(subject))
        .collect()
}

/// The whole rung in one scenario: five members are present, four answer the barrier
/// at `B` (one of them twice under the same producer key, one of them `refused`), a
/// fifth pre-published an `ack/<B>` BEFORE `B` existed, and the count is four.
#[test]
fn last_over_the_ack_subtree_counts_the_distinct_members_that_answered_this_barrier() {
    let p = fresh("count");
    let (_b, _h) = serve(&p);

    let mut m: Vec<Member> = vec![
        Member::new(&p.sock, "n-a1", "s-01", 11),
        Member::new(&p.sock, "n-a1", "s-02", 12),
        Member::new(&p.sock, "n-b2", "s-03", 13),
        Member::new(&p.sock, "n-b2", "s-04", 14),
        Member::new(&p.sock, "n-c3", "s-05", 15),
    ];

    // The roster: one presence row per member, offsets 0..=4.
    for (i, mem) in m.iter_mut().enumerate() {
        assert_eq!(mem.presence(1), i as u64);
    }

    // THE STALE ACK. The barrier will land at offset 6; member 5 publishes an
    // `ack/6` at offset 5 — before the question exists. It is a well-formed record
    // on exactly the subject the count queries, so only its OFFSET distinguishes it.
    const B: u64 = 6;
    assert_eq!(m[4].ack(2, B, b"ready").0, 5, "the stale ack precedes B");

    // The barrier itself: a human writes under its own fleet subtree (§3.3), and the
    // `PublishAck` offset IS the barrier's name.
    let mut issuer = Client::connect(&p.sock).unwrap();
    let (b, dup) = issuer
        .publish(90, 1, "/f/F/fleet/h-andrew/barrier", b"drain and report")
        .unwrap();
    assert!(!dup);
    assert_eq!(b, B, "the barrier's offset is the one the acks name");

    // Four members answer. Member 3 answers `refused` — a decision, and an ANSWER.
    assert_eq!(m[0].ack(2, B, b"ready").0, 7);
    assert_eq!(m[1].ack(2, B, b"ready").0, 8);
    assert_eq!(m[2].ack(2, B, b"refused").0, 9);
    let (four, dup) = m[3].ack(2, B, b"ready");
    assert_eq!((four, dup), (10, false));

    // THE RETRY. Member 4 re-sends its ack under the SAME producer key — the shape a
    // reconnecting bridge produces. Ingest dedup collapses it to the original offset
    // and appends nothing, so it cannot double-count even before the query runs.
    let head_before = issuer.fetch(0, "/f/>", 0).unwrap().1 .1;
    assert_eq!(
        m[3].ack(2, B, b"ready"),
        (four, true),
        "a retried ack lands once, at its original offset"
    );
    let head_after = issuer.fetch(0, "/f/>", 0).unwrap().1 .1;
    assert_eq!(head_before, head_after, "the retry appended no record");

    // A different barrier's ack is a different subject, so the query cannot see it.
    m[0].ack(3, 99, b"ready");

    // THE COUNT — one query.
    let filter = format!("/f/F/pub/*/*/ack/{B}");
    let (page, mark) = issuer.last(&filter, "", 64).unwrap();
    assert!(mark.1 >= mark.0, "the page is paired with a visible head");

    // The raw page holds FIVE rows: the four answers and the stale one. Discarding
    // the row below B — and only that — leaves the four members that answered.
    assert_eq!(page.len(), 5, "one row per subject in the ack subtree");
    let expected: BTreeSet<String> = ["n-a1/s-01", "n-a1/s-02", "n-b2/s-03", "n-b2/s-04"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(acked_owners(&page, B), expected, "four distinct members");
    assert_eq!(acked_owners(&page, B).len(), 4);
    assert_ne!(
        owners(&page),
        expected,
        "without the offset test the stale ack would be counted"
    );

    // A `refused` is an answer: member 3 is in the counted set, with its decision.
    let refused: Vec<&(u64, String, Vec<u8>)> =
        page.iter().filter(|(_, _, b)| b == b"refused").collect();
    assert_eq!(refused.len(), 1);
    assert_eq!(owner_of(&refused[0].1), "n-b2/s-03");
    assert!(acked_owners(&page, B).contains("n-b2/s-03"));

    // WHO IS MISSING is the roster minus the acked set — the fifth member, whose only
    // record on this subtree is the stale one. Nothing timed out to discover this.
    let (roster, _) = issuer.last("/f/F/pub/*/*/presence", "", 64).unwrap();
    let missing: BTreeSet<String> = owners(&roster)
        .difference(&acked_owners(&page, B))
        .cloned()
        .collect();
    assert_eq!(owners(&roster).len(), 5, "five members are present");
    assert_eq!(
        missing,
        ["n-c3/s-05".to_string()].into_iter().collect(),
        "presence minus acked"
    );
}

/// NOTHING BLOCKS. The count is a query over whatever has landed: run it before any
/// member answers and it is empty; the broker never waited, and the issuer's
/// connection is fully usable in between. A member that answers late is counted by
/// the next query and by no other mechanism.
#[test]
fn the_count_is_a_query_over_the_log_at_the_moment_it_runs_and_never_blocks() {
    let p = fresh("nonblocking");
    let (_b, _h) = serve(&p);
    let mut issuer = Client::connect(&p.sock).unwrap();
    let (b, _) = issuer
        .publish(90, 1, "/f/F/fleet/h-andrew/barrier", b"report")
        .unwrap();
    let filter = format!("/f/F/pub/*/*/ack/{b}");

    // Query one: no member has answered. The answer is "none", immediately — not a
    // wait, not an error, not a timeout.
    let (page, mark) = issuer.last(&filter, "", 64).unwrap();
    assert!(page.is_empty());
    assert_eq!(acked_owners(&page, b).len(), 0);
    let head_after_empty_query = mark.1;

    // The issuer's connection survives the query (the read verbs are non-terminal),
    // and one member answers afterwards.
    let mut m = Member::new(&p.sock, "n-a1", "s-01", 11);
    m.presence(1);
    m.ack(2, b, b"ready");

    // Query two, same connection, same filter: now one. The count moved because a
    // record landed, not because anything was signalled.
    let (page, mark) = issuer.last(&filter, "", 64).unwrap();
    assert_eq!(acked_owners(&page, b).len(), 1);
    assert!(
        mark.1 > head_after_empty_query,
        "the log advanced between the two counts"
    );

    // And the connection still publishes: the barrier cost the issuer no verb, no
    // subscription and no held connection state.
    let (_, dup) = issuer
        .publish(90, 2, "/f/F/fleet/h-andrew/notice", b"4/5")
        .unwrap();
    assert!(!dup);
}
