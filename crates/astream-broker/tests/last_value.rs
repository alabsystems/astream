//! Claim `broker.last-value` (fabric R1): `Last{filter, after, max}` is RETAINED
//! STATE as a query over the same log — the most recent record of every matching
//! subject, paged in ascending subject order, closed by a `Mark{next, head}` that
//! pairs the snapshot with the subscriber-visible head so a `Subscribe{from: next}`
//! on the SAME connection tails on gap-free and dup-free.
//!
//! Everything here synchronizes on acks and known delivery counts — no sleeps.
#![cfg(unix)]

use astream_broker::broker::{LAST_PAGE_MAX, LAST_SCAN_MAX};
use astream_broker::proto::{encode_request, write_frame};
use astream_broker::store::{BrokerLog, Durability, MAX_SUBJECTS_PER_PRODUCER};
use astream_broker::{Broker, BrokerHandle, Client, Request};
use astream_wire::Filter;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/aslast_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/aslast_{tag}_{pid}_{n}.log"),
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

/// `(subject, body)` of a page, so an assertion reads like the expectation.
fn shape(page: &[(u64, String, Vec<u8>)]) -> Vec<(String, String)> {
    page.iter()
        .map(|(_, s, b)| (s.clone(), String::from_utf8_lossy(b).into_owned()))
        .collect()
}

/// The heart of R1: `Last` is last-per-subject, subject-ordered, filter-scoped, and
/// its `Mark` is a cursor the SAME connection can subscribe from with no gap and no
/// dup — the retained value is also an offset you can replay to.
#[test]
fn last_is_the_newest_record_per_subject_then_a_mark_the_connection_tails_from() {
    let p = fresh("basic");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    assert_eq!(c.publish(1, 1, "/x/a", b"a0").unwrap(), (0, false));
    assert_eq!(c.publish(1, 2, "/x/b", b"b1").unwrap(), (1, false));
    assert_eq!(c.publish(1, 3, "/x/a", b"a2").unwrap(), (2, false));
    assert_eq!(c.publish(1, 4, "/y/c", b"c3").unwrap(), (3, false)); // outside the filter

    let (page, (next, head)) = c.last("/x/>", "", 64).unwrap();
    assert_eq!(
        shape(&page),
        vec![
            ("/x/a".to_string(), "a2".to_string()),
            ("/x/b".to_string(), "b1".to_string()),
        ],
        "the NEWEST record of each matching subject, in ascending subject order"
    );
    assert_eq!(page[0].0, 2, "/x/a's retained value is its offset-2 record");
    assert_eq!(page[1].0, 1);
    assert_eq!((next, head), (4, 4), "the snapshot is paired with the head");

    // The connection is still usable: publish, then tail from the mark on the SAME
    // connection — no gap (D arrives) and no dup (nothing from the snapshot repeats).
    assert_eq!(c.publish(1, 5, "/x/d", b"d4").unwrap(), (4, false));
    let mut sub = c.subscribe(next, "/x/>").unwrap();
    assert_eq!(
        sub.recv().unwrap(),
        Some((4, "/x/d".to_string(), b"d4".to_vec()))
    );
}

/// Paging: `max` bounds one query, `after` resumes it, and the union of the pages is
/// exactly the single-page snapshot.
#[test]
fn paging_by_max_and_after_reassembles_the_single_page_snapshot() {
    let p = fresh("page");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    for i in 0..8u64 {
        // Two records per subject, so each page entry must be the SECOND one.
        c.publish(1, 2 * i + 1, &format!("/s/{i}"), b"old").unwrap();
        c.publish(
            1,
            2 * i + 2,
            &format!("/s/{i}"),
            format!("new{i}").as_bytes(),
        )
        .unwrap();
    }
    let (whole, (_, head)) = c.last("/s/*", "", 64).unwrap();
    assert_eq!(whole.len(), 8);
    assert!(
        whole.windows(2).all(|w| w[0].1 < w[1].1),
        "ascending subject order"
    );
    assert!(
        whole.iter().all(|(_, s, b)| {
            let i = s.rsplit('/').next().unwrap();
            b == format!("new{i}").as_bytes()
        }),
        "every entry is that subject's newest record"
    );

    let mut paged = Vec::new();
    let mut after = String::new();
    loop {
        let (page, (_, h)) = c.last("/s/*", &after, 1).unwrap();
        assert_eq!(h, head, "each page is read at the same head");
        assert!(page.len() <= 1, "max = 1 is honoured");
        match page.first() {
            None => break,
            Some((_, s, _)) => {
                after = s.clone();
                paged.extend(page);
            }
        }
    }
    assert_eq!(
        shape(&paged),
        shape(&whole),
        "the pages reassemble the whole"
    );
}

/// Late-joiner equivalence: the snapshot equals the last-per-subject of a from-0
/// replay taken at the same head — the property that makes `Last` a *query over the
/// log* rather than a second source of truth.
#[test]
fn the_snapshot_equals_the_last_per_subject_of_a_from_zero_replay() {
    const ROUNDS: u64 = 3;
    let p = fresh("equiv");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let subjects = ["/f/F/pub/n1/s1/presence", "/f/F/pub/n1/s2/presence"];
    let mut seq = 0u64;
    for round in 0..ROUNDS {
        for s in subjects {
            seq += 1;
            c.publish(7, seq, s, format!("r{round}").as_bytes())
                .unwrap();
        }
    }
    let (page, (_, head)) = c.last("/f/F/pub/*/*/presence", "", 64).unwrap();
    assert_eq!(head, seq, "every publish is visible");

    // Fold a from-0 replay of exactly those records to last-per-subject. The count is
    // known, so the reader never parks on the live tail (no sleep, no timeout).
    let mut replay = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/f/>")
        .unwrap();
    let mut folded: std::collections::BTreeMap<String, Vec<u8>> = std::collections::BTreeMap::new();
    for _ in 0..(ROUNDS as usize * subjects.len()) {
        let (_, subject, body) = replay.recv().unwrap().expect("a delivery");
        folded.insert(subject, body);
    }
    let expected: Vec<(String, String)> = folded
        .iter()
        .map(|(s, b)| (s.clone(), String::from_utf8_lossy(b).into_owned()))
        .collect();
    assert_eq!(shape(&page), expected);
}

/// The `last` index is REBUILT on open from the stored bytes alone: the snapshot a
/// reopened broker answers is identical to the one the first broker answered.
#[test]
fn the_index_is_rebuilt_on_open_and_the_snapshot_is_identical() {
    let p = fresh("reopen");
    let sock2 = format!("{}.2", p.sock);
    let before = {
        let b = Broker::open(&p.log).unwrap();
        let mut h = b.serve(&p.sock).unwrap();
        let mut c = Client::connect(&p.sock).unwrap();
        for i in 0..5u64 {
            c.publish(3, 2 * i + 1, &format!("/k/{i}"), b"first")
                .unwrap();
            c.publish(
                3,
                2 * i + 2,
                &format!("/k/{i}"),
                format!("last{i}").as_bytes(),
            )
            .unwrap();
        }
        let (page, mark) = c.last("/k/>", "", 64).unwrap();
        drop(c);
        h.shutdown();
        (page, mark)
    };
    let b2 = Broker::open(&p.log).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut c = Client::connect(&sock2).unwrap();
    let (page, mark) = c.last("/k/>", "", 64).unwrap();
    // The WHOLE page, offsets included — the third field of every `Delivery` frame,
    // and the cursor a client replays from. Comparing subject+body alone would pass on
    // a rebuild that pointed each subject at an older record carrying the same bytes.
    assert_eq!((page, mark), before, "index rebuilt from the log");
}

/// The hidden subjects are excluded from the index and from delivery. A wildcard
/// `Last` over `/a/>` sees no `/a/commit` record (the leak class the audit found:
/// commit records reaching a wildcard subscriber), and a client cannot create one.
#[test]
fn hidden_subjects_are_neither_indexed_nor_delivered_nor_publishable() {
    let p = fresh("hidden");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    c.publish(1, 1, "/a/data", b"visible").unwrap();
    // A real commit record on the reserved subject, at a real offset.
    let commit_off = c.commit("/a/group", 0).unwrap();
    assert_eq!(commit_off, 1, "the commit record consumed an offset");
    c.publish(1, 2, "/a/more", b"visible2").unwrap();

    let (page, (_, head)) = c.last("/a/>", "", 64).unwrap();
    assert_eq!(head, 3);
    assert_eq!(
        shape(&page),
        vec![
            ("/a/data".to_string(), "visible".to_string()),
            ("/a/more".to_string(), "visible2".to_string()),
        ],
        "no /a/commit in a wildcard last-value page"
    );
    // A wildcard SUBSCRIBE agrees (the same skip on the delivery path).
    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/a/>")
        .unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().1, "/a/data");
    assert_eq!(sub.recv().unwrap().unwrap().1, "/a/more");

    // Every hidden subject is refused to a client publish BY NAME, with nothing
    // appended and the idempotency key left unconsumed.
    for hidden in ["/a/commit", "/a/will", "/a/bind"] {
        let e = c.publish(1, 3, hidden, b"forged").unwrap_err();
        assert!(e.to_string().contains("reserved subject"), "{hidden}: {e}");
    }
    assert_eq!(
        c.publish(1, 3, "/a/after", b"ok").unwrap(),
        (3, false),
        "the refused publishes appended nothing and burned no key"
    );
}

/// The per-producer distinct-subject bound: the index cannot be grown without limit
/// by one producer. Exercised on the store (4096 socket round trips would be a
/// needlessly slow way to assert an arithmetic bound), with the WIRE path asserting
/// the refusal reaches the client as an error.
#[test]
fn a_producer_cannot_grow_the_index_past_the_distinct_subject_bound() {
    let p = fresh("bound");
    // Relaxed for the SETUP only: 4096 records, one fsync each, would spend the whole
    // test on the disk to assert an arithmetic bound. The bytes are identical.
    let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
    for i in 0..MAX_SUBJECTS_PER_PRODUCER {
        log.publish(9, i as u64, format!("/b/{i}"), b"x".to_vec())
            .unwrap();
    }
    assert_eq!(log.subjects_per_producer(9), MAX_SUBJECTS_PER_PRODUCER);
    // A repeat of an EXISTING subject is fine — the bound counts distinct subjects.
    log.publish(9, u64::MAX, "/b/0".to_string(), b"again".to_vec())
        .unwrap();
    // A DIFFERENT producer is unaffected: the bound is per producer.
    log.publish(10, 1, "/b/other".to_string(), b"x".to_vec())
        .unwrap();
    drop(log);

    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let e = c
        .publish(9, u64::MAX - 1, "/b/one-too-many", b"x")
        .unwrap_err();
    assert!(
        e.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"),
        "the 4097th distinct subject under one producer is refused: {e}"
    );
    let (_, (_, head)) = c.last("/b/>", "", 1).unwrap();
    assert_eq!(
        head,
        MAX_SUBJECTS_PER_PRODUCER as u64 + 2,
        "nothing was appended by the refusal"
    );
}

/// `Last` is consistent under PIPELINING: while another connection holds a staged,
/// unpromoted window of publishes, every answer pairs its page with a `head` no record
/// in that page reaches (`next == head`, every page offset `< head`) — the test never
/// learns the first staged offset, so it asserts THAT, not a head-vs-staged-offset
/// bound — and the staged batch is then delivered EXACTLY once from `Mark.next`.
#[test]
fn a_snapshot_never_shows_a_record_at_or_above_the_head_it_reports() {
    let p = fresh("pipe");
    let (_b, _h) = serve(&p);
    let mut seed = Client::connect(&p.sock).unwrap();
    seed.publish(1, 1, "/p/base", b"base").unwrap();

    // A pipelining writer: 512 publishes in flight, its acks drained afterwards.
    const N: usize = 512;
    let sock = p.sock.clone();
    let (started_tx, started_rx) = mpsc::channel::<()>();
    let writer = std::thread::spawn(move || {
        let mut w = Client::connect(&sock).unwrap();
        let bodies: Vec<Vec<u8>> = (0..N).map(|i| format!("w{i}").into_bytes()).collect();
        let refs: Vec<&[u8]> = bodies.iter().map(|b| b.as_slice()).collect();
        started_tx.send(()).unwrap();
        w.publish_pipelined(2, "/p/burst", &refs, 256).unwrap()
    });
    started_rx.recv().unwrap();

    // Snapshot repeatedly while the burst lands; every answer must be self-consistent.
    let mut reader = Client::connect(&p.sock).unwrap();
    for _ in 0..64 {
        let (page, (next, head)) = reader.last("/p/>", "", 64).unwrap();
        assert_eq!(next, head);
        assert!(
            page.iter().all(|(off, _, _)| *off < head),
            "no snapshot record at or above the head it was paired with"
        );
    }
    let acks = writer.join().unwrap();
    assert_eq!(acks.len(), N);

    // From a snapshot's mark, the whole burst is delivered exactly once.
    let (page, (next, head)) = reader.last("/p/base", "", 64).unwrap();
    assert_eq!(
        shape(&page),
        vec![("/p/base".to_string(), "base".to_string())]
    );
    assert_eq!(head, N as u64 + 1, "the whole burst is promoted now");
    // A from-0 replay yields each record exactly once, dense and ordered, and ends
    // exactly one below the mark the snapshot handed out.
    let mut from_zero = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/p/>")
        .unwrap();
    let mut seen = Vec::new();
    for _ in 0..(N + 1) {
        seen.push(from_zero.recv().unwrap().unwrap().0);
    }
    assert_eq!(seen.len(), N + 1);
    assert!(
        seen.windows(2).all(|w| w[0] + 1 == w[1]),
        "dense and ordered"
    );
    assert_eq!(
        *seen.last().unwrap(),
        next - 1,
        "the mark is one past the last"
    );
}

/// FAN-OUT: N live subscribers on one filter each receive every record exactly once.
/// The broker absorbs the observers — `broker.exactly-once-pubsub-resume` never runs
/// more than one live matching subscriber, so this is the assertion that closes it.
#[test]
fn sixteen_concurrent_subscribers_each_receive_every_record_exactly_once() {
    const SUBS: usize = 16;
    const RECORDS: usize = 1000;
    let p = fresh("fanout");
    let (_b, _h) = serve(&p);

    let (ready_tx, ready_rx) = mpsc::channel::<()>();
    let mut readers = Vec::new();
    for _ in 0..SUBS {
        let sock = p.sock.clone();
        let ready = ready_tx.clone();
        readers.push(std::thread::spawn(move || {
            let mut sub = Client::connect(&sock)
                .unwrap()
                .subscribe(0, "/fan/>")
                .unwrap();
            ready.send(()).unwrap();
            let mut offs = Vec::with_capacity(RECORDS);
            while offs.len() < RECORDS {
                match sub.recv().unwrap() {
                    Some((off, _, _)) => offs.push(off),
                    None => break,
                }
            }
            offs
        }));
    }
    for _ in 0..SUBS {
        ready_rx.recv().unwrap();
    }

    let mut w = Client::connect(&p.sock).unwrap();
    let bodies: Vec<Vec<u8>> = (0..RECORDS).map(|i| format!("m{i}").into_bytes()).collect();
    let refs: Vec<&[u8]> = bodies.iter().map(|b| b.as_slice()).collect();
    let acks = w.publish_pipelined(5, "/fan/x", &refs, 256).unwrap();
    let expected: Vec<u64> = acks.iter().map(|(o, _)| *o).collect();

    for r in readers {
        let offs = r.join().unwrap();
        assert_eq!(
            offs, expected,
            "every subscriber saw every record, once, in order"
        );
    }
}

/// The store-level query is a range scan bounded by the filter's literal prefix, so
/// a query over one subtree never walks another — asserted through the observable
/// consequence: a filter's page contains exactly its own subtree.
#[test]
fn a_query_is_scoped_to_its_filters_literal_prefix() {
    let p = fresh("prefix");
    let mut log = BrokerLog::open(&p.log).unwrap();
    for (i, s) in [
        "/f/F/pub/n1/s1/presence",
        "/f/F/pub/n1/s1/ev",
        "/f/F/in/n1/s1/h/ask",
    ]
    .iter()
    .enumerate()
    {
        log.publish(1, i as u64, (*s).to_string(), b"x".to_vec())
            .unwrap();
    }
    let head = log.head().0;
    let f = Filter::new("/f/F/pub/*/*/presence").unwrap();
    let (page, resume) = log.last_matching(&f, "", 64, LAST_SCAN_MAX, head);
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].subject, "/f/F/pub/n1/s1/presence");
    assert_eq!(resume, None, "the prefix range ran out: nothing to resume");
    // `max = 0` yields nothing (the head query on the wire), and no cursor.
    assert_eq!(
        log.last_matching(&Filter::new("/f/>").unwrap(), "", 0, LAST_SCAN_MAX, head),
        (Vec::new(), None)
    );
    // `visible` fails CLOSED: a record at or above it is omitted, never exposed.
    assert!(log
        .last_matching(&Filter::new("/f/>").unwrap(), "", 64, LAST_SCAN_MAX, 0)
        .0
        .is_empty());
}

/// PAGING TERMINATES FOR A WILDCARD-FREE FILTER. `literal_prefix` returns the filter
/// itself when it has no `*` or `>`, and that string is the ONLY subject such a filter
/// can match — so a resume cursor equal to it must EXCLUDE it. The lower bound was
/// computed with a strict `>`, which `after == prefix` fails, so the range restarted at
/// `Included(prefix)` and the same row came back forever: `--after <subject>` printed
/// the very row it was told to skip, and a page-until-empty loop never ended.
#[test]
fn paging_a_wildcard_free_filter_terminates() {
    let p = fresh("literal");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    const S1: &str = "/f/F/pub/n1/s1/presence";
    c.publish(1, 1, S1, b"v1").unwrap();
    c.publish(1, 2, "/f/F/pub/n1/s2/presence", b"v2").unwrap();

    let (page, _) = c.last(S1, "", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].1, S1);
    // The page the cursor was explicitly told to skip past is EMPTY.
    let (page2, _) = c.last(S1, S1, 8).unwrap();
    assert!(
        page2.is_empty(),
        "\"strictly after `after`\" is the contract: {page2:?}"
    );
    // And the generic page-until-empty loop terminates, on the store's own face too.
    let log_after = c.last(S1, S1, 1).unwrap().0;
    assert!(log_after.is_empty());
}

/// ONE `Last` IS BOUNDED IN WORK, and says where to resume. The scan of the ordered
/// subject index is cut off after `scan_max` entries VISITED, matched or not — the
/// bound `Fetch` has always had, on the verb that lacked it — and the cursor is the
/// last subject visited, so a page that matched NOTHING still advances. Without both,
/// the §5.4 barrier query (`/f/F/pub/*/*/ack/<B>`, sparse inside a `/f/F/pub/` prefix
/// holding one ack subject per member per barrier ever issued) walks the whole index
/// with the log lock held.
#[test]
fn one_last_visits_a_bounded_number_of_index_entries_and_resumes_where_it_stopped() {
    let p = fresh("scanbound");
    let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
    // 200 presence rows and, buried at the END of the subject order, 3 acks for the
    // barrier we ask about. `/f/F/pub/` is the literal prefix of both.
    for i in 0..200u64 {
        log.publish(1, i, format!("/f/F/pub/n{i:03}/s/presence"), b"up".to_vec())
            .unwrap();
    }
    for i in 0..3u64 {
        log.publish(2, i, format!("/f/F/pub/z{i}/s/ack/b7"), b"ok".to_vec())
            .unwrap();
    }
    let head = log.head().0;
    let f = Filter::new("/f/F/pub/*/*/ack/b7").unwrap();

    // UNBOUNDED-ENOUGH: the whole answer in one page, and no cursor — the range ended.
    let (all, resume) = log.last_matching(&f, "", 64, LAST_SCAN_MAX, head);
    assert_eq!(all.len(), 3);
    assert_eq!(resume, None);

    // BOUNDED: 32 entries per request. Every early page matches NOTHING, and each still
    // hands back a cursor — the last subject visited — so paging makes progress.
    let mut after = String::new();
    let mut got = Vec::new();
    let mut requests = 0usize;
    loop {
        let (page, resume) = log.last_matching(&f, &after, 64, 32, head);
        requests += 1;
        assert!(requests < 64, "the cursor never advanced");
        got.extend(page.iter().map(|r| r.subject.clone()));
        match resume {
            None => break,
            Some(next) => {
                assert!(
                    next > after || after.is_empty(),
                    "the cursor went backwards"
                );
                after = next;
            }
        }
    }
    assert!(requests > 3, "the scan bound was never reached: {requests}");
    assert_eq!(
        got,
        vec![
            "/f/F/pub/z0/s/ack/b7",
            "/f/F/pub/z1/s/ack/b7",
            "/f/F/pub/z2/s/ack/b7"
        ],
        "the bounded pages reassemble the whole answer, once each"
    );
}

/// The BROKER owns both bounds, not the client: `max` is clamped to LAST_PAGE_MAX, so
/// one request can never ask it to clone and frame every subject it has ever seen.
#[test]
fn the_broker_clamps_the_pages_size() {
    let p = fresh("clamp");
    let n = LAST_PAGE_MAX as u64 + 20;
    {
        // Relaxed for the setup only: this asserts a clamp, not a durability tier.
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        // Spread over producers: MAX_SUBJECTS_PER_PRODUCER is per producer, and this
        // test is about the PAGE's clamp, not that one.
        for i in 0..n {
            log.publish(i % 4, i, format!("/c/{i:05}"), b"x".to_vec())
                .unwrap();
        }
    }
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let (page, _, resume) = c.last_page("/c/*", "", u32::MAX).unwrap();
    assert_eq!(page.len(), LAST_PAGE_MAX as usize, "max was not clamped");
    assert!(
        !resume.is_empty(),
        "a clamped page must say where to resume"
    );
    let (rest, _, done) = c.last_page("/c/*", &resume, u32::MAX).unwrap();
    assert_eq!(rest.len() as u64, n - u64::from(LAST_PAGE_MAX));
    assert!(done.is_empty(), "the second page is the last one");
}

/// The distinct-subject bound is the STORE's, not the wire path's. It lived only in
/// the staged (group-commit) path, so `BrokerLog::publish` — the public, un-batched
/// entry point, and the one an embedder of the re-exported type calls — grew the
/// last-value index and the per-producer count past the cap without ever consulting it.
#[test]
fn the_distinct_subject_bound_holds_on_the_un_batched_store_path_too() {
    let p = fresh("boundstore");
    let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
    for i in 0..MAX_SUBJECTS_PER_PRODUCER {
        log.publish(9, i as u64, format!("/u/{i}"), b"x".to_vec())
            .unwrap();
    }
    let head = log.head().0;
    let e = log
        .publish(9, u64::MAX, "/u/one-too-many".to_string(), b"x".to_vec())
        .unwrap_err();
    assert!(e.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"), "{e}");
    // The read-process-write entry point takes the same bound.
    let e = log
        .process_and_produce(
            9,
            u64::MAX - 1,
            "/u/one-too-many".to_string(),
            b"x".to_vec(),
            "/g".to_string(),
            0,
        )
        .unwrap_err();
    assert!(e.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"), "{e}");
    assert_eq!(log.head().0, head, "a refusal appends nothing");
    assert_eq!(log.subjects_per_producer(9), MAX_SUBJECTS_PER_PRODUCER);
    // A repeat of an existing subject, and another producer, are both unaffected.
    log.publish(9, u64::MAX - 2, "/u/0".to_string(), b"again".to_vec())
        .unwrap();
    log.publish(10, 1, "/u/other".to_string(), b"x".to_vec())
        .unwrap();
}

/// A PEER THAT STOPS READING DOES NOT KEEP ITS CONNECTION SLOT. `serve_conn` bounded
/// only the FIRST-FRAME read; every response write was an unbounded blocking
/// `write_all`. The pipelined ack path has had a write bound since it was written, on a
/// `try_clone` of the same socket — but a connection that only ever READS (`Hello`,
/// `Attach`, `Last`, `Fetch`: the fabric observer, `asb last`, `asb fetch`) never starts
/// a `Pipeline`, so it never inherited one. Such a peer, SIGSTOPped or partitioned so
/// its receive window shuts and never reopens, parked the broker thread inside the
/// write for good, with its fd and its MAX_CONNS slot still charged to it — the exact
/// exhaustion MAX_CONNS documents itself as preventing.
#[test]
fn a_peer_that_stops_reading_does_not_hold_its_connection_slot_forever() {
    use std::io::Write;
    let p = fresh("wedge");
    // Enough bytes that no socket buffer can absorb the page: the broker's write must
    // actually block on a peer that never reads.
    {
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        let body = vec![b'x'; 8192];
        for i in 0..2000u64 {
            log.publish(i % 4, i, format!("/w/{i:05}"), body.clone())
                .unwrap();
        }
    }
    let b = Broker::open(&p.log).unwrap();
    b.set_write_timeout(std::time::Duration::from_millis(150));
    b.set_max_conns(1);
    let _h = b.serve(&p.sock).unwrap();

    // One connection asks for a big page and then never reads a byte of it.
    let mut wedged = Client::connect(&p.sock).unwrap().into_stream();
    write_frame(
        &mut wedged,
        &encode_request(&Request::Fetch {
            from_offset: 0,
            filter: "/w/>".to_string(),
            max: u32::MAX,
        }),
    )
    .unwrap();
    wedged.flush().unwrap();

    // The one slot must come back: poll until a second connection is served, or give up.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    let mut served = false;
    while std::time::Instant::now() < deadline {
        if let Ok(mut c) = Client::connect(&p.sock) {
            if c.last("/w/>", "", 1).is_ok() {
                served = true;
                break;
            }
        }
        std::thread::sleep(std::time::Duration::from_millis(25));
    }
    assert!(
        served,
        "the wedged reader kept the only connection slot: every later connection is \
         refused `too many connections` until shutdown"
    );
    drop(wedged);
}
