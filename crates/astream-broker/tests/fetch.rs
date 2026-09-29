//! Claim `broker.fetch-bounded` (fabric R2): `Fetch{from, filter, max}` is a
//! BOUNDED, NON-TERMINAL read — at most `max` matching records, scanning at most
//! `FETCH_SCAN_MAX`, closed by a `Mark{next, head}` whose `next` counts SCANNED
//! records so a sparse filter still advances. Every streaming verb the broker had
//! ended the connection; this one does not.
//!
//! The scan cap is exercised by a log LONGER than the cap: a 10 k-record test can
//! never reach 65 536, so it would leave the bound unproven.
#![cfg(unix)]

use astream_broker::broker::FETCH_SCAN_MAX;
use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::store::{BrokerLog, Durability};
use astream_broker::{Broker, BrokerHandle, Client, Request, Response};
use astream_wire::Filter;
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
        sock: format!("/tmp/asfetch_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asfetch_{tag}_{pid}_{n}.log"),
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

/// Seed a log directly (Relaxed: no fsync per record) with `n` records where every
/// `hit_every`-th carries `/z/hit` and the rest `/z/miss`. Writing through the store
/// rather than a socket keeps a 70 000-record fixture a fraction of a second.
fn seed(path: &str, n: u64, hit_every: u64) -> Vec<u64> {
    let mut log = BrokerLog::open_with(path, Durability::Relaxed).unwrap();
    let mut hits = Vec::new();
    for i in 0..n {
        let subject = if i % hit_every == 0 {
            hits.push(i);
            "/z/hit"
        } else {
            "/z/miss"
        };
        log.publish(1, i, subject.to_string(), format!("b{i}").into_bytes())
            .unwrap();
    }
    hits
}

/// The core: a bounded page, a cursor that advances, a `max = 0` head query, and a
/// connection that is still usable afterwards.
#[test]
fn fetch_pages_bounded_and_leaves_the_connection_usable() {
    let p = fresh("basic");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    for i in 0..10u64 {
        c.publish(1, i, "/z/hit", format!("m{i}").as_bytes())
            .unwrap();
    }

    // max = 0 is the head query: no record, and a mark that has not moved.
    let (page, (next, head)) = c.fetch(0, "/z/>", 0).unwrap();
    assert!(page.is_empty());
    assert_eq!((next, head), (0, 10));

    // Paged with max = 3, the whole log arrives exactly once, in order.
    let mut got = Vec::new();
    let mut from = 0u64;
    loop {
        let (page, (next, h)) = c.fetch(from, "/z/>", 3).unwrap();
        assert_eq!(h, 10);
        assert!(page.len() <= 3, "max is honoured");
        got.extend(page.iter().map(|(o, _, _)| *o));
        if next == from {
            break; // cursor cannot advance: the log is exhausted
        }
        from = next;
        if from >= h {
            break;
        }
    }
    assert_eq!(got, (0..10).collect::<Vec<u64>>());

    // NON-TERMINAL: the connection publishes again and fetches the new record.
    assert_eq!(c.publish(1, 10, "/z/hit", b"m10").unwrap(), (10, false));
    let (page, _) = c.fetch(10, "/z/>", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].0, 10);
}

/// THE SCAN CAP, over a log longer than it: the first page scans exactly
/// `FETCH_SCAN_MAX` records, matches only the few hits inside that window, and hands
/// back a cursor at `from + FETCH_SCAN_MAX` — strictly below the head, which is what
/// proves the cap (not `max`) ended the page. Paging on reaches every match exactly
/// once with no gap and no duplicate.
#[test]
fn a_log_longer_than_the_scan_cap_pages_past_it_gapless_and_dup_free() {
    const N: u64 = 70_000;
    const HIT_EVERY: u64 = 10_000;
    let p = fresh("scancap");
    let expected = seed(&p.log, N, HIT_EVERY);
    assert!(
        N > FETCH_SCAN_MAX as u64,
        "the fixture must be longer than the cap, or the cap is never reached"
    );
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();

    let (first, (next, head)) = c.fetch(0, "/z/hit", 64).unwrap();
    assert_eq!(head, N);
    assert_eq!(
        next, FETCH_SCAN_MAX as u64,
        "the page ended at the SCAN cap, not at max and not at the head"
    );
    assert!(next < head, "the cap really did cut the scan short");
    assert!(
        first.len() < 64,
        "far fewer matches than max: the cap, not max, ended it"
    );

    let mut got: Vec<u64> = first.iter().map(|(o, _, _)| *o).collect();
    let mut from = next;
    while from < head {
        let (page, (next, h)) = c.fetch(from, "/z/hit", 64).unwrap();
        assert_eq!(h, head);
        assert!(next > from, "a page that matched nothing still advances");
        got.extend(page.iter().map(|(o, _, _)| *o));
        from = next;
    }
    assert_eq!(got, expected, "every match exactly once, in order");
    assert!(
        got.windows(2).all(|w| w[0] < w[1]),
        "no duplicate and no reorder"
    );
}

/// A 10 000-record log with a 1-in-1 000 filter: repeated paging reaches every match
/// exactly once. (This is the shape the design review flagged as UNABLE to reach the
/// scan cap — kept because it is still the right test for sparse paging, next to the
/// 70 000-record one that does reach it.)
#[test]
fn a_sparse_filter_over_ten_thousand_records_reaches_every_match_once() {
    const N: u64 = 10_000;
    let p = fresh("sparse");
    let expected = seed(&p.log, N, 1_000);
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let mut got = Vec::new();
    let mut from = 0u64;
    let head = c.fetch(0, "/z/hit", 0).unwrap().1 .1;
    assert_eq!(head, N);
    while from < head {
        let (page, (next, _)) = c.fetch(from, "/z/hit", 3).unwrap();
        got.extend(page.iter().map(|(o, _, _)| *o));
        assert!(next > from);
        from = next;
    }
    assert_eq!(got, expected);
}

/// Store-level: with a small `scan_max`, a page whose window holds ZERO matches
/// delivers nothing and still hands back `from + scan_max`. The bound is on WORK.
#[test]
fn a_window_with_no_match_delivers_nothing_and_still_advances() {
    let p = fresh("window");
    seed(&p.log, 200, 1_000); // only offset 0 is a hit
    let log = BrokerLog::open(&p.log).unwrap();
    let head = log.head().0;
    let f = Filter::new("/z/hit").unwrap();

    let (page, next) = log.fetch(1, &f, 64, 64, head);
    assert!(page.is_empty(), "no match inside offsets 1..65");
    assert_eq!(next, 1 + 64, "next = from + scan_max");

    let (page, next) = log.fetch(0, &f, 64, 64, head);
    assert_eq!(page.len(), 1, "the one hit at offset 0");
    assert_eq!(next, 64);

    // max = 0 scans nothing at all.
    assert_eq!(log.fetch(0, &f, 0, 64, head), (Vec::new(), 0));
    // `visible` fails closed: nothing at or above it is ever scanned out.
    assert!(log.fetch(0, &f, 64, 64, 0).0.is_empty());
}

/// A hidden record is never delivered by `Fetch` — and it is still SCANNED, so the
/// cursor accounts for the offset it consumed rather than stalling on it.
#[test]
fn hidden_records_are_scanned_but_never_delivered() {
    let p = fresh("hidden");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    c.publish(1, 1, "/a/x", b"one").unwrap(); // 0
    c.commit("/a/g", 0).unwrap(); // 1 — a real /a/commit record
    c.publish(1, 2, "/a/y", b"two").unwrap(); // 2

    let (page, (next, head)) = c.fetch(0, "/a/>", 64).unwrap();
    assert_eq!(head, 3);
    assert_eq!(next, 3, "all three offsets were scanned");
    assert_eq!(
        page.iter()
            .map(|(o, s, _)| (*o, s.clone()))
            .collect::<Vec<_>>(),
        vec![(0, "/a/x".to_string()), (2, "/a/y".to_string())],
        "the /a/commit record at offset 1 is never delivered"
    );
}

/// Pending pipelined acks are FLUSHED before the page: they arrive first, in order,
/// and none is lost. Asserted at the wire level, because the blocking client API
/// never leaves an ack outstanding.
#[test]
fn pipelined_acks_are_flushed_in_order_before_the_page() {
    let p = fresh("flush");
    let (_b, _h) = serve(&p);
    let mut s = Client::connect(&p.sock).unwrap().into_stream();

    // Three publishes in flight, no ack read yet.
    for i in 1..=3u64 {
        write_frame(
            &mut s,
            &encode_request(&Request::Publish {
                producer_id: 4,
                producer_seq: i,
                subject: "/q/x".to_string(),
                body: format!("p{i}").into_bytes(),
            }),
        )
        .unwrap();
    }
    write_frame(
        &mut s,
        &encode_request(&Request::Fetch {
            from_offset: 0,
            filter: "/q/>".to_string(),
            max: 64,
        }),
    )
    .unwrap();

    let mut resps = Vec::new();
    for _ in 0..7 {
        let payload = read_frame(&mut s).unwrap().expect("a response frame");
        resps.push(decode_response(&payload).expect("a decodable response"));
    }
    let acks: Vec<u64> = resps
        .iter()
        .take(3)
        .map(|r| match r {
            Response::PublishAck { offset, deduped } => {
                assert!(!deduped);
                *offset
            }
            other => panic!("expected the flushed acks first, got {other:?}"),
        })
        .collect();
    assert_eq!(acks, vec![0, 1, 2], "in request order, none lost");
    assert!(matches!(resps[3], Response::Delivery { offset: 0, .. }));
    assert!(matches!(resps[4], Response::Delivery { offset: 1, .. }));
    assert!(matches!(resps[5], Response::Delivery { offset: 2, .. }));
    assert_eq!(
        resps[6],
        Response::Mark {
            next: 3,
            head: 3,
            resume: String::new()
        }
    );

    // ...and the connection is still usable after the page.
    write_frame(
        &mut s,
        &encode_request(&Request::Publish {
            producer_id: 4,
            producer_seq: 4,
            subject: "/q/x".to_string(),
            body: b"p4".to_vec(),
        }),
    )
    .unwrap();
    let payload = read_frame(&mut s).unwrap().unwrap();
    assert_eq!(
        decode_response(&payload),
        Some(Response::PublishAck {
            offset: 3,
            deduped: false
        })
    );
}

/// A bad filter is an ordinary error the connection survives, not a close.
#[test]
fn a_bad_filter_is_refused_without_ending_the_connection() {
    let p = fresh("badfilter");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    c.publish(1, 1, "/z/hit", b"x").unwrap();
    let e = c.fetch(0, "no-leading-slash", 8).unwrap_err();
    assert!(e.to_string().contains("bad filter"), "{e}");
    let (page, _) = c.fetch(0, "/z/>", 8).unwrap();
    assert_eq!(page.len(), 1);
}
