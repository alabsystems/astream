//! Claim `broker.last-walk`: `Client::last_walk` and `Client::last_all` are the ONE
//! loop that knows how a `Last` answer ends — page on the resume cursor until it comes
//! back empty, keep the FIRST page's mark, stop where the caller says and say where to
//! go on from, and turn a walk that does not end into an error rather than a short list.
//!
//! Two kinds of peer. A REAL in-process broker answers everything a real broker can be
//! made to do cheaply: a face larger than one page, a head that moves between pages, a
//! stop, a row bound, an `on_row` error. A SCRIPTED peer on the far end of a socket pair
//! answers what a real broker cannot be made to do without a fixture of millions of
//! subjects: empty pages with a live cursor, a cursor that never runs out, rows it was
//! not asked for. The scripted peer speaks the real frame codec, so the client under
//! test is the real one either way.
//!
//! Everything synchronizes on acks, closing `Mark`s, and the peer thread's join — no
//! sleeps.
#![cfg(unix)]

use astream_broker::broker::LAST_PAGE_MAX;
use astream_broker::proto::{
    decode_request, encode_delivery, encode_response, read_frame, write_frame,
};
use astream_broker::store::{BrokerLog, Durability, MAX_SUBJECTS_PER_PRODUCER};
use astream_broker::{
    Broker, BrokerHandle, Client, Record, Request, Response, Walk, LAST_WALK_PAGES_MAX,
};
use std::io;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/aslastwalk_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/aslastwalk_{tag}_{pid}_{n}.log"),
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

/// The filter every real-broker test walks.
const FACE: &str = "/f/F/pub/>";

/// Zero-padded, so ascending SUBJECT order is the numeric order and row `i` of a walk
/// is subject `i`.
fn subject(i: usize) -> String {
    format!("/f/F/pub/n-{i:06}/ev")
}

/// More subjects than one `Last` page may carry: `n` of them under [`FACE`], subject `i`
/// at offset `i` with body `v<i>`, then one record outside it. Written straight to the
/// log (Relaxed: this is about paging, and thousands of strict fsyncs are minutes), then
/// served by a broker opened on that log.
fn serve_face(tag: &str, n: usize) -> (Paths, Broker, BrokerHandle) {
    let p = fresh(tag);
    {
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        for i in 0..n {
            // Spread over producers so MAX_SUBJECTS_PER_PRODUCER is not what stops us.
            let pid = (i / (MAX_SUBJECTS_PER_PRODUCER / 2)) as u64 + 1;
            log.publish(pid, i as u64 + 1, subject(i), format!("v{i}").into_bytes())
                .unwrap();
        }
        log.publish(999_999, 1, "/f/G/elsewhere".to_string(), b"no".to_vec())
            .unwrap();
    }
    let b = Broker::open(&p.log).unwrap();
    let h = b.serve(&p.sock).unwrap();
    (p, b, h)
}

/// A small face published through the broker: `/s/00` .. `/s/<n-1>`, body `v<i>`.
fn small_face(c: &mut Client, n: usize) {
    for i in 0..n {
        c.publish(
            1,
            i as u64 + 1,
            &format!("/s/{i:02}"),
            format!("v{i}").as_bytes(),
        )
        .unwrap();
    }
}

fn subjects(rows: &[Record]) -> Vec<String> {
    rows.iter().map(|(_, s, _)| s.clone()).collect()
}

/// MORE SUBJECTS THAN ONE PAGE ARE ALL WALKED, AND THE WALK ENDS ONLY ON THE CURSOR.
///
/// The fixture is proven multi-page first — one request comes back clamped at
/// `LAST_PAGE_MAX` rows with a live cursor, and `last`, which drops that cursor, reads
/// exactly like a finished answer — so the walk's every-subject answer is one no single
/// page could have given.
#[test]
fn a_walk_reads_past_the_brokers_page_bound_to_the_end_of_the_face() {
    let n = LAST_PAGE_MAX as usize + 100;
    let (p, b, mut h) = serve_face("whole", n);
    let head = b.visible_head();
    let mut c = Client::connect(&p.sock).unwrap();

    let (one, _, resume) = c.last_page(FACE, "", u32::MAX).unwrap();
    assert_eq!(
        one.len(),
        LAST_PAGE_MAX as usize,
        "the broker clamps one page"
    );
    assert!(!resume.is_empty(), "and says there is more");
    let (short, _) = c.last(FACE, "", u32::MAX).unwrap();
    assert_eq!(
        short.len(),
        LAST_PAGE_MAX as usize,
        "`last` is one page with its cursor thrown away"
    );

    let (rows, mark) = c.last_all(FACE).unwrap();
    assert_eq!(rows.len(), n, "every subject, not one page of them");
    for (i, (off, s, body)) in rows.iter().enumerate() {
        assert_eq!(s, &subject(i), "ascending subject order, no gap, no repeat");
        assert_eq!(*off, i as u64);
        assert_eq!(body, format!("v{i}").as_bytes());
    }
    assert_eq!(
        mark,
        (head, head),
        "nothing moved: the first page's mark is the head"
    );

    // The streaming form is the same walk: the same rows, the same mark, and a
    // continuation that says the answer is complete.
    let mut streamed = Vec::new();
    let (smark, rest) = c
        .last_walk(FACE, "", u32::MAX, |row| {
            streamed.push(row);
            Ok(Walk::Continue)
        })
        .unwrap();
    assert_eq!(rest, None, "the walk ran the face out");
    assert_eq!(smark, mark);
    assert_eq!(streamed, rows);

    drop(c);
    h.shutdown();
}

/// THE MARK IS THE FIRST PAGE'S, AND THE TAIL FROM IT SPLICES ON WITH NO GAP.
///
/// `on_row` for page 1 runs before page 2 is asked for, so a write made from inside it
/// lands between the pages. It supersedes TWO subjects: the first (already delivered on
/// page 1) and the last (not reached until page 2). Page 2 then reports the last
/// subject at its NEW value — an offset at or above the head the walk returns, which is
/// the proof that page 2 was read at a later head — and the walk still returns page 1's
/// mark, from which a `subscribe` delivers both superseding records. From page 2's
/// mark the first subject's new value would never arrive.
#[test]
fn the_mark_is_the_first_pages_and_a_subscribe_from_it_misses_nothing() {
    let n = LAST_PAGE_MAX as usize + 100;
    let (p, b, mut h) = serve_face("mark", n);
    let head0 = b.visible_head();
    let mut c = Client::connect(&p.sock).unwrap();
    let mut w = Client::connect(&p.sock).unwrap();

    let mut written: Vec<u64> = Vec::new();
    let mut rows = Vec::new();
    let (mark, rest) = c
        .last_walk(FACE, "", u32::MAX, |row| {
            if written.is_empty() {
                for (seq, s) in [(1, subject(0)), (2, subject(n - 1))] {
                    let (off, deduped) = w.publish(777_777, seq, &s, b"new")?;
                    assert!(!deduped, "a real superseding record");
                    written.push(off);
                }
            }
            rows.push(row);
            Ok(Walk::Continue)
        })
        .unwrap();

    assert_eq!(
        written,
        vec![head0, head0 + 1],
        "both writes landed mid-walk"
    );
    assert_eq!(rest, None);
    assert_eq!(
        rows.len(),
        n,
        "the writes superseded subjects; they added none"
    );
    assert_eq!(
        rows[0],
        (0, subject(0), b"v0".to_vec()),
        "page 1 was read before the write, and reports the value it was read at"
    );
    assert_eq!(
        rows[n - 1],
        (head0 + 1, subject(n - 1), b"new".to_vec()),
        "page 2 was read AFTER the write: its row carries an offset above the returned head"
    );
    assert_eq!(
        mark,
        (head0, head0),
        "the walk returns the FIRST page's mark, not the later head page 2 was read at"
    );

    // The splice: from the first page's `next`, the tail delivers the record that
    // superseded a value page 1 already reported, then the one page 2 already carried
    // (same offset: a reader that tails dedups on offset and folds newest-wins).
    let mut sub = c.subscribe(mark.0, FACE).unwrap();
    assert_eq!(
        sub.recv().unwrap(),
        Some((head0, subject(0), b"new".to_vec())),
        "nothing between the snapshot and the tail is lost"
    );
    assert_eq!(
        sub.recv().unwrap(),
        Some((head0 + 1, subject(n - 1), b"new".to_vec()))
    );

    drop(sub);
    drop(w);
    h.shutdown();
}

/// AN EARLY STOP RETURNS ONLY THE ROWS DELIVERED, AND A CONTINUATION THAT WORKS.
///
/// `Walk::Stop` mid-page, the `max` row bound (asb's `--max`), the head query, and a
/// stop on the very last row — each checked for exactly which rows reached `on_row`,
/// what the continuation says, that continuing from it reassembles the whole face, and
/// that the connection is still usable after a walk that ended mid-page.
#[test]
fn an_early_stop_delivers_only_what_was_taken_and_says_where_to_go_on() {
    let p = fresh("stop");
    let b = Broker::open(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    small_face(&mut c, 10);
    let head = b.visible_head();
    let (whole, _) = c.last_all("/s/*").unwrap();
    assert_eq!(whole.len(), 10);

    // `Walk::Stop` on the 4th row of a 10-row page.
    let mut got = Vec::new();
    let (mark, rest) = c
        .last_walk("/s/*", "", u32::MAX, |row| {
            got.push(row);
            Ok(if got.len() == 4 {
                Walk::Stop
            } else {
                Walk::Continue
            })
        })
        .unwrap();
    assert_eq!(
        got,
        whole[..4].to_vec(),
        "only the rows taken, none after the stop"
    );
    assert_eq!(
        rest.as_deref(),
        Some("/s/03"),
        "continue after the last row taken"
    );
    assert_eq!(mark, (head, head));

    // The page the stop cut short was read to its `Mark`: the connection is at a frame
    // boundary and fully usable.
    let (off, _) = c.publish(2, 1, "/t/elsewhere", b"x").unwrap();
    assert_eq!(off, head, "the connection acks a publish after the stop");

    // Continuing from the continuation reassembles the face.
    let mut rest_rows = Vec::new();
    let (_, end) = c
        .last_walk("/s/*", "/s/03", u32::MAX, |row| {
            rest_rows.push(row);
            Ok(Walk::Continue)
        })
        .unwrap();
    assert_eq!(end, None);
    got.extend(rest_rows);
    assert_eq!(got, whole, "stop + continue == the whole face, once each");

    // The ROW bound: `max = 3` pages the face three rows at a time, each walk handing
    // back the cursor the next one starts from, and the last one saying it is complete.
    let mut paged = Vec::new();
    let mut walks = Vec::new();
    let mut after = String::new();
    loop {
        let mut page = Vec::new();
        let (_, rest) = c
            .last_walk("/s/*", &after, 3, |row| {
                page.push(row);
                Ok(Walk::Continue)
            })
            .unwrap();
        assert!(page.len() <= 3, "max bounds the rows of the WHOLE walk");
        walks.push((subjects(&page), rest.clone()));
        paged.extend(page);
        match rest {
            Some(next) => after = next,
            None => break,
        }
    }
    assert_eq!(paged, whole, "the row-bounded walks reassemble the face");
    assert_eq!(
        walks.iter().map(|(_, r)| r.clone()).collect::<Vec<_>>(),
        vec![
            Some("/s/02".to_string()),
            Some("/s/05".to_string()),
            Some("/s/08".to_string()),
            None
        ],
    );

    // A row bound met exactly at the end of the face still reports a continuation —
    // the walk stopped on `max`, not on the cursor — and continuing finds nothing.
    let mut n = 0;
    let (_, rest) = c
        .last_walk("/s/*", "", 10, |_| {
            n += 1;
            Ok(Walk::Continue)
        })
        .unwrap();
    assert_eq!((n, rest.as_deref()), (10, Some("/s/09")));
    let (_, rest) = c
        .last_walk("/s/*", "/s/09", u32::MAX, |_| panic!("nothing is left"))
        .unwrap();
    assert_eq!(rest, None);

    // `max = 0` is the head query: no row, the mark, and a continuation that is the
    // walk's own `after` — including `""`, which is why the continuation is an Option.
    let head = b.visible_head();
    for start in ["", "/s/04"] {
        let (mark, rest) = c
            .last_walk("/s/*", start, 0, |_| panic!("max = 0 delivers nothing"))
            .unwrap();
        assert_eq!(mark, (head, head));
        assert_eq!(
            rest.as_deref(),
            Some(start),
            "nothing taken: go on from `after`"
        );
    }

    // A stop on the very last row: every row was delivered and the cursor ran out, so
    // the answer IS complete and the continuation says so.
    let (_, rest) = c
        .last_walk("/s/*", "/s/08", u32::MAX, |row| {
            Ok(if row.1 == "/s/09" {
                Walk::Stop
            } else {
                Walk::Continue
            })
        })
        .unwrap();
    assert_eq!(rest, None);

    drop(c);
    h.shutdown();
}

/// AN `on_row` ERROR ENDS THE WALK WITH THAT ERROR — its own kind and message, after
/// exactly the rows that reached `on_row` — and leaves the connection usable.
#[test]
fn an_on_row_error_ends_the_walk_with_that_error() {
    let p = fresh("err");
    let b = Broker::open(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    small_face(&mut c, 6);

    let mut calls = 0;
    let err = c
        .last_walk("/s/*", "", u32::MAX, |_| {
            calls += 1;
            if calls == 2 {
                return Err(io::Error::new(io::ErrorKind::BrokenPipe, "sink closed"));
            }
            Ok(Walk::Continue)
        })
        .unwrap_err();
    assert_eq!(
        err.kind(),
        io::ErrorKind::BrokenPipe,
        "the callback's own error"
    );
    assert_eq!(err.to_string(), "sink closed");
    assert_eq!(calls, 2, "no row after the failing one");

    let (whole, _) = c.last_all("/s/*").unwrap();
    assert_eq!(
        whole.len(),
        6,
        "the connection is still usable after the error"
    );

    drop(c);
    h.shutdown();
}

/// A SCRIPTED PEER on the far end of a socket pair. It answers the i-th request — which
/// must be a `Last` — with `script(i)`: those rows as `Delivery` frames, then a `Mark`
/// whose `next` and `head` are the given head and whose `resume` is the given cursor.
/// Joining it (after the client is dropped) yields every request's `(after, max)`.
#[allow(clippy::type_complexity)]
fn scripted(
    mut script: impl FnMut(usize) -> (Vec<Record>, u64, String) + Send + 'static,
) -> (Client<UnixStream>, thread::JoinHandle<Vec<(String, u32)>>) {
    let (near, mut far) = UnixStream::pair().unwrap();
    let peer = thread::spawn(move || {
        let mut seen = Vec::new();
        while let Ok(Some(frame)) = read_frame(&mut far) {
            let Some(Request::Last { after, max, .. }) = decode_request(&frame) else {
                panic!("the walk sent something other than Last");
            };
            let (rows, head, resume) = script(seen.len());
            seen.push((after, max));
            // A client that refuses a page hangs up mid-page: stop writing then.
            let mut sent = rows.into_iter().try_for_each(|(off, s, body)| {
                write_frame(&mut far, &encode_delivery(off, &s, &body))
            });
            if sent.is_ok() {
                sent = write_frame(
                    &mut far,
                    &encode_response(&Response::Mark {
                        next: head,
                        head,
                        resume,
                    }),
                );
            }
            if sent.is_err() {
                break;
            }
        }
        seen
    });
    (Client::from_stream(near), peer)
}

fn row(off: u64, s: &str) -> Record {
    (off, s.to_string(), s.as_bytes().to_vec())
}

/// AN EMPTY PAGE IS NOT THE END, THE WALK PAGES ON THE CURSOR RATHER THAN ON THE LAST
/// ROW, EACH REQUEST ASKS FOR EXACTLY THE ROWS STILL OWED, AND THE MARK IS THE FIRST
/// PAGE'S — pinned at the wire, where every page reports a different head.
#[test]
fn empty_pages_with_a_live_cursor_are_walked_through_on_the_cursor() {
    let (mut c, peer) = scripted(|i| match i {
        0 => (vec![], 10, "/s/b".into()),
        1 => (vec![row(3, "/s/c")], 11, "/s/d".into()),
        2 => (vec![], 12, "/s/m".into()),
        3 => (vec![row(7, "/s/n")], 13, String::new()),
        _ => panic!("the walk asked past the empty cursor"),
    });
    let mut got = Vec::new();
    let (mark, rest) = c
        .last_walk("/s/*", "", u32::MAX, |r| {
            got.push(r);
            Ok(Walk::Continue)
        })
        .unwrap();
    drop(c);
    let seen = peer.join().unwrap();

    assert_eq!(got, vec![row(3, "/s/c"), row(7, "/s/n")]);
    assert_eq!(rest, None);
    assert_eq!(
        mark,
        (10, 10),
        "the FIRST page's mark, not the last page's (13)"
    );
    assert_eq!(
        seen,
        vec![
            (String::new(), u32::MAX),
            ("/s/b".to_string(), u32::MAX),
            // The cursor, not the last row ("/s/c"); one row fewer owed.
            ("/s/d".to_string(), u32::MAX - 1),
            ("/s/m".to_string(), u32::MAX - 1),
        ]
    );
}

/// `max` IS THE CALLER'S PROMISE: a peer that sends more rows than it was asked for
/// is refused as a protocol violation (`InvalidData`), and none of its rows is handed
/// to `on_row` -- an over-long page is not a page, so nothing of it is delivered.
#[test]
fn a_peer_that_over_delivers_is_refused_and_delivers_nothing() {
    let (mut c, peer) = scripted(|_| {
        let rows = ["/s/a", "/s/b", "/s/c", "/s/d", "/s/e"];
        (rows.iter().map(|s| row(1, s)).collect(), 9, "/s/e".into())
    });
    let mut got = Vec::new();
    let err = c
        .last_walk("/s/*", "", 3, |r| {
            got.push(r);
            Ok(Walk::Continue)
        })
        .expect_err("a 5-row page answers a request for at most 3");
    drop(c);
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(got.is_empty(), "no row of the over-long page is delivered");
    assert_eq!(
        peer.join().unwrap(),
        vec![(String::new(), 3)],
        "one request"
    );
}

/// An `on_row` error ends the walk where it happened: no further request is made.
#[test]
fn an_on_row_error_asks_for_no_further_page() {
    let (mut c, peer) = scripted(|i| {
        let s = format!("/s/{i:02}");
        (vec![row(i as u64, &s)], 5, s)
    });
    let err = c
        .last_walk("/s/*", "", u32::MAX, |r| {
            if r.1 == "/s/01" {
                return Err(io::Error::other("refused on page 2"));
            }
            Ok(Walk::Continue)
        })
        .unwrap_err();
    drop(c);
    assert_eq!(err.to_string(), "refused on page 2");
    assert_eq!(
        peer.join().unwrap().len(),
        2,
        "page 1, page 2, and no page 3"
    );
}

/// THE PAGE BOUND IS AN ERROR, NOT A SHORT ANSWER — at the real constant.
///
/// A peer whose cursor never runs out is walked for EXACTLY `LAST_WALK_PAGES_MAX`
/// requests, every row it sent reaches `on_row`, and the walk then fails naming the
/// bound instead of returning what it had as if it were the face. The boundary is
/// pinned from the other side too: an answer that ends ON the last permitted page is a
/// complete answer, not an error.
#[test]
fn a_walk_that_does_not_end_within_the_page_bound_is_an_error() {
    let endless = |i: usize| {
        let s = format!("/p/{i:05}");
        (vec![row(i as u64, &s)], 1, s)
    };
    let (mut c, peer) = scripted(endless);
    let mut rows = 0usize;
    let err = c
        .last_walk("/p/*", "", u32::MAX, |_| {
            rows += 1;
            Ok(Walk::Continue)
        })
        .unwrap_err();
    drop(c);
    let seen = peer.join().unwrap();
    assert_eq!(
        seen.len(),
        LAST_WALK_PAGES_MAX,
        "exactly the bound, not one more"
    );
    assert_eq!(
        rows, LAST_WALK_PAGES_MAX,
        "every row sent was delivered first"
    );
    assert!(
        err.to_string()
            .contains(&format!("did not end within {LAST_WALK_PAGES_MAX} pages")),
        "{err}"
    );

    // The same walk through the collecting form is the same error, not a short Vec.
    let (mut c, peer) = scripted(endless);
    assert!(c.last_all("/p/*").is_err());
    drop(c);
    assert_eq!(peer.join().unwrap().len(), LAST_WALK_PAGES_MAX);

    // An answer that ends on the last permitted page is complete.
    let (mut c, peer) = scripted(|i| {
        let s = format!("/p/{i:05}");
        let resume = if i + 1 == LAST_WALK_PAGES_MAX {
            String::new()
        } else {
            s.clone()
        };
        (vec![row(i as u64, &s)], 1, resume)
    });
    let (rows, mark) = c.last_all("/p/*").unwrap();
    drop(c);
    assert_eq!(rows.len(), LAST_WALK_PAGES_MAX);
    assert_eq!(mark, (1, 1));
    assert_eq!(peer.join().unwrap().len(), LAST_WALK_PAGES_MAX);
}
