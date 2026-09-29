//! LAST-VALUE QUERY throughput (fabric R12): how fast the broker answers a page of
//! `Last{filter, after, max}` over a log with many distinct subjects and a long
//! history, and whether answering it stalls ingest.
//!
//! Three numbers, all from one run. The first is the gated floor; the other two are
//! SAME-RUN RATIOS, and the bench EXITS 2 if either falls below its bound — so they
//! gate the structure on any hardware, which an absolute floor cannot.
//!
//! * `broker_last_queries_per_sec` — full `PAGE`-row pages per second. `Last` is a
//!   range scan of the last-value index from the filter's literal prefix, so the cost
//!   is `O(log n + page)`: it must NOT grow with the length of the history behind it.
//! * `broker_last_page_cost_ratio` — the rate of a `SMALL_PAGE`-row query over the
//!   rate of a `PAGE`-row query on the SAME index. A range scan pays for the page it
//!   returns, so a 64-row page is ~64x cheaper than a 4096-row one; a query that
//!   walked the whole history (or the whole index) instead would cost the same at
//!   either size and drive this toward 1. `MIN_PAGE_RATIO` bounds it.
//! * `broker_last_ingest_ratio` — durable publishes/s while the query loop hammers
//!   the broker, over publishes/s for the SAME work with the query loop idle. It
//!   fails if a query holds the writer's log lock for its whole duration instead of
//!   for the page clone. `MIN_INGEST_RATIO` bounds it.
//!
//!   SUBJECTS=10000 HISTORY=200000 cargo run --release -p astream-broker --example broker_last_bench

#[cfg(unix)]
use astream_broker::{Broker, Client};
#[cfg(unix)]
use std::time::Instant;

/// Ingest under a concurrent query loop must keep at least this share of its own
/// un-queried rate in the SAME run. Set far below the observed ratio (which is close
/// to 1: a query holds the log lock only long enough to clone a page of `Arc`s), so
/// it gates the structural regression — a query that parks the writer — and not
/// scheduling noise.
#[cfg(unix)]
const MIN_INGEST_RATIO: f64 = 0.25;

/// A small page must be at least this many times cheaper than a full one. The ideal
/// is `PAGE / SMALL_PAGE` (64); a per-query walk of the history or of the whole
/// subject index would flatten it to ~1. Set far below observed, so it gates that
/// structural regression and not the fixed per-request cost.
#[cfg(unix)]
const MIN_PAGE_RATIO: f64 = 8.0;

#[cfg(unix)]
fn env(k: &str, d: u64) -> u64 {
    std::env::var(k)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(d)
}

/// The bench serves the broker on a Unix-domain socket; std has no UDS on
/// Windows, so there is nothing honest to measure there.
#[cfg(not(unix))]
fn main() {
    eprintln!("broker_last_bench requires Unix-domain sockets; run it on a unix host");
}

/// The subject of retained row `i` — zero-padded so subject order is index order,
/// and shaped like the fabric's roster face `/f/<F>/pub/<node>/<sid>/presence`.
#[cfg(unix)]
fn row_subject(i: u64) -> String {
    format!("/f/bench/pub/n-{:04}/s-{:08}/presence", i / 1000, i)
}

/// Which producer owns row `i`. `MAX_SUBJECTS_PER_PRODUCER` bounds the distinct
/// subjects ONE producer may create (4096), so a 10 000-subject roster is spread over
/// several producers exactly as a real fleet's nodes would be.
#[cfg(unix)]
fn producer_of(i: u64) -> u64 {
    1 + i / 2048
}

/// Publish `bodies` — one per (subject, producer, seq) triple the closure yields —
/// keeping `window` acks in flight, and return the seconds it took. Used for both the
/// fill and the two ingest legs, so the legs are the same code path.
#[cfg(unix)]
fn publish_windowed(
    c: &mut Client,
    n: u64,
    window: u64,
    mut at: impl FnMut(u64) -> (u64, u64, String),
    body: &[u8],
) -> f64 {
    let start = Instant::now();
    let mut sent = 0u64;
    let mut acked = 0u64;
    while acked < n {
        while sent < n && sent - acked < window {
            let (pid, seq, subject) = at(sent);
            c.send_publish(pid, seq, &subject, body).unwrap();
            sent += 1;
        }
        c.recv_publish_ack().unwrap();
        acked += 1;
    }
    start.elapsed().as_secs_f64()
}

/// Removes the bench's files when dropped, so a run that returns or panics leaves
/// nothing behind. Bound before the broker, so it drops after it; `main` drops it
/// by hand before a `process::exit`, which runs no destructors.
#[cfg(unix)]
struct Cleanup(Vec<String>);

#[cfg(unix)]
impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let _ = std::fs::remove_file(path);
        }
    }
}

#[cfg(unix)]
fn main() {
    let pid = std::process::id();
    let log = format!("/tmp/aslastbench_{pid}.log");
    let sock = format!("/tmp/aslastbench_{pid}.sock");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup(vec![log.clone(), sock.clone()]);
    let broker = Broker::open(&log).unwrap();
    let _h = broker.serve(&sock).unwrap();

    let subjects = env("SUBJECTS", 10_000).max(1);
    let history = env("HISTORY", 200_000).max(subjects);
    let page = env("PAGE", 4096).max(1);
    let queries = env("QUERIES", 200).max(1);
    let ingest_n = env("INGEST_N", 12_000).max(1);
    let small = env("SMALL_PAGE", 64).max(1).min(page);
    if page * 2 > subjects {
        eprintln!("PAGE*2 must not exceed SUBJECTS (two full pages are queried)");
        drop(tmp);
        std::process::exit(2);
    }

    // ---- Fill: `history` records spread round-robin over `subjects` distinct
    // subjects, so every subject's retained value sits behind a long tail of
    // superseded records. That is the shape a range scan must not walk.
    {
        let mut w = Client::connect(&sock).unwrap();
        let mut seqs = vec![0u64; (producer_of(subjects - 1) + 2) as usize];
        let mut plan: Vec<(u64, u64, String)> = Vec::with_capacity(history as usize);
        for k in 0..history {
            let i = k % subjects;
            let p = producer_of(i);
            seqs[p as usize] += 1;
            plan.push((p, seqs[p as usize], row_subject(i)));
        }
        let secs = publish_windowed(
            &mut w,
            history,
            512,
            |k| plan[k as usize].clone(),
            b"state=live inc=1",
        );
        eprintln!(
            "fill: {history} records over {subjects} subjects in {secs:.2}s \
             ({:.0} durable publishes/s)",
            history as f64 / secs
        );
    }

    // ---- Query leg. Two `after` cursors, each of which yields a FULL page, so every
    // measured query does the same amount of work and a short page cannot inflate the
    // rate. The filter's literal prefix is `/f/bench/pub/`, so the scan starts at the
    // cursor and stops at the page — never at the end of the index, and never in the
    // history behind it.
    let filter = "/f/bench/pub/*/*/presence";
    let cursors = ["".to_string(), row_subject(page - 1)];
    let mut q = Client::connect(&sock).unwrap();
    for after in &cursors {
        let (rows, _) = q.last(filter, after, page as u32).unwrap();
        if rows.len() as u64 != page {
            eprintln!(
                "cursor {after:?} did not yield a full page ({} rows)",
                rows.len()
            );
            std::process::exit(2);
        }
    }
    let measure = |c: &mut Client, rows_per_page: u64| -> f64 {
        let start = Instant::now();
        let mut rows_seen = 0u64;
        for k in 0..queries {
            let (rows, _) = c
                .last(filter, &cursors[(k % 2) as usize], rows_per_page as u32)
                .unwrap();
            rows_seen += rows.len() as u64;
        }
        let secs = start.elapsed().as_secs_f64();
        if rows_seen != queries * rows_per_page {
            eprintln!("a query returned a short page: {rows_seen} rows over {queries} queries");
            std::process::exit(2);
        }
        queries as f64 / secs
    };
    let qps = measure(&mut q, page);
    // The same query for a SMALL page. A range scan from the cursor pays for the page
    // it returns, so this is far cheaper; a per-query walk of the whole history would
    // cost the same either way and collapse the ratio toward 1.
    let qps_small = measure(&mut q, small);
    let page_ratio = qps_small / qps;

    // ---- Ingest legs. The same durable publishes, first with the query loop idle,
    // then with it running flat out on another connection. `Last` holds the log lock
    // only for the page clone, so the second rate must stay close to the first.
    let ingest = |c: &mut Client, tag: u64| -> f64 {
        let subject = format!("/f/bench/in/n-0000/s-00000000/h-bench/note{tag}");
        let secs = publish_windowed(
            c,
            ingest_n,
            64,
            |k| (9_000 + tag, k + 1, subject.clone()),
            b"x",
        );
        ingest_n as f64 / secs
    };

    let mut w = Client::connect(&sock).unwrap();
    let alone = ingest(&mut w, 0);

    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let hammer = {
        let sock = sock.clone();
        let stop = stop.clone();
        let cursors = cursors.clone();
        std::thread::spawn(move || {
            let mut c = Client::connect(&sock).unwrap();
            let mut n = 0u64;
            while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                c.last(filter, &cursors[(n % 2) as usize], page as u32)
                    .unwrap();
                n += 1;
            }
            n
        })
    };
    let under_query = ingest(&mut w, 1);
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    let hammered = hammer.join().unwrap();
    let ratio = under_query / alone;

    println!("METRIC broker_last_queries_per_sec {qps:.0}");
    println!("METRIC broker_last_ingest_ratio {ratio:.3}");
    println!("METRIC broker_last_page_cost_ratio {page_ratio:.2}");
    eprintln!(
        "astream-broker Last: {queries} pages of {page} rows over {subjects} subjects \
         / {history} records at {qps:.0} queries/s \
         ({:.0} rows/s); a {small}-row page runs at {qps_small:.0} queries/s = \
         {page_ratio:.2}x the full page; durable ingest {alone:.0} ops/s alone vs {under_query:.0} ops/s \
         under {hammered} concurrent queries = ratio {ratio:.3}",
        qps * page as f64
    );
    let _ = std::fs::remove_file(&log);

    if page_ratio < MIN_PAGE_RATIO {
        eprintln!(
            "FAIL: small-page/full-page rate ratio {page_ratio:.2} < {MIN_PAGE_RATIO} — a Last \
             query is scanning more than the page it returns"
        );
        drop(tmp);
        std::process::exit(2);
    }
    if ratio < MIN_INGEST_RATIO {
        eprintln!(
            "FAIL: concurrent-query ingest ratio {ratio:.3} < {MIN_INGEST_RATIO} — a Last \
             query is holding the writer's log lock beyond its page"
        );
        drop(tmp);
        std::process::exit(2);
    }
}
