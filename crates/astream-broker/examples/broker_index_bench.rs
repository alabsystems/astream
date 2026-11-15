// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WHAT A RETAINED RECORD COSTS A LOG'S MEMORY, AND WHAT ITS INDEX COSTS A PUBLISH. The
//! measurement behind `docs/DESIGN-aterm-fabric.md` §14 open question 8: every retained
//! record keeps an entry in the residency tier (`tier.rs`) and one in the exactly-once dedup
//! index (`dedup.rs`), under any residency budget, so they set the floor of an always-on
//! broker's memory.
//!
//! For each count in `INDEX_RECORDS` (`503000,1006000` by default) the bench writes a Relaxed
//! log of 128-byte records on one fabric subject, keyed as `INDEX_SHAPE` says, timed
//! (`publish_ns`, per record); re-sends every key once in a strided order, each answered
//! from the dedup index with nothing appended (`dedup_ns`, per re-send); and closes it
//! cleanly. It then reopens the log twice, `BrokerLog::open_opts` with the residency budget in
//! its `OpenOptions`, as an embedder opens it (aterm's broker), at a budget of 0 (one record
//! decoded) and of 16 MiB, and reports the most the open itself held at once, its peak: the
//! live heap bytes at their highest during the open less before it (`open_peak_bytes`, aterm
//! F16), and what the open log holds:
//! the live heap bytes, counted by this process's global allocator, after the open less
//! before it (`held_bytes`, and per retained record `per_record`), the part of it in
//! allocations of 1 MiB or more (`large_bytes` in `large_allocs` allocations, and per retained
//! record `large_per_record`: at a budget of 0 the tier's three columns of 4 B a record, its
//! frame starts, broker times and bytes with flags, and under a budget the hot window's ring
//! of handles beside them; every other part is the tier's 1-byte column of subject indices,
//! under 1 MiB below 1,048,576 records, or a heap object, a chunk or a buffer under that size),
//! and how long the open took (`open_ms`). Then it times one-record reads
//! (`BrokerLog::read_range`) spread over up to 65,536 of the records that budget left cold and
//! as many of those it keeps resident (`read_ns` per read and the percentiles of each one, and
//! the log's `cold_reads` over them, which says each cold one went to the file): what a
//! residency budget costs a reader of old records, the page cache warm. Then it times
//! `BrokerLog::stats` [`WALKS`] times (`walk_ns`: the median, fastest and slowest). The slot
//! vector found its pending wills by reading every retained record's summary, and the pages,
//! until aterm F19, by walking the pages that name the will subject; since F19 `stats` counts
//! them from the log's latest-will map and reads no record, summary or page, so `walk_ns` is
//! no walk but a pass over that map, empty here (`examples/broker_stats_bench` times `stats`
//! as a log retains wills).
//! Last it times a filtered read's scan [`SCANS`] times (`BrokerLog::fetch` of [`LANE`], a
//! session's lane, from the base to the head: `scan_ns`, the median, and per record
//! `per_record_ns` with the fastest and slowest), which matches none, as a bridge's refill
//! pages a session's lane over a backlog (aterm D10f), and the same lane's refill as the
//! broker serves it (aterm F11c). Every page here names the one [`SUBJECT`], which the lane
//! does not want, so both pass each page whole by its subject ids (`Tier::passing`, aterm
//! F11c) and read no record's summary or column entries: their `per_record_ns` is a page's
//! cost spread over its 256 records, not what reading one record costs (a page naming a
//! subject the lane wants is read record by record, which no shape here measures). The
//! refill is `Fetch`es from the base to the
//! head of at most `FETCH_SCAN_MAX` records each, as `serve_fetch` asks one with the log's lock
//! held, so a fetch timed alone is its part of one hold of that lock (`refill_ns` and its
//! `per_record_ns`, the median refill, and `hold_p50_ns`, `hold_p99_ns` and `hold_max_ns` over
//! every fetch of the [`SCANS`] refills).
//! The shapes (`INDEX_SHAPE`, `filler` by default):
//!
//! - `filler`: aterm's attach-bench filler, one producer publishing consecutive seqs from 1.
//! - `acks`: a processor that publishes and acks under one id: each publish of its next
//!   consecutive seq is followed by a `process_and_produce` whose seq is
//!   `ACK_SEQ_BASE | the offset just published` (an ack's, above every ordinary seq),
//!   committing a group past it. Half the records are its publishes, half its acks.
//! - `producers`: one record per producer, as `asb pub` with no `--id` publishes (its process
//!   id, a nanosecond seq).
//! - `short`: groups of consecutive keys from many short-lived producers. Set
//!   `INDEX_KEYS_PER_PRODUCER` (default 2); for 50,000 producers with 4 keys use
//!   `INDEX_SHAPE=short INDEX_KEYS_PER_PRODUCER=4 INDEX_RECORDS=200000`.
//!   This shape publishes with a zero residency budget, so `publish_held_bytes`
//!   measures index growth without keeping every decoded payload. Other shapes
//!   retain their original unbounded publish budget. All shapes also print the
//!   live heap and peak heap delta during publishing, before close-time shrinking.
//!
//! Set `INDEX_INSPECT=1` to compare fallible full-log collection with streaming
//! inspection at the zero residency budget. Both compute SHA-256 over identical
//! bytes; the extra live-heap peak excludes the already-open log. The streamed
//! copy uses 64 KiB of stack scratch and a fixed-size digest sink.
//!
//! The counting allocator is this bench's only `unsafe` and stays here: the library is
//! `forbid(unsafe_code)`, and an example is its own crate.
//!
//!   targo --unverified run --release -p astream-broker --example broker_index_bench
//!
//! One line per count and budget:
//! `INDEX shape=S records=N budget=B resident=R/BYTES held_bytes=H per_record=P large_bytes=L
//! large_allocs=K large_per_record=Q open_peak_bytes=X open_ms=O`, after each up to two
//! `INDEX shape=S records=N budget=B read=cold|resident reads=K read_ns=T p50_ns=A p95_ns=B
//! p99_ns=C cold_reads=D` (the mean, then the nearest-rank percentiles of each read timed
//! alone, which carry the clock's own cost), then
//! `INDEX shape=S records=N budget=B walk=stats walks=K walk_ns=M min_ns=F max_ns=S`, then
//! `INDEX shape=S records=N budget=B scan=fetch scans=K scan_ns=M per_record_ns=P
//! min_per_record_ns=F max_per_record_ns=S`, then
//! `INDEX shape=S records=N budget=B scan=refill refills=K fetches=F refill_ns=M
//! per_record_ns=P hold_p50_ns=A hold_p99_ns=B hold_max_ns=C`, and
//! one per count: `INDEX shape=S records=N publish_ns=X dedup_ns=Y`. Last, for the
//! `filler` shape only, `METRIC broker_index_bytes_per_record P`: the most any count held a
//! retained record at a budget of 0, which claim `broker.bench.index-bytes-ceiling` gates, then
//! `METRIC broker_open_peak_bytes_per_record X`: the most any count's open held at once at a
//! budget of 0, a retained record, which claim `broker.bench.open-peak-ceiling` gates.

#![deny(unsafe_code)]

use astream_broker::broker::FETCH_SCAN_MAX;
use astream_broker::{BrokerLog, Durability, OpenOptions, ACK_SEQ_BASE};
use astream_digest::Sha256;
use astream_wire::{Filter, Offset};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

#[allow(unsafe_code)]
mod counting {
    //! A global allocator that forwards to the system's and keeps a count of the bytes live,
    //! and of those in LARGE allocations (at least [`LARGE`] bytes each) apart.

    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub(crate) struct Counting;

    /// The size from which an allocation is counted LARGE: at the bench's counts, the tier's
    /// columns of 4 B a record and the hot window's ring of handles are; the tier's 1-byte
    /// subject column (until 1,048,576 records), its pages, the log's per-record heap objects,
    /// its index chunks and its buffers are not.
    pub(crate) const LARGE: usize = 1 << 20;

    static LIVE: AtomicUsize = AtomicUsize::new(0);
    static PEAK: AtomicUsize = AtomicUsize::new(0);
    static LARGE_LIVE: AtomicUsize = AtomicUsize::new(0);
    static LARGE_COUNT: AtomicUsize = AtomicUsize::new(0);

    /// Bytes allocated and not yet freed.
    pub(crate) fn live() -> usize {
        LIVE.load(Ordering::SeqCst)
    }

    /// The most bytes live at once since the last [`reset_peak`].
    pub(crate) fn peak() -> usize {
        PEAK.load(Ordering::SeqCst)
    }

    /// Start a new peak from the bytes live now.
    pub(crate) fn reset_peak() {
        PEAK.store(LIVE.load(Ordering::SeqCst), Ordering::SeqCst);
    }

    /// `(bytes, allocations)` live in allocations of at least [`LARGE`] bytes.
    pub(crate) fn large() -> (usize, usize) {
        (
            LARGE_LIVE.load(Ordering::SeqCst),
            LARGE_COUNT.load(Ordering::SeqCst),
        )
    }

    fn add(size: usize) {
        let now = LIVE.fetch_add(size, Ordering::SeqCst).saturating_add(size);
        PEAK.fetch_max(now, Ordering::SeqCst);
        if size >= LARGE {
            LARGE_LIVE.fetch_add(size, Ordering::SeqCst);
            LARGE_COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn sub(size: usize) {
        LIVE.fetch_sub(size, Ordering::SeqCst);
        if size >= LARGE {
            LARGE_LIVE.fetch_sub(size, Ordering::SeqCst);
            LARGE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    // SAFETY: every method forwards its arguments unchanged to `System`, which upholds
    // `GlobalAlloc`'s contract; the count is bookkeeping beside it and never touches memory.
    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            // SAFETY: the caller's contract for `alloc` is `System.alloc`'s.
            let p = unsafe { System.alloc(layout) };
            if !p.is_null() {
                add(layout.size());
            }
            p
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            // SAFETY: the caller's contract for `alloc_zeroed` is `System.alloc_zeroed`'s.
            let p = unsafe { System.alloc_zeroed(layout) };
            if !p.is_null() {
                add(layout.size());
            }
            p
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            // SAFETY: `ptr` came from this allocator (so from `System`) with `layout`.
            unsafe { System.dealloc(ptr, layout) };
            sub(layout.size());
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            // SAFETY: `ptr` came from this allocator (so from `System`) with `layout`, and
            // the caller's contract for `new_size` is `System.realloc`'s.
            let p = unsafe { System.realloc(ptr, layout, new_size) };
            if !p.is_null() {
                sub(layout.size());
                add(new_size);
            }
            p
        }
    }
}

#[global_allocator]
static ALLOC: counting::Counting = counting::Counting;

/// aterm's attach-bench filler: one subject, 128-byte bodies.
const SUBJECT: &str = "/f/lab/pub/n-a/s-one/ev";
const BODY: usize = 128;
const PRODUCER: u64 = 7;
/// The group the `acks` shape's processor commits.
const GROUP: &str = "proc";
/// The `producers` shape's first seq: a nanosecond clock's reading in 2026.
const NANOS: u64 = 1_793_000_000_000_000_000;
const BUDGETS: [usize; 2] = [0, 16 << 20];
/// The one-record reads timed in each of a reopened log's cold records and its resident ones.
const READS: u64 = 65_536;
/// The `stats` calls timed at each budget.
const WALKS: usize = 9;
/// The filtered scans timed at each budget.
const SCANS: usize = 9;
/// A refill's kind of filter (a session's lane on the node), which no record of any shape
/// matches: its scan passes every page whole by its subject ids, reading no record's summary
/// and decoding none.
const LANE: &str = "/f/lab/in/n-a/s-one/>";
/// The records a refill's `Fetch` asks for (none matches, so any page size reads alike).
const REFILL_PAGE: usize = 256;

/// How the bench keys its records (`INDEX_SHAPE`; the module doc says each).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Filler,
    Acks,
    Producers,
    Short(u64),
}

impl Shape {
    fn name(self) -> &'static str {
        match self {
            Shape::Filler => "filler",
            Shape::Acks => "acks",
            Shape::Producers => "producers",
            Shape::Short(_) => "short",
        }
    }
}

/// Removes the bench's directory when dropped.
struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn counts() -> Result<Vec<u64>, String> {
    let raw = std::env::var("INDEX_RECORDS").unwrap_or_else(|_| "503000,1006000".to_string());
    let mut out = Vec::new();
    for part in raw.split(',') {
        match part.trim().parse::<u64>() {
            Ok(n) if n > 0 => out.push(n),
            _ => {
                return Err(format!(
                    "INDEX_RECORDS takes positive whole numbers, got {raw:?}"
                ))
            }
        }
    }
    Ok(out)
}

fn shape() -> Result<Shape, String> {
    match std::env::var("INDEX_SHAPE").as_deref() {
        Err(_) | Ok("filler") => Ok(Shape::Filler),
        Ok("acks") => Ok(Shape::Acks),
        Ok("producers") => Ok(Shape::Producers),
        Ok("short") => {
            let raw = std::env::var("INDEX_KEYS_PER_PRODUCER").unwrap_or_else(|_| "2".to_string());
            match raw.parse::<u64>() {
                Ok(keys) if keys > 0 => Ok(Shape::Short(keys)),
                _ => Err(format!(
                    "INDEX_KEYS_PER_PRODUCER takes a positive whole number, got {raw:?}"
                )),
            }
        }
        Ok(other) => Err(format!(
            "INDEX_SHAPE takes filler, acks, producers or short, got {other:?}"
        )),
    }
}

/// Nanoseconds per operation, to one decimal.
fn per_op(took: std::time::Duration, n: u64) -> f64 {
    (took.as_nanos() as f64 / n as f64 * 10.0).round() / 10.0
}

struct DigestSink {
    digest: Sha256,
    bytes: u64,
}

impl Write for DigestSink {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.digest.update(bytes);
        self.bytes = self.bytes.saturating_add(bytes.len() as u64);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn inspect(log: &BrokerLog, name: &str, n: u64) -> io::Result<()> {
    let before = counting::live();
    counting::reset_peak();
    let start = Instant::now();
    let bytes = log.try_bytes()?;
    let count = bytes.len() as u64;
    let mut digest = Sha256::new();
    digest.update(&bytes);
    let expected = digest.finalize();
    let collect_ns = start.elapsed().as_nanos();
    let collect_peak = counting::peak().saturating_sub(before);
    drop(bytes);

    let before = counting::live();
    counting::reset_peak();
    let start = Instant::now();
    let mut sink = DigestSink {
        digest: Sha256::new(),
        bytes: 0,
    };
    let copied = log.copy_bytes_to(&mut sink)?;
    let streamed_ns = start.elapsed().as_nanos();
    let streamed_peak = counting::peak().saturating_sub(before);
    assert_eq!(copied, count);
    assert_eq!(sink.bytes, count);
    assert_eq!(sink.digest.finalize(), expected);
    println!("INDEX shape={name} records={n} inspect=collect bytes={count} extra_peak_bytes={collect_peak} elapsed_ns={collect_ns}");
    println!("INDEX shape={name} records={n} inspect=stream bytes={count} extra_peak_bytes={streamed_peak} scratch_bytes=65536 elapsed_ns={streamed_ns} sha256_equal=true");
    Ok(())
}

/// Publishes record `i` of `shape` (it lands at offset `i`, the log starting at 0, or is
/// answered with that offset when re-sent): its offset and whether the index answered it.
fn put(log: &mut BrokerLog, shape: Shape, i: u64, body: &[u8]) -> std::io::Result<(u64, bool)> {
    let subject = SUBJECT.to_string();
    let (off, deduped) = match shape {
        Shape::Filler => log.publish(PRODUCER, i + 1, subject, body.to_vec())?,
        Shape::Producers => log.publish(i + 1, NANOS + i * 7_919, subject, body.to_vec())?,
        Shape::Short(keys) => log.publish(i / keys + 1, i % keys + 1, subject, body.to_vec())?,
        Shape::Acks if i % 2 == 0 => log.publish(PRODUCER, i / 2 + 1, subject, body.to_vec())?,
        Shape::Acks => log.process_and_produce(
            PRODUCER,
            ACK_SEQ_BASE | (i - 1),
            subject,
            body.to_vec(),
            GROUP.to_string(),
            i,
        )?,
    };
    Ok((off.0, deduped))
}

/// Runs one count; returns what the open log held a retained record at a budget of 0, and the
/// most its open held at once, a retained record.
fn run(dir: &std::path::Path, shape: Shape, n: u64) -> std::io::Result<(f64, f64)> {
    let path = dir.join(format!("index-{n}.log"));
    let body = vec![b'e'; BODY];
    let name = shape.name();
    if let Shape::Short(keys) = shape {
        println!(
            "INDEX shape={name} records={n} keys_per_producer={keys} producers={}",
            n.div_ceil(keys)
        );
    }
    {
        let before = counting::live();
        counting::reset_peak();
        let mut log = if matches!(shape, Shape::Short(_)) {
            BrokerLog::open_opts(
                &path,
                OpenOptions::new(Durability::Relaxed).with_resident_budget(0),
                BrokerLog::prepare_nothing,
            )?
        } else {
            BrokerLog::open_with(&path, Durability::Relaxed)?
        };
        let start = Instant::now();
        for i in 0..n {
            let (off, deduped) = put(&mut log, shape, i, &body)?;
            assert!(
                !deduped && off == i,
                "record {i} landed at {off} (deduped {deduped})"
            );
        }
        let publish = start.elapsed();
        let publish_held = counting::live().saturating_sub(before);
        let publish_peak = counting::peak().saturating_sub(before);
        // A stride coprime to n visits every key once, out of order.
        let stride = (1..n)
            .rev()
            .find(|s| gcd(*s, n) == 1 && *s > n / 2)
            .unwrap_or(1);
        let start = Instant::now();
        let mut i = 0u64;
        for _ in 0..n {
            let (off, deduped) = put(&mut log, shape, i, &body)?;
            assert!(
                deduped && off == i,
                "the re-send of record {i} is not its original"
            );
            i = (i + stride) % n;
        }
        let dedup = start.elapsed();
        log.close_clean()?;
        println!(
            "INDEX shape={name} records={n} publish_ns={} dedup_ns={} \
             publish_held_bytes={publish_held} publish_peak_bytes={publish_peak}",
            per_op(publish, n),
            per_op(dedup, n)
        );
    }
    let (mut at_zero, mut peak_at_zero) = (0.0, 0.0);
    for budget in BUDGETS {
        let before = counting::live();
        let (large_before, large_allocs_before) = counting::large();
        counting::reset_peak();
        let start = Instant::now();
        let opts = OpenOptions::new(Durability::Relaxed).with_resident_budget(budget);
        let log = BrokerLog::open_opts(&path, opts, BrokerLog::prepare_nothing)?;
        let open = start.elapsed();
        let open_peak = counting::peak().saturating_sub(before);
        let held = counting::live().saturating_sub(before);
        let (large, large_allocs) = counting::large();
        let large = large.saturating_sub(large_before);
        let large_allocs = large_allocs.saturating_sub(large_allocs_before);
        let (resident, bytes, _) = log.residency();
        let per_record = held as f64 / n as f64;
        if budget == 0 {
            at_zero = per_record;
            peak_at_zero = open_peak as f64 / n as f64;
        }
        assert_eq!(
            log.head().0 - log.base().0,
            n,
            "the reopened log lost records"
        );
        println!(
            "INDEX shape={name} records={n} budget={budget} resident={resident}/{bytes} \
             held_bytes={held} per_record={per_record:.2} large_bytes={large} \
             large_allocs={large_allocs} large_per_record={:.2} open_peak_bytes={open_peak} \
             open_ms={:.1}",
            large as f64 / n as f64,
            open.as_secs_f64() * 1000.0
        );
        // One-record reads spread over the records this budget left cold (budget 0: all but
        // the newest), then over the ones it keeps resident (the hot window at the head).
        let (base, head) = (log.base().0, log.head().0);
        let hot_from = head - resident as u64;
        for (what, lo, hi) in [("cold", base, hot_from), ("resident", hot_from, head)] {
            let span = hi - lo;
            if span == 0 {
                continue;
            }
            let reads = span.min(READS);
            let stride = span / reads;
            let cold_before = log.cold_reads();
            let mut each: Vec<u64> = Vec::with_capacity(reads as usize);
            let start = Instant::now();
            for j in 0..reads {
                let one = Instant::now();
                let got = log.read_range(Offset(lo + j * stride), 1);
                each.push(u64::try_from(one.elapsed().as_nanos()).unwrap_or(u64::MAX));
                assert_eq!(
                    got.len(),
                    1,
                    "a {what} read of {} returned nothing",
                    lo + j * stride
                );
            }
            let took = start.elapsed();
            each.sort_unstable();
            println!(
                "INDEX shape={name} records={n} budget={budget} read={what} reads={reads} \
                 read_ns={} p50_ns={} p95_ns={} p99_ns={} cold_reads={}",
                per_op(took, reads),
                rank(&each, 50),
                rank(&each, 95),
                rank(&each, 99),
                log.cold_reads() - cold_before
            );
        }
        // `stats` counts its pending wills from the latest-will map (aterm F19), empty here, and
        // decodes none of these records.
        let cold_before = log.cold_reads();
        let mut walks: Vec<u64> = Vec::with_capacity(WALKS);
        for _ in 0..WALKS {
            let one = Instant::now();
            let stats = log.stats();
            walks.push(u64::try_from(one.elapsed().as_nanos()).unwrap_or(u64::MAX));
            assert_eq!(stats.retained_records as u64, n, "a walk's count");
        }
        assert_eq!(log.cold_reads(), cold_before, "a walk read a cold record");
        walks.sort_unstable();
        println!(
            "INDEX shape={name} records={n} budget={budget} walk=stats walks={WALKS} \
             walk_ns={} min_ns={} max_ns={}",
            rank(&walks, 50),
            walks.first().copied().unwrap_or(0),
            walks.last().copied().unwrap_or(0)
        );
        // A filtered read's scan (`BrokerLog::fetch`, as a bridge's refill pages a session's
        // lane over a backlog): every page passed whole by its subject ids, no record's summary
        // read, none matching, none decoded.
        let lane = Filter::new(LANE).map_err(|e| std::io::Error::other(e.to_string()))?;
        let cold_before = log.cold_reads();
        let mut scans: Vec<u64> = Vec::with_capacity(SCANS);
        for _ in 0..SCANS {
            let one = Instant::now();
            let (page, next) = log.fetch(base, &lane, 1, n as usize, head);
            scans.push(u64::try_from(one.elapsed().as_nanos()).unwrap_or(u64::MAX));
            assert!(
                page.is_empty() && next == head,
                "a scan of the lane matched {} record(s) and stopped at {next}",
                page.len()
            );
        }
        assert_eq!(log.cold_reads(), cold_before, "a scan read a cold record");
        scans.sort_unstable();
        let per = |ns: u64| ns as f64 / n as f64;
        println!(
            "INDEX shape={name} records={n} budget={budget} scan=fetch scans={SCANS} \
             scan_ns={} per_record_ns={:.3} min_per_record_ns={:.3} max_per_record_ns={:.3}",
            rank(&scans, 50),
            per(rank(&scans, 50)),
            per(scans.first().copied().unwrap_or(0)),
            per(scans.last().copied().unwrap_or(0))
        );
        // A refill's pages of the same lane (aterm F11c): `Fetch`es from the base to the head,
        // each scanning at most `FETCH_SCAN_MAX` records, as `serve_fetch` asks one with the
        // log's lock held, so each fetch timed alone is its part of one hold of that lock.
        let cold_before = log.cold_reads();
        let mut refills: Vec<u64> = Vec::with_capacity(SCANS);
        let mut holds: Vec<u64> = Vec::new();
        for _ in 0..SCANS {
            let mut from = base;
            let whole = Instant::now();
            while from < head {
                let one = Instant::now();
                let (page, next) = log.fetch(from, &lane, REFILL_PAGE, FETCH_SCAN_MAX, head);
                holds.push(u64::try_from(one.elapsed().as_nanos()).unwrap_or(u64::MAX));
                assert!(
                    page.is_empty() && next > from && next <= head,
                    "a refill's fetch from {from} matched {} record(s) and stopped at {next}",
                    page.len()
                );
                from = next;
            }
            refills.push(u64::try_from(whole.elapsed().as_nanos()).unwrap_or(u64::MAX));
        }
        assert_eq!(log.cold_reads(), cold_before, "a refill read a cold record");
        refills.sort_unstable();
        holds.sort_unstable();
        println!(
            "INDEX shape={name} records={n} budget={budget} scan=refill refills={SCANS} \
             fetches={} refill_ns={} per_record_ns={:.3} hold_p50_ns={} hold_p99_ns={} \
             hold_max_ns={}",
            holds.len(),
            rank(&refills, 50),
            per(rank(&refills, 50)),
            rank(&holds, 50),
            rank(&holds, 99),
            holds.last().copied().unwrap_or(0)
        );
        if budget == 0 && std::env::var("INDEX_INSPECT").as_deref() == Ok("1") {
            inspect(&log, name, n)?;
        }
        drop(log);
    }
    std::fs::remove_file(&path)?;
    Ok((at_zero, peak_at_zero))
}

/// The `pct`th percentile of `sorted` (nearest rank; 0 for none).
fn rank(sorted: &[u64], pct: usize) -> u64 {
    let n = sorted.len();
    if n == 0 {
        return 0;
    }
    let k = (pct * n).div_ceil(100).clamp(1, n);
    sorted[k - 1]
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn main() -> ExitCode {
    let (counts, shape) = match (counts(), shape()) {
        (Ok(c), Ok(s)) => (c, s),
        (Err(e), _) | (_, Err(e)) => {
            eprintln!("broker_index_bench: {e}");
            return ExitCode::from(2);
        }
    };
    let dir = std::env::temp_dir().join(format!("asindex_{}.noindex", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("broker_index_bench: {}: {e}", dir.display());
        return ExitCode::FAILURE;
    }
    let _cleanup = Cleanup(dir.clone());
    let (mut most, mut most_peak): (f64, f64) = (0.0, 0.0);
    for n in counts {
        match run(&dir, shape, n) {
            Ok((per_record, peak)) => {
                most = most.max(per_record);
                most_peak = most_peak.max(peak);
            }
            Err(e) => {
                eprintln!("broker_index_bench: {n} records: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    if shape == Shape::Filler {
        println!("METRIC broker_index_bytes_per_record {most:.2}");
        println!("METRIC broker_open_peak_bytes_per_record {most_peak:.2}");
    }
    ExitCode::SUCCESS
}
