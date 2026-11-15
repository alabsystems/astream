//! Held-tail work bounds and independent whole-delivery controls.
use super::*;
use crate::retention::{Held, Retention, Rule};
use crate::test_scratch::Scratch;
use std::cell::Cell;

thread_local! { static VISITS: Cell<usize> = const { Cell::new(0) }; }
pub(super) fn visit() {
    VISITS.with(|n| n.set(n.get().saturating_add(1)));
}
fn take_visits() -> usize {
    VISITS.with(|n| n.replace(0))
}

fn held_record(off: u64, subject: &str) -> Held {
    Held {
        rec: Arc::new(BrokerRecord {
            seq: Offset(off),
            producer_id: 1,
            producer_seq: off,
            subject: subject.into(),
            body: vec![b'x'; 16],
            commit: None,
        }),
        at_ms: 0,
        bt_ms: None,
    }
}

/// Actual retention carries the prefix before a retained suffix is appended.
fn retained_fixture(n: usize) -> (Scratch, BrokerLog) {
    let root = Scratch::new("held-tail-bound");
    let mut log = BrokerLog::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
    log.set_retention(
        Retention::new(
            vec![
                Rule::prefix("/stream").unwrap().max_bytes(1),
                Rule::hold("/held/>").unwrap().max_bytes(1 << 30),
            ],
            Rule::default_hold(),
        )
        .unwrap(),
    )
    .unwrap();
    for i in 0..n as u64 {
        log.stage_publish(1, i, "/held/other".into(), vec![b'x'; 16])
            .unwrap();
    }
    log.stage_publish(1, n as u64, "/stream".into(), vec![b'x'; 16])
        .unwrap();
    log.commit_batch().unwrap();
    log.retain_by_rules(1).unwrap();
    assert_eq!(log.hold.entries.len(), n);
    assert_eq!(log.base.0, n as u64 + 1);
    assert_subject_presence(&log);
    log.stage_publish(1, n as u64 + 1, "/held/mine".into(), b"tail".to_vec())
        .unwrap();
    log.stage_publish(1, n as u64 + 2, "/held/other".into(), b"tail".to_vec())
        .unwrap();
    log.commit_batch().unwrap();
    (root, log)
}

/// Independent full scan: no paging or budget calculation from the implementation.
fn whole(
    log: &BrokerLog,
    from: u64,
    head: u64,
    filter: &Filter,
    also: Option<u64>,
) -> Vec<Arc<BrokerRecord>> {
    let wanted = |r: &BrokerRecord| {
        also == Some(r.seq.0) || (!is_hidden_record(r) && filter.matches_str(&r.subject))
    };
    let mut out = Vec::new();
    for (_, h) in log.hold.range(from, log.base.0.min(head)) {
        if wanted(&h.rec) {
            out.push(h.rec.clone());
        }
    }
    let start = from.max(log.base.0);
    if start < head {
        for r in log.read_range(Offset(start), usize::try_from(head - start).unwrap()) {
            if wanted(&r) {
                out.push(r);
            }
        }
    }
    out
}

fn paged(
    log: &BrokerLog,
    from: u64,
    head: u64,
    filter: &Filter,
    also: Option<u64>,
    max: usize,
) -> Vec<Arc<BrokerRecord>> {
    let mut cursor = from;
    let mut out = Vec::new();
    while cursor < head {
        let before = cursor;
        take_visits();
        let TailStep::Chunk {
            records,
            scanned_to,
        } = log.read_tail_chunk(&mut cursor, head, filter, also, max)
        else {
            panic!("fixture must be readable");
        };
        assert!(take_visits() <= max.max(1));
        if records.is_empty() {
            assert_eq!(cursor, scanned_to, "empty steps advance the cursor");
        } else {
            let held = records.first().is_some_and(|r| r.seq.0 < log.base.0);
            let expected = if held { before } else { before.max(log.base.0) };
            assert_eq!(
                cursor, expected,
                "queued rows retain the delivery cursor, after any pruned-base clamp"
            );
        }
        out.extend(records);
        cursor = cursor.max(scanned_to);
        assert!(
            cursor > before && cursor <= head,
            "progress stays under pinned head"
        );
    }
    out
}

#[test]
fn held_tail_bound_counts_hidden_and_nonmatching_entries() {
    let (_root, mut log) = retained_fixture(258);
    // Controlled public-record edge: hidden rows and the forced fork record use
    // the same traversal budget as ordinary held mail.
    log.hold.insert(held_record(1, "/a/commit"));
    log.hold.insert(held_record(257, "/held/mine"));
    let scan_head = 257;
    let filter = Filter::new("/held/mine").unwrap();
    for max in [0, 1, 2, 7, 64] {
        let mut cursor = 0;
        take_visits();
        let TailStep::Chunk {
            records,
            scanned_to,
        } = log.read_tail_chunk(&mut cursor, scan_head, &filter, None, max)
        else {
            panic!()
        };
        assert!(records.is_empty());
        assert_eq!(take_visits(), max.max(1));
        assert_eq!(cursor, max.max(1) as u64);
        assert_eq!(scanned_to, cursor);
    }
    // The former output-counted loop examines every row for this same no-match read.
    let mut old_visits = 0;
    let mut old_out = Vec::new();
    for (_, h) in log.hold.range(0, scan_head) {
        old_visits += 1;
        if is_hidden_record(&h.rec) || !filter.matches_str(&h.rec.subject) {
            continue;
        }
        if !old_out.is_empty() {
            break;
        }
        old_out.push(h.rec.clone());
    }
    assert_eq!(old_visits, 257);
    assert!(old_out.is_empty());
}

#[test]
fn held_tail_paging_matches_whole_scan_across_holes_heads_and_forced_rows() {
    let (_root, mut log) = retained_fixture(257);
    log.hold.insert(held_record(129, "/held/mine"));
    log.hold.insert(held_record(7, "/a/commit"));
    // Sparse absolute offsets must not turn holes into skipped held records.
    for off in (10..120).step_by(3) {
        log.hold.remove_entry(off);
    }
    let heads = [1, 8, 64, 128, 130, 257, log.base.0, log.head().0];
    for pat in ["/held/mine", "/held/>", "/absent", "/>"] {
        let filter = Filter::new(pat).unwrap();
        for head in heads {
            for from in [0, 7, 63, 128, 129, 256].into_iter().filter(|f| *f < head) {
                for also in [None, Some(7), Some(64), Some(129), Some(257)] {
                    let expected = whole(&log, from, head, &filter, also);
                    for max in [0, 1, 2, 7, 64, 256, 4096] {
                        assert_eq!(
                            paged(&log, from, head, &filter, also, max),
                            expected,
                            "{pat} from{from} head{head} also{also:?} max{max}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn held_tail_at_or_past_a_pinned_head_never_rewinds() {
    let (_root, log) = retained_fixture(17);
    let filter = Filter::new("/>").unwrap();
    for head in [0, 1, 8, log.base.0, log.head().0] {
        for start in [head, head.saturating_add(1), u64::MAX] {
            let mut cursor = start;
            take_visits();
            let TailStep::Chunk {
                records,
                scanned_to,
            } = log.read_tail_chunk(&mut cursor, head, &filter, None, 1)
            else {
                panic!()
            };
            assert!(records.is_empty());
            assert_eq!((cursor, scanned_to, take_visits()), (start, start, 0));
        }
    }
}

// Frozen pre-change whole method: retained-tail behavior is also independent.
impl BrokerLog {
    fn read_tail_chunk_reference(
        &self,
        cursor: &mut u64,
        head: u64,
        filter: &Filter,
        also_at: Option<u64>,
        max: usize,
    ) -> TailStep {
        let max_scan = max.max(1);
        #[cfg(feature = "retention")]
        if *cursor < self.base.0 {
            let mut out = Vec::new();
            let hold_end = self.base.0.min(head);
            let mut scanned_to = hold_end;
            for (&off, h) in self.hold.range(*cursor, hold_end) {
                visit();
                let is_also = match also_at {
                    Some(a) => a == off,
                    None => false,
                };
                if !is_also && (is_hidden_record(&h.rec) || !filter.matches_str(&h.rec.subject)) {
                    continue;
                }
                if out.len() >= max_scan {
                    scanned_to = off;
                    break;
                }
                out.push(Arc::clone(&h.rec));
            }
            if !out.is_empty() {
                return TailStep::Chunk {
                    records: out,
                    scanned_to,
                };
            }
            if head <= self.base.0 {
                *cursor = hold_end;
                return TailStep::Chunk {
                    records: Vec::new(),
                    scanned_to: hold_end,
                };
            }
        }
        let head = head.min(self.next.0);
        if *cursor >= head {
            return TailStep::Chunk {
                records: Vec::new(),
                scanned_to: *cursor,
            };
        }
        if head <= self.base.0 {
            *cursor = head;
            return TailStep::Chunk {
                records: Vec::new(),
                scanned_to: head,
            };
        }
        *cursor = (*cursor).max(self.base.0);
        let len = self.tier.len();
        let from = (*cursor).saturating_sub(self.base.0).min(len as u64) as usize;
        let end_rel = head.saturating_sub(self.base.0).min(len as u64) as usize;
        let to = from.saturating_add(max_scan).min(end_rel);
        let base = self.base.0;
        let mut out = Vec::new();
        // `also_at`'s record is read in its place whatever the filter says of it.
        let mut also = also_at
            .and_then(|a| usize::try_from(a.checked_sub(base)?).ok())
            .filter(|a| (from..to).contains(a));
        // The records the filter matches, a page that names no subject it matches passed
        // whole; a record whose summary cannot be read is wanted too, and its read decides.
        let mut met = self
            .tier
            .passing(from, to, |s| filter.matches_str(s))
            .map(crate::tier::Met::index);
        let mut next_met = met.next();
        loop {
            let i = match (also, next_met) {
                (Some(a), Some(m)) => {
                    if a <= m {
                        also = None;
                        if a == m {
                            next_met = met.next();
                        }
                        a
                    } else {
                        next_met = met.next();
                        m
                    }
                }
                (Some(a), None) => {
                    also = None;
                    a
                }
                (None, Some(m)) => {
                    next_met = met.next();
                    m
                }
                (None, None) => break,
            };
            let off = base.saturating_add(i as u64);
            let Some(rec) = self.record_arc(i) else {
                if out.is_empty() {
                    return TailStep::Unreadable(off);
                }
                // The step ends before the record it cannot read, which the next one reads
                // again.
                return TailStep::Chunk {
                    records: out,
                    scanned_to: off,
                };
            };
            out.push(rec);
        }
        // Every record of the step's range was passed.
        let scanned_to = if from < to {
            base.saturating_add(to as u64)
        } else {
            *cursor
        };
        if out.is_empty() {
            *cursor = scanned_to;
        }
        TailStep::Chunk {
            records: out,
            scanned_to,
        }
    }
}

#[test]
fn held_tail_full_reference_delivers_identical_records() {
    let (_root, mut log) = retained_fixture(257);
    log.hold.insert(held_record(129, "/held/mine"));
    log.hold.insert(held_record(7, "/a/commit"));
    for pat in ["/held/mine", "/held/>", "/absent", "/>"] {
        let filter = Filter::new(pat).unwrap();
        for max in [0, 1, 7, 64, 4096] {
            for also in [None, Some(7), Some(64), Some(129)] {
                let mut at = 0;
                let mut old = Vec::new();
                while at < log.head().0 {
                    let TailStep::Chunk {
                        records,
                        scanned_to,
                    } = log.read_tail_chunk_reference(&mut at, log.head().0, &filter, also, max)
                    else {
                        panic!()
                    };
                    old.extend(records);
                    at = at.max(scanned_to);
                }
                assert_eq!(paged(&log, 0, log.head().0, &filter, also, max), old);
            }
        }
    }
}

#[test]
#[ignore = "manual alternating native held-tail work benchmark"]
fn held_tail_bound_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    fn run(
        log: &BrokerLog,
        filter: &Filter,
        max: usize,
        old: bool,
        whole: bool,
        reps: usize,
    ) -> (u128, usize) {
        let begin = Instant::now();
        let mut output_capacity = 0;
        for _ in 0..reps {
            let mut at = 0;
            let mut checksum = 0u64;
            loop {
                let step = if old {
                    log.read_tail_chunk_c90(&mut at, log.head().0, filter, black_box(None), max)
                } else {
                    log.read_tail_chunk(&mut at, log.head().0, filter, black_box(None), max)
                };
                let TailStep::Chunk {
                    records,
                    scanned_to,
                } = step
                else {
                    panic!()
                };
                output_capacity = output_capacity.max(records.capacity());
                for r in records {
                    checksum = checksum.wrapping_add(r.seq.0.wrapping_add(1));
                }
                at = at.max(scanned_to);
                if !whole || at >= log.head().0 {
                    break;
                }
            }
            black_box((checksum, at));
        }
        (begin.elapsed().as_nanos() / reps as u128, output_capacity)
    }
    for n in [0usize, 64, 4096, 65_536] {
        let (_root, mut log) = retained_fixture(n);
        // A periodic sparse lane exposes chunk/Vec churn as well as late matches.
        for off in (0..n as u64).step_by(67) {
            log.hold.insert(held_record(off, "/held/periodic"));
        }
        // Keep a separate late matching held row.
        if n != 0 {
            log.hold.insert(held_record((n - 1) as u64, "/held/mine"));
        }
        assert_subject_presence(&log);
        for (name, pat) in [
            ("none", "/absent"),
            ("sparse", "/held/mine"),
            ("periodic", "/held/periodic"),
            ("all", "/held/>"),
            ("wild_absent", "/held/missing/*"),
            ("suffix_only", "/held/suffix"),
        ] {
            if name == "suffix_only" {
                log.publish(2, 0, "/held/suffix".into(), b"suffix only".to_vec())
                    .unwrap();
            }
            let filter = Filter::new(pat).unwrap();
            for max in [64, 4096] {
                for whole in [false, true] {
                    let inspect_outputs = |old: bool| {
                        let mut at = 0;
                        let mut vectors = 0usize;
                        let mut count = 0usize;
                        let mut checksum = 0u64;
                        loop {
                            let step = if old {
                                log.read_tail_chunk_c90(
                                    &mut at,
                                    log.head().0,
                                    &filter,
                                    black_box(None),
                                    max,
                                )
                            } else {
                                log.read_tail_chunk(
                                    &mut at,
                                    log.head().0,
                                    &filter,
                                    black_box(None),
                                    max,
                                )
                            };
                            let TailStep::Chunk {
                                records,
                                scanned_to,
                            } = step
                            else {
                                panic!()
                            };
                            vectors += usize::from(records.capacity() != 0);
                            count += records.len();
                            for r in records {
                                checksum = checksum.wrapping_add(r.seq.0.wrapping_add(1));
                            }
                            at = at.max(scanned_to);
                            if !whole || at >= log.head().0 {
                                break;
                            }
                        }
                        (vectors, count, checksum, at)
                    };
                    let old_outputs = inspect_outputs(true);
                    let new_outputs = inspect_outputs(false);
                    if whole {
                        assert_eq!(
                            (old_outputs.1, old_outputs.2, old_outputs.3),
                            (new_outputs.1, new_outputs.2, new_outputs.3),
                            "whole catch-up parity"
                        );
                    }
                    let reps = if whole || n == 65_536 { 30 } else { 120 };
                    for old in [true, false] {
                        black_box(run(&log, &filter, max, old, whole, 2));
                    }
                    let mut old_samples = Vec::new();
                    let mut new_samples = Vec::new();
                    let mut caps = [0, 0];
                    for round in 0..8 {
                        for old in if round % 2 == 0 {
                            [true, false]
                        } else {
                            [false, true]
                        } {
                            let (ns, cap) = run(&log, &filter, max, old, whole, reps);
                            caps[usize::from(!old)] = cap;
                            if old {
                                old_samples.push(ns);
                            } else {
                                new_samples.push(ns);
                            }
                        }
                    }
                    old_samples.sort_unstable();
                    new_samples.sort_unstable();
                    let before = (old_samples[3] + old_samples[4]) / 2;
                    let after = (new_samples[3] + new_samples[4]) / 2;
                    println!("HELD_TAIL n={n} pattern={name} max={max} whole={whole} old_ns={before} new_ns={after} speedup={:.4} old_capacity={} new_capacity={} old_vectors={} new_vectors={} samples_old={old_samples:?} samples_new={new_samples:?}", before as f64 / after as f64, caps[0], caps[1], old_outputs.0, new_outputs.0);
                }
            }
        }
    }
}

#[test]
fn held_tail_yields_before_an_unreadable_retained_suffix_without_skipping_it() {
    use std::io::{Seek, SeekFrom, Write};
    let (root, mut log) = retained_fixture(17);
    log.set_resident_budget(0);
    let base = log.base.0;
    let bad_at = log.frame_at_for_test(0).unwrap();
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .open(root.path().join("log"))
        .unwrap();
    file.seek(SeekFrom::Start(bad_at + 16)).unwrap();
    file.write_all(&[0xde, 0xad, 0xbe, 0xef]).unwrap();
    file.sync_all().unwrap();
    let filter = Filter::new("/*/mine").unwrap();
    let mut cursor = 0;
    while cursor < base {
        let before = cursor;
        let TailStep::Chunk {
            records,
            scanned_to,
        } = log.read_tail_chunk(&mut cursor, log.head().0, &filter, None, 3)
        else {
            panic!("held chunk must yield before cold suffix");
        };
        assert!(records.is_empty());
        assert!(cursor > before && cursor <= base);
        assert_eq!(cursor, scanned_to);
    }
    assert!(
        matches!(log.read_tail_chunk(&mut cursor, log.head().0, &filter, None, 3), TailStep::Unreadable(off) if off == base)
    );
    assert_eq!(cursor, base);
    assert!(
        matches!(log.read_tail_chunk_reference(&mut cursor, log.head().0, &filter, None, 3), TailStep::Unreadable(off) if off == base)
    );
    let exact = Filter::new("/held/mine").unwrap();
    let mut exact_cursor = 0;
    take_visits();
    assert!(
        matches!(log.read_tail_chunk(&mut exact_cursor, log.head().0, &exact, None, 3), TailStep::Unreadable(off) if off == base)
    );
    assert_eq!((exact_cursor, take_visits()), (base, 0));
}

// Frozen bounded c90 baseline, before exact-subject absence was consulted.
impl BrokerLog {
    fn read_tail_chunk_c90(
        &self,
        cursor: &mut u64,
        head: u64,
        filter: &Filter,
        also_at: Option<u64>,
        max: usize,
    ) -> TailStep {
        let max_scan = max.max(1);
        // A pinned snapshot can end below the current retention base. Never move
        // a cursor that already reached its head backwards while checking held rows.
        if *cursor >= head {
            return TailStep::Chunk {
                records: Vec::new(),
                scanned_to: *cursor,
            };
        }
        #[cfg(feature = "retention")]
        if *cursor < self.base.0 {
            let mut out = Vec::new();
            let hold_end = self.base.0.min(head);
            let mut scanned_to = *cursor;
            let mut inspected = 0usize;
            for (&off, h) in self.hold.range(*cursor, hold_end).take(max_scan) {
                inspected = inspected.saturating_add(1);
                scanned_to = off.saturating_add(1);
                #[cfg(test)]
                visit();
                let is_also = match also_at {
                    Some(a) => a == off,
                    None => false,
                };
                if !is_also && (is_hidden_record(&h.rec) || !filter.matches_str(&h.rec.subject)) {
                    continue;
                }
                out.push(Arc::clone(&h.rec));
            }
            if inspected != 0 {
                // Fewer than the budget means the range was exhausted; pruned
                // holes cost no work. A full step stops after its last inspected
                // row, without peeking at or skipping an uninspected entry.
                if inspected < max_scan {
                    scanned_to = hold_end;
                }
                if out.is_empty() {
                    *cursor = scanned_to;
                }
                // Yield after held work even when it matched nothing. Spending
                // another full budget on the retained suffix would break the bound.
                return TailStep::Chunk {
                    records: out,
                    scanned_to,
                };
            }
            if head <= self.base.0 {
                *cursor = hold_end;
                return TailStep::Chunk {
                    records: Vec::new(),
                    scanned_to: hold_end,
                };
            }
        }
        let head = head.min(self.next.0);
        if *cursor >= head {
            return TailStep::Chunk {
                records: Vec::new(),
                scanned_to: *cursor,
            };
        }
        if head <= self.base.0 {
            *cursor = head;
            return TailStep::Chunk {
                records: Vec::new(),
                scanned_to: head,
            };
        }
        *cursor = (*cursor).max(self.base.0);
        let len = self.tier.len();
        let from = (*cursor).saturating_sub(self.base.0).min(len as u64) as usize;
        let end_rel = head.saturating_sub(self.base.0).min(len as u64) as usize;
        let to = from.saturating_add(max_scan).min(end_rel);
        let base = self.base.0;
        let mut out = Vec::new();
        // `also_at`'s record is read in its place whatever the filter says of it.
        let mut also = also_at
            .and_then(|a| usize::try_from(a.checked_sub(base)?).ok())
            .filter(|a| (from..to).contains(a));
        // The records the filter matches, a page that names no subject it matches passed
        // whole; a record whose summary cannot be read is wanted too, and its read decides.
        let mut met = self
            .tier
            .passing(from, to, |s| filter.matches_str(s))
            .map(crate::tier::Met::index);
        let mut next_met = met.next();
        loop {
            let i = match (also, next_met) {
                (Some(a), Some(m)) => {
                    if a <= m {
                        also = None;
                        if a == m {
                            next_met = met.next();
                        }
                        a
                    } else {
                        next_met = met.next();
                        m
                    }
                }
                (Some(a), None) => {
                    also = None;
                    a
                }
                (None, Some(m)) => {
                    next_met = met.next();
                    m
                }
                (None, None) => break,
            };
            let off = base.saturating_add(i as u64);
            let Some(rec) = self.record_arc(i) else {
                if out.is_empty() {
                    return TailStep::Unreadable(off);
                }
                // The step ends before the record it cannot read, which the next one reads
                // again.
                return TailStep::Chunk {
                    records: out,
                    scanned_to: off,
                };
            };
            out.push(rec);
        }
        // Every record of the step's range was passed.
        let scanned_to = if from < to {
            base.saturating_add(to as u64)
        } else {
            *cursor
        };
        if out.is_empty() {
            *cursor = scanned_to;
        }
        TailStep::Chunk {
            records: out,
            scanned_to,
        }
    }
}

fn assert_subject_presence(log: &BrokerLog) {
    for subject in [
        "/held/other",
        "/held/mine",
        "/held/new",
        "/held/periodic",
        "/held/suffix",
        "/a/commit",
        "/absent",
    ] {
        let expected = log.hold.entries.values().any(|h| h.rec.subject == subject);
        assert_eq!(
            log.hold.holds_subject(subject),
            expected,
            "subject index {subject}"
        );
    }
    for h in log.hold.entries.values() {
        assert!(
            log.hold.holds_subject(&h.rec.subject),
            "no held row may be absent from the index"
        );
    }
}

#[test]
fn exact_held_absence_skips_only_to_the_pinned_head_and_reads_the_suffix() {
    let (_root, log) = retained_fixture(257);
    let filter = Filter::new("/held/mine").unwrap();
    assert!(!log.hold.holds_subject(filter.as_str()));
    for max in [0, 1, 64, 4096] {
        for head in [1, 7, 64, 257, log.base.0] {
            let mut cursor = 0;
            take_visits();
            let TailStep::Chunk {
                records,
                scanned_to,
            } = log.read_tail_chunk(&mut cursor, head, &filter, None, max)
            else {
                panic!()
            };
            assert!(records.is_empty());
            assert_eq!((cursor, scanned_to, take_visits()), (head, head, 0));
        }
        let mut cursor = 0;
        take_visits();
        let TailStep::Chunk {
            records,
            scanned_to,
        } = log.read_tail_chunk(&mut cursor, log.head().0, &filter, None, max)
        else {
            panic!()
        };
        assert_eq!(
            records.iter().map(|r| r.seq.0).collect::<Vec<_>>(),
            vec![log.base.0]
        );
        assert_eq!(
            cursor, log.base.0,
            "retained rows await delivery after the base clamp"
        );
        assert_eq!(take_visits(), 0);
        assert!(scanned_to > cursor && scanned_to <= log.head().0);
    }
}

#[test]
fn forced_rows_and_wildcards_keep_the_bounded_held_scan() {
    let (_root, log) = retained_fixture(257);
    let exact = Filter::new("/held/mine").unwrap();
    assert!(!log.hold.holds_subject(exact.as_str()));
    let mut cursor = 0;
    take_visits();
    let TailStep::Chunk {
        records,
        scanned_to,
    } = log.read_tail_chunk(&mut cursor, log.head().0, &exact, Some(64), 64)
    else {
        panic!()
    };
    assert!(records.is_empty());
    assert_eq!((cursor, scanned_to, take_visits()), (64, 64, 64));
    take_visits();
    let TailStep::Chunk {
        records,
        scanned_to,
    } = log.read_tail_chunk(&mut cursor, log.head().0, &exact, Some(64), 64)
    else {
        panic!()
    };
    assert_eq!(
        records.iter().map(|r| r.seq.0).collect::<Vec<_>>(),
        vec![64]
    );
    assert_eq!((cursor, scanned_to, take_visits()), (64, 128, 64));
    let wildcard = Filter::new("/held/missing/*").unwrap();
    let mut cursor = 0;
    take_visits();
    let TailStep::Chunk {
        records,
        scanned_to,
    } = log.read_tail_chunk(&mut cursor, log.head().0, &wildcard, None, 64)
    else {
        panic!()
    };
    assert!(records.is_empty());
    assert_eq!((cursor, scanned_to, take_visits()), (64, 64, 64));
}

#[test]
fn held_subject_presence_tracks_replacements_and_last_removals() {
    let (_root, mut log) = retained_fixture(4);
    assert_subject_presence(&log);
    for (off, subject) in [
        (0, "/held/new"),
        (1, "/held/new"),
        (0, "/held/new"),
        (0, "/held/mine"),
        (2, "/held/mine"),
    ] {
        log.hold.insert(held_record(off, subject));
        assert_subject_presence(&log);
    }
    log.hold.remove_entry(1);
    assert!(!log.hold.holds_subject("/held/new"));
    assert_subject_presence(&log);
    log.hold.remove_entry(0);
    assert!(log.hold.holds_subject("/held/mine"));
    assert_subject_presence(&log);
    log.hold.remove_entry(2);
    assert!(!log.hold.holds_subject("/held/mine"));
    log.hold.remove_entry(u64::MAX);
    assert_subject_presence(&log);
}

#[test]
fn real_retention_recovery_and_removal_keep_exact_presence_sound() {
    use std::time::Duration;
    fn rules() -> Retention {
        Retention::new(
            vec![
                Rule::prefix("/stream").unwrap().max_bytes(1),
                Rule::hold("/held/>")
                    .unwrap()
                    .max_bytes(1 << 30)
                    .max_age(Duration::from_millis(10)),
            ],
            Rule::default_hold(),
        )
        .unwrap()
    }
    fn pair(log: &mut BrokerLog, seq: u64) {
        log.stage_publish(1, seq, "/held/mine".into(), vec![b'x'; 16])
            .unwrap();
        log.stage_publish(1, seq + 1, "/stream".into(), vec![b'x'; 16])
            .unwrap();
        log.commit_batch().unwrap();
    }
    let root = Scratch::new("held-exact-reopen");
    let path = root.path().join("log");
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    log.set_retention(rules()).unwrap();
    pair(&mut log, 0);
    log.retain_by_rules(1).unwrap();
    pair(&mut log, 2);
    log.retain_by_rules(5).unwrap();
    assert_eq!(
        log.hold.entries.keys().copied().collect::<Vec<_>>(),
        vec![0, 2]
    );
    drop(log);
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    assert_subject_presence(&log);
    assert!(log.hold.holds_subject("/held/mine"));
    let exact = Filter::new("/held/mine").unwrap();
    assert_eq!(
        paged(&log, 0, log.head().0, &exact, None, 1)
            .iter()
            .map(|r| r.seq.0)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    log.set_retention(rules()).unwrap();
    assert_eq!(log.retain_by_rules(12).unwrap().released, 1);
    assert_eq!(
        log.hold.entries.keys().copied().collect::<Vec<_>>(),
        vec![2]
    );
    assert_subject_presence(&log);
    drop(log);
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    assert!(log.hold.holds_subject("/held/mine"));
    log.set_retention(rules()).unwrap();
    assert_eq!(log.retain_by_rules(16).unwrap().released, 1);
    assert!(!log.hold.holds_subject("/held/mine"));
    assert_subject_presence(&log);
    drop(log);
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    assert!(!log.hold.holds_subject("/held/mine"));
    let (off, _) = log
        .publish(1, 4, "/held/mine".into(), b"retained".to_vec())
        .unwrap();
    let mut cursor = 0;
    take_visits();
    let TailStep::Chunk {
        records,
        scanned_to,
    } = log.read_tail_chunk(&mut cursor, log.head().0, &exact, None, 1)
    else {
        panic!()
    };
    assert_eq!(records.iter().map(|r| r.seq).collect::<Vec<_>>(), vec![off]);
    assert_eq!(take_visits(), 0);
    assert_eq!((cursor, scanned_to), (log.base.0, off.0 + 1));
}
