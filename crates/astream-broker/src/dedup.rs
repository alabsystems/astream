// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The exactly-once ingest index: `(producer_id, producer_seq) -> Offset` for every retained
//! produce, exact, at a few bytes a record.
//!
//! The contract is the PRECISE pair (`store.rs`'s head): a producer may re-send an old seq
//! after a crash, so no per-producer high-water mark can stand in for it, and the index must
//! answer every question a `HashMap<(u64, u64), Offset>` answered before it: a retained key's
//! original offset, its absence once retention cut its record, the count of keys, and an
//! insert of a key already held replaces its offset (a replica that holds a key twice,
//! because its retention kept an old record its leader pruned and then re-took, answers with
//! the newer, as the map did).
//!
//! The map paid one hash entry a record (a 24-byte entry and its control byte, about 52 B a
//! record by its fill; `docs/DESIGN-aterm-fabric.md` §14 open question 8). Producers mostly
//! publish consecutive seqs, so a producer's keys are PACKED once a contiguous run
//! reaches `PACK_MIN` keys: it keeps every key from then on sorted by seq in chunks of at most `CHUNK`
//! keys, each chunk as maximal runs of consecutive seqs (`Run`: the run's first seq and where
//! its entries start, 16 B) and one offset per key as a `u32` from the chunk's base. A
//! producer that publishes `1, 2, 3, …` costs 4 B a record and its chunks' headers under a
//! tenth of a byte more; a sparse key beside its runs (an ack's `ACK_SEQ_BASE | input`, which
//! a processor publishes under the id it publishes with) is a run of one, 20 B. A producer
//! none of whose keys neighbour keeps each LOOSE, one hash entry as the map's was, so a
//! producer that publishes a key or two (`asb pub` with no `--id`) costs what the map cost
//! and no more. Short producers stay loose until their run justifies a packed
//! directory's allocations. Every key lives in exactly one store; each loose run is
//! shorter than `PACK_MIN`, and inserts into packed producers absorb adjacent loose runs.
//!
//! WHAT IS EXACT, AND WHAT IS ONLY FAST. Exactness never depends on how seqs or offsets
//! arrive: every key is placed by its seq, a lookup searches its producer's chunks and runs and
//! then the loose keys, and a retention cut drops exactly the keys whose offsets lie below it. The chunk bounds
//! what an insert inside the order costs (a second stream under one id, such as a
//! processor's acks above its publishes, or a re-sent old seq): it moves at most a chunk's
//! offsets and runs, and a full chunk splits in halves. What depends on the broker's order
//! (every insert at the log's head, so above every offset held) is a cut's speed: then a
//! chunk's offsets increase in seq order (`Chunk::ordered`) and a cut drops a prefix of it;
//! any other chunk is filtered through at most a chunk's keys of scratch. A chunk whose
//! offsets span more than `u32::MAX` keeps them as `u64`s (`Offs::Wide`), so no span is
//! ever wrong.
//!
//! Each chunk also keeps conservative inclusive offset bounds (16 B per chunk).
//! Retention skips chunks wholly above the cut and clears chunks wholly below it,
//! without searching their offsets. Only overlapping unordered chunks need filtering;
//! an unsuccessful scan tightens the lower bound to avoid repeated work at that floor.
//! Replacements widen bounds rather than rescanning, so retries remain constant work
//! beyond their existing lookup and update. Stale bounds can only cause extra work.
//!
//! Chunk directories start flat. Once a backfill or interleaved stream would shift
//! 64 chunk headers, end-heavy edits move to a boxed ring directory. Its cheaper
//! end is used until an interior edit would move 64 headers from either end; that
//! promotes to a B-tree keyed by first seq. Append-only producers retain their
//! contiguous flat directories. Arbitrary-order directory inserts become
//! logarithmic, while local offset/run edits remain chunk-bounded.
//! Growing consecutive runs split away from later runs at their boundary once
//! they occupy half a chunk, avoiding repeated shifts of an interleaved ACK tail.

use astream_wire::Offset;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::ops::Bound::{Excluded, Unbounded};

/// The most keys a chunk holds: what an insert inside the order moves at most (its offsets
/// and its runs), and what a cut's filter of a chunk copies at most. A full chunk's header
/// and its run cost under a tenth of a byte a key.
const CHUNK: usize = 1024;

/// Below this contiguous-run length, packing costs more than hash entries for a
/// short producer. A bound on startup probes and the keys migrated on promotion.
const PACK_MIN: usize = 8;
// Tests compare larger startup thresholds without widening production's scratch.
#[cfg(test)]
const PACK_CAP: usize = 16;
#[cfg(not(test))]
const PACK_CAP: usize = PACK_MIN;

fn pack_min() -> usize {
    #[cfg(test)]
    {
        tally::pack_min()
    }
    #[cfg(not(test))]
    {
        PACK_MIN
    }
}

/// The contiguous loose run around a new key, excluding that key. Runs are always
/// shorter than the packing threshold, so at most PACK_MIN - 1 keys lie on either
/// side. Stop at the first miss; isolated keys cost only the two adjacent probes.
fn loose_run(loose: &HashMap<(u64, u64), u64>, pid: u64, seq: u64) -> (usize, usize) {
    let mut left = 0;
    let mut right = 0;
    for d in 1..pack_min() {
        let Some(before) = seq.checked_sub(d as u64) else {
            break;
        };
        if !loose.contains_key(&(pid, before)) {
            break;
        }
        left = d;
    }
    for d in 1..pack_min() {
        let Some(after) = seq.checked_add(d as u64) else {
            break;
        };
        if !loose.contains_key(&(pid, after)) {
            break;
        }
        right = d;
    }
    (left, right)
}

/// The chunk size in force: `CHUNK`, which a test may lower on its own thread so that a
/// short stream crosses chunk boundaries.
fn chunk_cap() -> usize {
    #[cfg(test)]
    {
        tally::chunk_cap()
    }
    #[cfg(not(test))]
    {
        CHUNK
    }
}

/// A maximal run of consecutive producer seqs: `seq0, seq0 + 1, …`, whose offsets are
/// `Chunk::offs[at..]` up to the next run's `at`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Run {
    seq0: u64,
    at: usize,
}

/// One chunk's offsets, one per key, in seq order.
#[derive(Debug)]
enum Offs {
    /// Each offset as its distance from `base`, which is at or below every one.
    Narrow { base: u64, v: Vec<u32> },
    /// Offsets spanning more than `u32::MAX`, kept whole.
    Wide(Vec<u64>),
}

impl Offs {
    /// The `n` offsets `all` yields, narrow when their span fits a `u32`, at capacity `n`.
    fn of(all: impl Iterator<Item = u64> + Clone, n: usize) -> Offs {
        let mut lo = u64::MAX;
        let mut hi = 0u64;
        for o in all.clone() {
            lo = lo.min(o);
            hi = hi.max(o);
        }
        if lo > hi {
            return Offs::Narrow {
                base: 0,
                v: Vec::new(),
            };
        }
        let cap = if n <= 65_536 { n } else { 0 };
        if hi.saturating_sub(lo) > u64::from(u32::MAX) {
            let mut v = Vec::with_capacity(cap);
            v.extend(all);
            return Offs::Wide(v);
        }
        let mut v = Vec::with_capacity(cap);
        for o in all {
            v.push(Offs::narrow(lo, o));
        }
        Offs::Narrow { base: lo, v }
    }

    fn len(&self) -> usize {
        match self {
            Offs::Narrow { v, .. } => v.len(),
            Offs::Wide(v) => v.len(),
        }
    }

    fn get(&self, j: usize) -> Option<u64> {
        match self {
            Offs::Narrow { base, v } => match v.get(j) {
                Some(&d) => base.checked_add(u64::from(d)),
                None => None,
            },
            Offs::Wide(v) => v.get(j).copied(),
        }
    }

    /// Every offset, in seq order.
    fn to_vec(&self) -> Vec<u64> {
        let len = self.len();
        let mut out = if len <= 65_536 {
            Vec::with_capacity(len)
        } else {
            Vec::new()
        };
        for j in 0..self.len() {
            if let Some(o) = self.get(j) {
                out.push(o);
            }
        }
        out
    }

    /// Make room for `off`: a narrow list whose base or span cannot hold it is re-based on the
    /// least offset it would hold, or kept whole when even that span passes `u32::MAX`.
    fn fit(&mut self, off: u64) {
        let Offs::Narrow { base, v } = self else {
            return;
        };
        if off >= *base && off - *base <= u64::from(u32::MAX) {
            return;
        }
        let mut lo = off;
        let mut hi = off;
        for &d in v.iter() {
            let o = base.saturating_add(u64::from(d));
            lo = lo.min(o);
            hi = hi.max(o);
        }
        if hi.saturating_sub(lo) <= u64::from(u32::MAX) {
            let old = *base;
            let cap = v.capacity();
            let mut moved = if cap <= 65_536 {
                Vec::with_capacity(cap)
            } else {
                Vec::new()
            };
            for &d in v.iter() {
                // In range: `old + d` lies in `lo..=hi`, a span that fits a `u32`.
                let o = old.saturating_add(u64::from(d));
                moved.push(u32::try_from(o.saturating_sub(lo)).unwrap_or(u32::MAX));
            }
            *self = Offs::Narrow { base: lo, v: moved };
        } else {
            *self = Offs::Wide(self.to_vec());
        }
    }

    /// The narrow distance of `off` from `base`, which `fit` made representable.
    fn narrow(base: u64, off: u64) -> u32 {
        u32::try_from(off.saturating_sub(base)).unwrap_or(u32::MAX)
    }

    fn insert(&mut self, j: usize, off: u64) {
        self.fit(off);
        #[cfg(test)]
        tally::offset_moved(self.len().saturating_sub(j));
        match self {
            Offs::Narrow { base, v } => vec_insert_at(v, j, Offs::narrow(*base, off)),
            Offs::Wide(v) => vec_insert_at(v, j, off),
        }
    }

    fn set(&mut self, j: usize, off: u64) {
        self.fit(off);
        match self {
            Offs::Narrow { base, v } => {
                if let Some(slot) = v.get_mut(j) {
                    *slot = Offs::narrow(*base, off);
                }
            }
            Offs::Wide(v) => {
                if let Some(slot) = v.get_mut(j) {
                    *slot = off;
                }
            }
        }
    }

    /// Drop the first `k` offsets.
    #[cfg(any(test, feature = "retention"))]
    fn drain_front(&mut self, k: usize) {
        match self {
            Offs::Narrow { v, .. } => vec_drop_prefix(v, k),
            Offs::Wide(v) => vec_drop_prefix(v, k),
        }
    }

    fn shrink(&mut self, to: usize) {
        match self {
            Offs::Narrow { v, .. } => v.shrink_to(to),
            Offs::Wide(v) => v.shrink_to(to),
        }
    }

    /// The bytes the offsets' vector holds.
    #[cfg(test)]
    fn heap_bytes(&self) -> usize {
        match self {
            Offs::Narrow { v, .. } => v.capacity() * std::mem::size_of::<u32>(),
            Offs::Wide(v) => v.capacity() * std::mem::size_of::<u64>(),
        }
    }

    /// Whether the offsets strictly increase, in seq order.
    fn increasing(&self) -> bool {
        let mut prev: Option<u64> = None;
        for j in 0..self.len() {
            let o = self.get(j);
            if let (Some(p), Some(o)) = (prev, o) {
                if o <= p {
                    return false;
                }
            }
            prev = o;
        }
        true
    }
}

/// Whether `seq` is the seq after `prev`.
fn follows(prev: Option<u64>, seq: u64) -> bool {
    match prev {
        Some(p) => p.checked_add(1) == Some(seq),
        None => false,
    }
}

/// At most `chunk_cap()` of one producer's packed keys: a stretch of its seq order that no
/// other chunk of the producer overlaps.
#[derive(Debug)]
struct Chunk {
    /// Maximal runs of consecutive seqs within the chunk, sorted by `seq0`, disjoint, none
    /// empty (a run that crosses into the next chunk is two runs, one in each).
    runs: Vec<Run>,
    /// One offset per key, in seq order.
    offs: Offs,
    /// SOUND, not complete: when set, `offs` strictly increases in seq order, so a cut drops
    /// a prefix. Kept while every insert lands above every offset held before it in the
    /// chunk's order and below every one after it (a producer publishing increasing seqs on a
    /// log appending at its head).
    ordered: bool,
    /// The least seq held, `runs[0].seq0`, kept beside the header so that a search over a
    /// producer's chunks reads no run vector.
    first: u64,
    /// Conservative inclusive offset bounds. Replacements may leave them wider than
    /// necessary; inserts expand them, rebuilds make them exact, and cuts tighten lo.
    /// They certify whole-chunk retention decisions even when seq order is unrelated
    /// to offset order (backfills, replicated retries, and interleaved ack streams).
    offset_lo: u64,
    offset_hi: u64,
}

/// The standard Vec operations move a contiguous tail with memmove, preserving
/// ownership for non-Copy chunk headers. Keep the helpers' admitted edge semantics.
fn vec_insert_at<T>(v: &mut Vec<T>, idx: usize, val: T) {
    #[cfg(test)]
    if !tally::bulk_moves() {
        vec_insert_swap(v, idx, val);
        return;
    }
    if idx >= v.len() {
        v.push(val);
    } else {
        v.insert(idx, val);
    }
}

fn vec_remove_at<T>(v: &mut Vec<T>, idx: usize) -> Option<T> {
    if idx >= v.len() {
        return None;
    }
    #[cfg(test)]
    if !tally::bulk_moves() {
        return vec_remove_swap(v, idx);
    }
    Some(v.remove(idx))
}

/// Prefix removal is used only for Copy runs and offsets. copy_within preserves
/// survivor order and capacity without introducing any destructor-order change.
#[cfg(any(test, feature = "retention"))]
fn vec_drop_prefix<T: Copy>(v: &mut Vec<T>, k: usize) {
    let len = v.len();
    let drop_n = k.min(len);
    if drop_n == 0 {
        return;
    }
    #[cfg(test)]
    {
        tally::prefix_moved(len.saturating_sub(drop_n));
        if !tally::bulk_moves() {
            vec_drop_prefix_swap(v, k);
            return;
        }
    }
    if drop_n >= len {
        v.clear();
    } else {
        v.copy_within(drop_n..len, 0);
        v.truncate(len.saturating_sub(drop_n));
    }
}

#[cfg(test)]
fn vec_insert_swap<T>(v: &mut Vec<T>, idx: usize, val: T) {
    let at = idx.min(v.len());
    v.push(val);
    let mut cur = v.len().saturating_sub(1);
    while cur > at {
        let prev = cur.saturating_sub(1);
        if let Some(pair) = v.get_mut(prev..=cur) {
            if let Some((first, rest)) = pair.split_first_mut() {
                if let Some(second) = rest.last_mut() {
                    std::mem::swap(first, second);
                }
            }
        }
        cur = prev;
    }
}

#[cfg(test)]
fn vec_remove_swap<T>(v: &mut Vec<T>, idx: usize) -> Option<T> {
    if idx >= v.len() {
        return None;
    }
    let last_idx = v.len().saturating_sub(1);
    let mut cur = idx;
    while cur < last_idx {
        let next = cur.saturating_add(1);
        if let Some(pair) = v.get_mut(cur..=next) {
            if let Some((first, rest)) = pair.split_first_mut() {
                if let Some(second) = rest.last_mut() {
                    std::mem::swap(first, second);
                }
            }
        }
        cur = next;
    }
    v.pop()
}

#[cfg(test)]
fn vec_drop_prefix_swap<T: Copy>(v: &mut Vec<T>, k: usize) {
    let len = v.len();
    let drop_n = k.min(len);
    if drop_n == 0 {
        return;
    }
    let keep = len.saturating_sub(drop_n);
    for idx in 0..keep {
        let src = idx.saturating_add(drop_n);
        if let Some(sub) = v.get_mut(idx..=src) {
            if let Some((first, rest)) = sub.split_first_mut() {
                if let Some(end) = rest.last_mut() {
                    std::mem::swap(first, end);
                }
            }
        }
    }
    v.truncate(keep);
}

impl Chunk {
    /// The chunk holding `pairs`, `(seq, offset)` sorted by seq and distinct, at capacity.
    fn of(pairs: &[(u64, u64)]) -> Chunk {
        let mut n_runs = 0usize;
        let mut prev: Option<u64> = None;
        for &(seq, _) in pairs {
            if !follows(prev, seq) {
                n_runs = n_runs.saturating_add(1);
            }
            prev = Some(seq);
        }
        let cap = n_runs;
        let mut runs = if cap <= 65_536 {
            Vec::with_capacity(cap)
        } else {
            Vec::new()
        };
        prev = None;
        for (at, &(seq0, _)) in pairs.iter().enumerate() {
            if !follows(prev, seq0) {
                runs.push(Run { seq0, at });
            }
            prev = Some(seq0);
        }
        let offs = Offs::of(pairs.iter().map(|p| p.1), pairs.len());
        let ordered = offs.increasing();
        let first = match runs.first() {
            Some(r) => r.seq0,
            None => 0,
        };
        Chunk {
            runs,
            offs,
            ordered,
            first,
            offset_lo: pairs.iter().map(|p| p.1).min().unwrap_or(u64::MAX),
            offset_hi: pairs.iter().map(|p| p.1).max().unwrap_or(0),
        }
    }

    fn len(&self) -> usize {
        self.offs.len()
    }

    /// The least seq held (a chunk is never left empty).
    fn first_seq(&self) -> u64 {
        self.first
    }

    /// Re-read `first` after the runs changed at their front.
    fn refirst(&mut self) {
        if let Some(r) = self.runs.first() {
            self.first = r.seq0;
        }
    }

    /// The greatest seq held.
    fn last_seq(&self) -> u64 {
        match self.runs.last() {
            Some(r) => {
                let tail = self.len().saturating_sub(r.at).saturating_sub(1);
                r.seq0.saturating_add(tail as u64)
            }
            None => 0,
        }
    }

    /// Where run `i`'s entries end in `offs`.
    fn run_end(&self, i: usize) -> usize {
        match self.runs.get(i.saturating_add(1)) {
            Some(next) => next.at,
            None => self.offs.len(),
        }
    }

    /// Index into `offs` of `seq`, when held.
    fn slot(&self, seq: u64) -> Option<usize> {
        let i = self
            .runs
            .partition_point(|r| r.seq0 <= seq)
            .checked_sub(1)?;
        let run = self.runs.get(i)?;
        let k = usize::try_from(seq.checked_sub(run.seq0)?).ok()?;
        let j = run.at.checked_add(k)?;
        if j < self.run_end(i) {
            Some(j)
        } else {
            None
        }
    }

    /// Whether entry `j` is the last of its run.
    #[cfg(test)]
    fn ends_run(&self, j: usize) -> bool {
        match self.runs.partition_point(|r| r.at <= j).checked_sub(1) {
            Some(i) => j.saturating_add(1) == self.run_end(i),
            None => false,
        }
    }

    /// Whether `off` placed at index `j` keeps `offs` increasing, with `next` the index of
    /// the entry that would follow it.
    fn keeps_order(&self, j: usize, next: usize, off: u64) -> bool {
        let below = match j.checked_sub(1) {
            Some(p) => self.offs.get(p).is_some_and(|o| o < off),
            None => true,
        };
        let above = match self.offs.get(next) {
            Some(o) => off < o,
            None => true,
        };
        below && above
    }

    /// Shift every run from `from` on by one entry (a key was inserted before them).
    fn shift_from(&mut self, from: usize) {
        #[cfg(test)]
        tally::moved(self.runs.len().saturating_sub(from));
        for r in self.runs.iter_mut().skip(from) {
            r.at = r.at.saturating_add(1);
        }
    }

    /// Replace entry `j`'s offset.
    fn set(&mut self, j: usize, off: u64) {
        self.ordered = self.ordered && self.keeps_order(j, j.saturating_add(1), off);
        self.offs.set(j, off);
        self.offset_lo = self.offset_lo.min(off);
        self.offset_hi = self.offset_hi.max(off);
    }

    /// Insert `seq`, which the chunk does not hold, at `off`.
    fn insert(&mut self, seq: u64, off: u64) {
        // `i` runs start at or below `seq`; none holds it, so it extends the run before it,
        // starts the run after it, joins the two, or stands alone.
        let i = self.runs.partition_point(|r| r.seq0 <= seq);
        let extends = match i.checked_sub(1) {
            Some(p) => match self.runs.get(p) {
                Some(run) => {
                    let len = self.run_end(p).saturating_sub(run.at) as u64;
                    run.seq0.checked_add(len) == Some(seq)
                }
                None => false,
            },
            None => false,
        };
        let starts_next = match (self.runs.get(i), seq.checked_add(1)) {
            (Some(next), Some(after)) => next.seq0 == after,
            _ => false,
        };
        let j = match self.runs.get(i) {
            Some(next) => next.at,
            None => self.offs.len(),
        };
        self.ordered = self.ordered && self.keeps_order(j, j, off);
        self.offs.insert(j, off);
        self.offset_lo = self.offset_lo.min(off);
        self.offset_hi = self.offset_hi.max(off);
        match (extends, starts_next) {
            (true, true) => {
                // The run before now runs into the one after: they are one run.
                let _ = vec_remove_at(&mut self.runs, i);
                self.shift_from(i);
            }
            (true, false) => self.shift_from(i),
            (false, true) => {
                if let Some(next) = self.runs.get_mut(i) {
                    next.seq0 = seq;
                }
                self.shift_from(i.saturating_add(1));
            }
            (false, false) => {
                vec_insert_at(&mut self.runs, i, Run { seq0: seq, at: j });
                self.shift_from(i.saturating_add(1));
            }
        }
        if i == 0 {
            self.refirst();
        }
    }

    /// Call `f` with every `(seq, offset)` held, in seq order, while it answers true;
    /// whether it always did.
    fn each(&self, mut f: impl FnMut(u64, u64) -> bool) -> bool {
        for (i, run) in self.runs.iter().enumerate() {
            for j in run.at..self.run_end(i) {
                let Some(o) = self.offs.get(j) else {
                    return false;
                };
                if !f(run.seq0.saturating_add(j.saturating_sub(run.at) as u64), o) {
                    return false;
                }
            }
        }
        true
    }

    /// Separate an established consecutive run from a later run when insertion
    /// extends it across a gap. The long lower run keeps at least half a chunk;
    /// sparse and descending backfills retain the balanced split policy. Once
    /// separated, directory insertion keeps this frontier out of the later run.
    fn split_point(&self, seq: u64) -> usize {
        let next = self.runs.partition_point(|r| r.seq0 <= seq);
        if let (Some(prev), Some(after)) = (
            next.checked_sub(1).and_then(|i| self.runs.get(i)),
            self.runs.get(next),
        ) {
            let len = after.at.saturating_sub(prev.at);
            let last = prev.seq0.saturating_add(len.saturating_sub(1) as u64);
            if len >= chunk_cap() / 2 && isolate_forward_run(last, seq, after.seq0) {
                return after.at;
            }
        }
        self.len() / 2
    }

    /// Every `(seq, offset)` held, in seq order.
    fn pairs(&self) -> Vec<(u64, u64)> {
        let len = self.len();
        let mut out = if len <= 65_536 {
            Vec::with_capacity(len)
        } else {
            Vec::new()
        };
        self.each(|seq, o| {
            out.push((seq, o));
            true
        });
        out
    }

    /// Take in `from`'s keys, every one of which lies above this chunk's.
    #[cfg(any(test, feature = "retention"))]
    fn absorb(&mut self, from: &Chunk) {
        let cap = self.len().saturating_add(from.len());
        let mut pairs = if cap <= 65_536 {
            Vec::with_capacity(cap)
        } else {
            Vec::new()
        };
        for c in [&*self, from] {
            c.each(|seq, o| {
                pairs.push((seq, o));
                true
            });
        }
        #[cfg(test)]
        tally::scratch(pairs.capacity() * std::mem::size_of::<(u64, u64)>());
        *self = Chunk::of(&pairs);
    }

    /// Drop every key whose offset lies below `min`; how many were dropped.
    #[cfg(any(test, feature = "retention"))]
    fn retain_from(&mut self, min: u64) -> usize {
        let n = self.len();
        if min <= self.offset_lo || n == 0 {
            return 0;
        }
        if self.offset_hi < min {
            self.runs.clear();
            self.offs.drain_front(n);
            self.offset_lo = u64::MAX;
            self.offset_hi = 0;
            return n;
        }
        let cut = |o: u64| !crate::store::dedup_retains_from_cut(o, min);
        if self.ordered {
            // The offsets rise in seq order, so the keys below the cut are a prefix.
            let (mut lo, mut hi) = (0usize, n);
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                if self.offs.get(mid).is_some_and(cut) {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }
            let k = lo;
            if k == 0 {
                return 0;
            }
            // The run holding entry `k` becomes the first; the ones wholly below go.
            let first = self.runs.partition_point(|r| r.at <= k).saturating_sub(1);
            vec_drop_prefix(&mut self.runs, first);
            if k == n {
                self.runs.clear();
            } else if let Some(run) = self.runs.first_mut() {
                run.seq0 = run.seq0.saturating_add(k.saturating_sub(run.at) as u64);
                run.at = k;
            }
            for r in &mut self.runs {
                r.at = r.at.saturating_sub(k);
            }
            self.offs.drain_front(k);
            self.offset_lo = self.offs.get(0).unwrap_or(u64::MAX);
            self.refirst();
            return k;
        }
        // Unordered: count first, so a chunk the cut misses copies nothing, then rebuild
        // from the kept keys. A dropped entry inside a run splits it, so the runs stay
        // maximal.
        let mut gone = 0usize;
        let mut offset_lo = u64::MAX;
        #[cfg(test)]
        tally::retention_scan(n);
        for j in 0..n {
            if let Some(off) = self.offs.get(j) {
                offset_lo = offset_lo.min(off);
                if cut(off) {
                    gone = gone.saturating_add(1);
                }
            }
        }
        if gone == 0 {
            // Recover the exact lower bound after replacements left it stale, so
            // advancing floors below the first live offset also avoid rescanning.
            self.offset_lo = offset_lo;
            return 0;
        }
        let rem = n.saturating_sub(gone);
        let mut kept = if rem <= 65_536 {
            Vec::with_capacity(rem)
        } else {
            Vec::new()
        };
        self.each(|seq, o| {
            if !cut(o) {
                kept.push((seq, o));
            }
            true
        });
        #[cfg(test)]
        tally::scratch(kept.capacity() * std::mem::size_of::<(u64, u64)>());
        *self = Chunk::of(&kept);
        gone
    }

    fn shrink_to_fit(&mut self) {
        self.runs.shrink_to_fit();
        self.offs.shrink(0);
    }
}

/// The most chunk headers a flat directory insert may shift. Producers that only
/// append chunks stay flat; rings move the nearer end, and costly interior edits
/// promote to a tree. Allocation growth and effective cuts remain amortized work.
const FLAT_SHIFT_MAX: usize = 64;

fn should_promote(shifted: usize) -> bool {
    #[cfg(test)]
    {
        shifted >= tally::flat_shift_max()
    }
    #[cfg(not(test))]
    {
        shifted >= FLAT_SHIFT_MAX
    }
}

/// Keep an extending consecutive run out of a later run's partial chunk. Merely
/// landing in a seq gap is insufficient: descending gap backfills must still fill
/// the next chunk rather than open a new single-key chunk on every insert.
fn isolate_forward_run(last: u64, seq: u64, next_first: u64) -> bool {
    #[cfg(test)]
    if !tally::isolate_runs() {
        return false;
    }
    last.checked_add(1) == Some(seq) && seq.checked_add(1) != Some(next_first)
}

/// One producer's packed keys. Flat directories preserve the compact, contiguous
/// append path; boxed rings handle end edits without enlarging this enum, and trees
/// bound costly interior edits for arbitrary backfills and interleaved streams.
#[derive(Debug)]
enum Packed {
    Flat(Vec<Chunk>),
    // Keep Packed as small as the flat representation for every short producer.
    #[allow(clippy::box_collection)]
    Ring(Box<VecDeque<Chunk>>),
    Tree(BTreeMap<u64, Chunk>),
}

impl Default for Packed {
    fn default() -> Self {
        Self::Flat(Vec::new())
    }
}

enum Chunks<'a> {
    Flat(std::slice::Iter<'a, Chunk>),
    Ring(std::collections::vec_deque::Iter<'a, Chunk>),
    Tree(std::collections::btree_map::Values<'a, u64, Chunk>),
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a Chunk;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Flat(it) => it.next(),
            Self::Ring(it) => it.next(),
            Self::Tree(it) => it.next(),
        }
    }
}

/// Statically dispatched shared insertion policy. Flat vectors move the tail;
/// rings move the nearer end, while both keep chunks in the same logical order.
trait ChunkDirectory {
    fn len(&self) -> usize;
    fn at(&self, seq: u64) -> usize;
    fn chunk_mut(&mut self, i: usize) -> Option<&mut Chunk>;
    fn push_chunk(&mut self, chunk: Chunk);
    fn insert_chunk(&mut self, i: usize, chunk: Chunk);
    fn shift_work(&self, i: usize) -> usize;
}

impl ChunkDirectory for Vec<Chunk> {
    fn len(&self) -> usize {
        Vec::len(self)
    }
    fn at(&self, seq: u64) -> usize {
        Packed::at_flat(self, seq)
    }
    fn chunk_mut(&mut self, i: usize) -> Option<&mut Chunk> {
        self.get_mut(i)
    }
    fn push_chunk(&mut self, chunk: Chunk) {
        self.push(chunk);
    }
    fn insert_chunk(&mut self, i: usize, chunk: Chunk) {
        vec_insert_at(self, i, chunk);
    }
    fn shift_work(&self, i: usize) -> usize {
        self.len().saturating_sub(i)
    }
}

impl ChunkDirectory for VecDeque<Chunk> {
    fn len(&self) -> usize {
        VecDeque::len(self)
    }
    fn at(&self, seq: u64) -> usize {
        Packed::at_ring(self, seq)
    }
    fn chunk_mut(&mut self, i: usize) -> Option<&mut Chunk> {
        self.get_mut(i)
    }
    fn push_chunk(&mut self, chunk: Chunk) {
        self.push_back(chunk);
    }
    fn insert_chunk(&mut self, i: usize, chunk: Chunk) {
        if i == 0 {
            self.push_front(chunk);
        } else if i >= self.len() {
            self.push_back(chunk);
        } else {
            self.insert(i, chunk);
        }
    }
    fn shift_work(&self, i: usize) -> usize {
        i.min(self.len().saturating_sub(i))
    }
}

impl Packed {
    fn from_chunks(chunks: Vec<Chunk>) -> Self {
        #[cfg(test)]
        if tally::start_ring() {
            return Self::Ring(Box::new(VecDeque::from(chunks)));
        }
        Self::Flat(chunks)
    }

    fn chunks(&self) -> Chunks<'_> {
        match self {
            Self::Flat(v) => Chunks::Flat(v.iter()),
            Self::Ring(v) => Chunks::Ring(v.iter()),
            Self::Tree(m) => Chunks::Tree(m.values()),
        }
    }

    #[cfg(any(test, feature = "retention"))]
    fn is_empty(&self) -> bool {
        match self {
            Self::Flat(v) => v.is_empty(),
            Self::Ring(v) => v.is_empty(),
            Self::Tree(m) => m.is_empty(),
        }
    }

    /// The flat chunk whose seq stretch contains seq, or the first for a lower key.
    fn at_flat(chunks: &[Chunk], seq: u64) -> usize {
        chunks
            .partition_point(|c| c.first_seq() <= seq)
            .saturating_sub(1)
    }

    fn at_ring(chunks: &VecDeque<Chunk>, seq: u64) -> usize {
        chunks
            .partition_point(|c| c.first_seq() <= seq)
            .saturating_sub(1)
    }

    /// The tree chunk whose seq stretch contains seq, or the first for a lower key.
    fn at_tree(chunks: &BTreeMap<u64, Chunk>, seq: u64) -> Option<u64> {
        chunks
            .range(..=seq)
            .next_back()
            .or_else(|| chunks.first_key_value())
            .map(|(&k, _)| k)
    }

    fn slot(&self, seq: u64) -> Option<(&Chunk, usize)> {
        let chunk = match self {
            Self::Flat(v) => v.get(Self::at_flat(v, seq))?,
            Self::Ring(v) => v.get(Self::at_ring(v, seq))?,
            Self::Tree(m) => {
                m.range(..=seq)
                    .next_back()
                    .or_else(|| m.first_key_value())?
                    .1
            }
        };
        Some((chunk, chunk.slot(seq)?))
    }

    fn get(&self, seq: u64) -> Option<u64> {
        let (chunk, j) = self.slot(seq)?;
        chunk.offs.get(j)
    }

    fn put(&mut self, seq: u64, off: u64) -> bool {
        match self {
            Self::Flat(chunks) => {
                let at = match Self::put_linear(chunks, seq, off) {
                    Ok(inserted) => return inserted,
                    Err(at) => at,
                };
                let end_work = at.min(chunks.len().saturating_sub(at));
                #[cfg(test)]
                let ring_enabled = tally::ring_dirs();
                #[cfg(not(test))]
                let ring_enabled = true;
                if ring_enabled && !should_promote(end_work) {
                    // Vec -> VecDeque transfers the allocation without moving its
                    // headers. Box only the ring metadata; short producers stay flat.
                    *self = Self::Ring(Box::new(VecDeque::from(std::mem::take(chunks))));
                } else {
                    #[cfg(test)]
                    tally::directory_moved(chunks.len());
                    *self = Self::Tree(
                        std::mem::take(chunks)
                            .into_iter()
                            .map(|c| (c.first_seq(), c))
                            .collect(),
                    );
                }
                self.put(seq, off)
            }
            Self::Ring(chunks) => {
                if let Ok(inserted) = Self::put_linear(chunks.as_mut(), seq, off) {
                    return inserted;
                }
                // Both ring ends would move too many headers. Promote once;
                // arbitrary middle insertions then use the logarithmic tree path.
                #[cfg(test)]
                tally::directory_moved(chunks.len());
                *self = Self::Tree(
                    std::mem::take(chunks.as_mut())
                        .into_iter()
                        .map(|c| (c.first_seq(), c))
                        .collect(),
                );
                self.put(seq, off)
            }
            Self::Tree(chunks) => Self::put_tree(chunks, seq, off),
        }
    }

    /// Insert into a non-full tree chunk, updating its directory key if its first
    /// seq changes. The predecessor search makes a lower seq possible only at the
    /// first chunk, or when filling the next chunk from below.
    fn insert_tree(chunks: &mut BTreeMap<u64, Chunk>, key: u64, seq: u64, off: u64) {
        if seq < key {
            if let Some(mut c) = chunks.remove(&key) {
                c.insert(seq, off);
                chunks.insert(c.first_seq(), c);
            }
        } else if let Some(c) = chunks.get_mut(&key) {
            c.insert(seq, off);
        }
    }

    fn put_tree(chunks: &mut BTreeMap<u64, Chunk>, seq: u64, off: u64) -> bool {
        let Some(key) = Self::at_tree(chunks, seq) else {
            chunks.insert(seq, Chunk::of(&[(seq, off)]));
            return true;
        };
        let (len, last) = match chunks.get_mut(&key) {
            Some(c) => {
                if let Some(j) = c.slot(seq) {
                    c.set(j, off);
                    return false;
                }
                (c.len(), c.last_seq())
            }
            None => return false,
        };
        if len < chunk_cap() {
            Self::insert_tree(chunks, key, seq, off);
        } else if seq > last {
            let next = chunks
                .range((Excluded(key), Unbounded))
                .next()
                .map(|(&k, _)| k);
            if let Some(next) = next.filter(|k| {
                chunks.get(k).is_some_and(|c| {
                    c.len() < chunk_cap() && !isolate_forward_run(last, seq, c.first_seq())
                })
            }) {
                Self::insert_tree(chunks, next, seq, off);
            } else {
                chunks.insert(seq, Chunk::of(&[(seq, off)]));
            }
        } else if seq < key {
            chunks.insert(seq, Chunk::of(&[(seq, off)]));
        } else if let Some(c) = chunks.remove(&key) {
            let split = c.split_point(seq);
            let pairs = c.pairs();
            #[cfg(test)]
            tally::moved(pairs.len());
            let halves = (split > 0 && split < pairs.len())
                .then(|| pairs.get(..split).zip(pairs.get(split..)))
                .flatten();
            let Some((lo, hi)) = halves else {
                // Keep every key if inconsistent chunk metadata ever proposes an
                // out-of-range split. Valid full chunks always take the split.
                let mut c = c;
                c.insert(seq, off);
                chunks.insert(c.first_seq(), c);
                return true;
            };
            let mut lower = Chunk::of(lo);
            let mut upper = Chunk::of(hi);
            if seq > upper.first_seq() {
                upper.insert(seq, off);
            } else {
                lower.insert(seq, off);
            }
            chunks.insert(lower.first_seq(), lower);
            chunks.insert(upper.first_seq(), upper);
        }
        true
    }

    #[cfg(any(test, feature = "retention"))]
    fn retain_from(&mut self, min: u64) -> usize {
        match self {
            Self::Flat(chunks) => Self::retain_flat(chunks, min),
            Self::Ring(chunks) => {
                let mut dropped = 0usize;
                for c in chunks.iter_mut() {
                    dropped = dropped.saturating_add(c.retain_from(min));
                }
                if dropped > 0 {
                    // Reads and unchanged cuts leave a wrapped ring untouched.
                    let keep = Self::compact_chunks(chunks.make_contiguous());
                    chunks.truncate(keep);
                    if chunks.capacity() > 16 && chunks.len() <= chunks.capacity() / 4 {
                        chunks.shrink_to(chunks.len().saturating_mul(2).max(4));
                    }
                }
                dropped
            }
            Self::Tree(chunks) => {
                let mut dropped = 0usize;
                for c in chunks.values_mut() {
                    dropped = dropped.saturating_add(c.retain_from(min));
                }
                if dropped == 0 {
                    return 0;
                }
                // Rebuild only when a cut changed chunks: first seqs may have changed,
                // and thin neighbours merge. Tree rebuilding costs O(chunks * log chunks).
                // Consume old nodes as new nodes are built;
                // no second directory-sized vector or per-record scratch is needed.
                let mut pending: Option<Chunk> = None;
                for c in std::mem::take(chunks).into_values().filter(|c| c.len() > 0) {
                    match pending.as_mut() {
                        Some(prev) if prev.len().saturating_add(c.len()) <= chunk_cap() / 2 => {
                            prev.absorb(&c)
                        }
                        _ => {
                            if let Some(prev) = pending.replace(c) {
                                chunks.insert(prev.first_seq(), prev);
                            }
                        }
                    }
                }
                if let Some(prev) = pending {
                    chunks.insert(prev.first_seq(), prev);
                }
                dropped
            }
        }
    }

    fn shrink_to_fit(&mut self) {
        match self {
            Self::Flat(chunks) => {
                for c in &mut *chunks {
                    c.shrink_to_fit();
                }
                chunks.shrink_to_fit();
            }
            Self::Ring(chunks) => {
                for c in chunks.iter_mut() {
                    c.shrink_to_fit();
                }
                chunks.shrink_to_fit();
            }
            Self::Tree(chunks) => {
                for c in chunks.values_mut() {
                    c.shrink_to_fit();
                }
            }
        }
    }

    /// Place `seq` at `off`: replace its offset when held, else insert it; whether it is new.
    /// A new key joins the chunk whose stretch holds its seq. A full chunk passes a key past
    /// its end to the next chunk when that one has room, else to a new chunk, and splits in
    /// halves for a key inside it.
    fn put_linear<D: ChunkDirectory>(chunks: &mut D, seq: u64, off: u64) -> Result<bool, usize> {
        let cap = chunk_cap();
        let i = chunks.at(seq);
        let (len, first, last) = match chunks.chunk_mut(i) {
            Some(c) => {
                if let Some(j) = c.slot(seq) {
                    c.set(j, off);
                    return Ok(false);
                }
                (c.len(), c.first_seq(), c.last_seq())
            }
            None => {
                chunks.push_chunk(Chunk::of(&[(seq, off)]));
                return Ok(true);
            }
        };
        if len < cap {
            if let Some(c) = chunks.chunk_mut(i) {
                c.insert(seq, off);
            }
            return Ok(true);
        }
        if seq > last {
            let next = i.saturating_add(1);
            if let Some(c) = chunks.chunk_mut(next) {
                if c.len() < cap && !isolate_forward_run(last, seq, c.first_seq()) {
                    c.insert(seq, off);
                    return Ok(true);
                }
            }
            if should_promote(chunks.shift_work(next)) {
                return Err(next);
            }
            Self::open_linear(chunks, next, seq, off);
            return Ok(true);
        }
        if seq < first {
            // Below the first chunk.
            if should_promote(chunks.shift_work(i)) {
                return Err(i);
            }
            Self::open_linear(chunks, i, seq, off);
            return Ok(true);
        }
        if should_promote(chunks.shift_work(i.saturating_add(1))) {
            return Err(i.saturating_add(1));
        }
        // Inside a full chunk: split it in halves and place the key in the half whose
        // stretch holds it.
        let Some(c) = chunks.chunk_mut(i) else {
            return Ok(true);
        };
        let split = c.split_point(seq);
        let pairs = c.pairs();
        let halves = (split > 0 && split < pairs.len())
            .then(|| pairs.get(..split).zip(pairs.get(split..)))
            .flatten();
        let Some((lo, hi)) = halves else {
            // Preserve the original chunk and new key if its metadata cannot
            // describe the materialized pairs. No directory edit has happened.
            c.insert(seq, off);
            return Ok(true);
        };
        let upper_first = hi.first().map(|p| p.0);
        *c = Chunk::of(lo);
        #[cfg(test)]
        {
            tally::moved(pairs.len());
            tally::directory_moved(chunks.shift_work(i.saturating_add(1)));
        }
        chunks.insert_chunk(i.saturating_add(1), Chunk::of(hi));
        let into = if upper_first.is_some_and(|f| seq > f) {
            i.saturating_add(1)
        } else {
            i
        };
        if let Some(c) = chunks.chunk_mut(into) {
            c.insert(seq, off);
        }
        Ok(true)
    }

    /// A new chunk at `i` holding just `seq`.
    fn open_linear<D: ChunkDirectory>(chunks: &mut D, i: usize, seq: u64, off: u64) {
        #[cfg(test)]
        tally::directory_moved(chunks.shift_work(i));
        let chunk = Chunk::of(&[(seq, off)]);
        if i <= chunks.len() {
            chunks.insert_chunk(i, chunk);
        } else {
            chunks.push_chunk(chunk);
        }
    }

    /// Drop every key whose offset lies below `min`; how many were dropped. Emptied chunks
    /// go, and neighbours that together hold at most half a chunk join, so a cut that thins
    /// chunks leaves no chunk header to a key or two.
    #[cfg(any(test, feature = "retention"))]
    fn retain_flat(chunks: &mut Vec<Chunk>, min: u64) -> usize {
        let mut dropped = 0usize;
        for c in &mut *chunks {
            dropped = dropped.saturating_add(c.retain_from(min));
        }
        if dropped > 0 {
            let keep = Self::compact_chunks(chunks.as_mut_slice());
            chunks.truncate(keep);
            if chunks.capacity() > 16 && chunks.len() <= chunks.capacity() / 4 {
                chunks.shrink_to(chunks.len().saturating_mul(2).max(4));
            }
        }
        dropped
    }

    #[cfg(any(test, feature = "retention"))]
    fn compact_chunks(chunks: &mut [Chunk]) -> usize {
        let half = chunk_cap() / 2;
        // In place: `..w` are the chunks kept so far, `w..r` the emptied or absorbed.
        let mut w = 0usize;
        let total = chunks.len();
        for r in 0..total {
            let len = match chunks.get(r) {
                Some(c) if c.len() > 0 => c.len(),
                _ => continue,
            };
            let joins = match w.checked_sub(1).and_then(|p| chunks.get(p)) {
                Some(prev) => prev.len().saturating_add(len) <= half,
                None => false,
            };
            if joins {
                if let Some(prev_idx) = w.checked_sub(1) {
                    if prev_idx < r {
                        if let Some(sub) = chunks.get_mut(prev_idx..=r) {
                            if let Some((into, rest)) = sub.split_first_mut() {
                                if let Some(from) = rest.last() {
                                    into.absorb(from);
                                }
                            }
                        }
                    }
                }
            } else {
                if w < r {
                    if let Some(sub) = chunks.get_mut(w..=r) {
                        if let Some((first, rest)) = sub.split_first_mut() {
                            if let Some(end) = rest.last_mut() {
                                std::mem::swap(first, end);
                            }
                        }
                    }
                }
                w = w.saturating_add(1);
            }
        }
        w
    }
}

/// The retained produces' exactly-once keys: `(producer_id, producer_seq) -> Offset`.
#[derive(Debug, Default)]
pub(crate) struct DedupIndex {
    /// The keys held beside a neighbour of their producer, by producer.
    packed: HashMap<u64, Packed>,
    /// The keys with no neighbour held, one entry each, as the map's were.
    loose: HashMap<(u64, u64), u64>,
    len: usize,
    /// The negative control's mutant: a lookup forgets the last key of every packed run.
    #[cfg(test)]
    forget_run_end: bool,
}

impl DedupIndex {
    pub(crate) fn new() -> DedupIndex {
        DedupIndex::default()
    }

    /// The offset `(producer_id, producer_seq)` first landed at, while its record is retained.
    pub(crate) fn get(&self, producer_id: u64, producer_seq: u64) -> Option<Offset> {
        #[cfg(test)]
        if self.forget_run_end {
            let p = self.packed.get(&producer_id);
            if let Some((c, j)) = p.and_then(|p| p.slot(producer_seq)) {
                if c.ends_run(j) {
                    return None;
                }
            }
        }
        self.lookup(producer_id, producer_seq).map(Offset)
    }

    /// The offset held for a key, in whichever store holds it.
    fn lookup(&self, producer_id: u64, producer_seq: u64) -> Option<u64> {
        if let Some(p) = self.packed.get(&producer_id) {
            if let Some(o) = p.get(producer_seq) {
                return Some(o);
            }
        }
        self.loose.get(&(producer_id, producer_seq)).copied()
    }

    /// Whether `(producer_id, producer_seq)` is held.
    pub(crate) fn contains(&self, producer_id: u64, producer_seq: u64) -> bool {
        self.get(producer_id, producer_seq).is_some()
    }

    /// Record that `(producer_id, producer_seq)` landed at `off`, replacing the offset a key
    /// already held had (as `HashMap::insert` does).
    pub(crate) fn insert(&mut self, producer_id: u64, producer_seq: u64, off: Offset) {
        let (pid, seq, off) = (producer_id, producer_seq, off.0);
        // A key lives in one store: a loose one is replaced where it is. (A log of one
        // consecutive producer holds no loose key, so its inserts hash nothing here.)
        if !self.loose.is_empty() {
            if let Some(o) = self.loose.get_mut(&(pid, seq)) {
                *o = off;
                return;
            }
        }
        // A packed producer may still have short loose runs from before promotion.
        // Absorb the entire neighbouring run, not just its nearest key. Each side
        // holds fewer than PACK_MIN entries and ends at the first absent key.
        if let Some(p) = self.packed.get_mut(&pid) {
            if p.put(seq, off) {
                self.len = self.len.saturating_add(1);
                let before = self.loose.len();
                if !self.loose.is_empty() {
                    for d in 1..pack_min() {
                        let Some(n) = seq.checked_sub(d as u64) else {
                            break;
                        };
                        let Some(o) = self.loose.remove(&(pid, n)) else {
                            break;
                        };
                        p.put(n, o);
                    }
                    for d in 1..pack_min() {
                        let Some(n) = seq.checked_add(d as u64) else {
                            break;
                        };
                        let Some(o) = self.loose.remove(&(pid, n)) else {
                            break;
                        };
                        p.put(n, o);
                    }
                }
                if self.loose.len() < before {
                    self.shrink_loose();
                }
            }
            return;
        }
        self.len = self.len.saturating_add(1);
        let (left, right) = loose_run(&self.loose, pid, seq);
        if left.saturating_add(right).saturating_add(1) < pack_min() {
            self.loose.insert((pid, seq), off);
            return;
        }
        self.pack_loose_run(pid, seq, off, left, right);
    }

    /// Pack the startup run after len has accounted for the new key. Bounds and
    /// missing-neighbour recovery keep this migration lossless on every path.
    fn pack_loose_run(&mut self, pid: u64, seq: u64, off: u64, left: usize, right: usize) {
        // Build the whole contiguous run in seq order, using bounded stack scratch.
        // At most PACK_MIN - 1 loose keys lie on each side. One production chunk
        // holds the entire run; test-only tiny chunks may grow the header vector.
        let n = left.saturating_add(right).saturating_add(1);
        let mut pairs = [(0u64, 0u64); 2 * PACK_CAP - 1];
        if n > pairs.len() {
            self.loose.insert((pid, seq), off);
            return;
        }
        // The scratch bound also bounds both usize-to-u64 casts. A stale plan
        // must not wrap below zero or saturate into duplicate maximum keys.
        let Some(first) = seq.checked_sub(left as u64) else {
            self.loose.insert((pid, seq), off);
            return;
        };
        if seq.checked_add(right as u64).is_none() {
            self.loose.insert((pid, seq), off);
            return;
        }
        let mut filled = 0usize;
        for (d, pair) in pairs.iter_mut().take(n).enumerate() {
            let key = first.saturating_add(d as u64);
            let value = if key == seq {
                off
            } else if let Some(value) = self.loose.remove(&(pid, key)) {
                value
            } else {
                break;
            };
            *pair = (key, value);
            filled = filled.saturating_add(1);
        }
        let run = pairs.get(..n).filter(|_| filled == n);
        let Some(run) = run else {
            // A stale or inconsistent run plan must not discard keys already
            // removed before the miss, nor lose the newly inserted key.
            for &(key, value) in pairs.iter().take(filled) {
                self.loose.insert((pid, key), value);
            }
            self.loose.insert((pid, seq), off);
            return;
        };
        let mut chunks = Vec::with_capacity(1);
        for pairs in run.chunks(chunk_cap()) {
            chunks.push(Chunk::of(pairs));
        }
        self.packed.insert(pid, Packed::from_chunks(chunks));
        self.shrink_loose();
    }

    /// Reclaim an emptied startup map after promotions. Quarter-full hysteresis
    /// amortizes rehashing over removed keys and avoids retaining a fleet's whole
    /// startup allocation after its producers have all become packed.
    fn shrink_loose(&mut self) {
        if self.loose.capacity() > 64 && self.loose.len() <= self.loose.capacity() / 4 {
            self.loose
                .shrink_to(self.loose.len().saturating_mul(2).max(16));
        }
    }

    /// How many keys are held.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Whether no key is held.
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Drop every key whose offset lies below `min` (a retention cut to `min`), and release
    /// the memory a store that shrank no longer uses.
    #[cfg(any(test, feature = "retention"))]
    pub(crate) fn retain_from(&mut self, min: u64) {
        let mut dropped = 0usize;
        for p in self.packed.values_mut() {
            dropped = dropped.saturating_add(p.retain_from(min));
        }
        self.packed.retain(|_, p| !p.is_empty());
        let before = self.loose.len();
        self.loose
            .retain(|_, o| crate::store::dedup_retains_from_cut(*o, min));
        dropped = dropped.saturating_add(before.saturating_sub(self.loose.len()));
        self.len = self.len.saturating_sub(dropped);
        if self.packed.capacity() > 64 && self.packed.len() <= self.packed.capacity() / 4 {
            self.packed
                .shrink_to(self.packed.len().saturating_mul(2).max(16));
        }
        self.shrink_loose();
    }

    /// Give back every vector's spare capacity (after an open built the index whole).
    pub(crate) fn shrink_to_fit(&mut self) {
        for p in self.packed.values_mut() {
            p.shrink_to_fit();
        }
        self.packed.shrink_to_fit();
        self.loose.shrink_to_fit();
    }

    /// Call `f` with every held `(producer_id, producer_seq, offset)` while it answers
    /// true; whether it always did.
    #[cfg(test)]
    fn each(&self, mut f: impl FnMut(u64, u64, u64) -> bool) -> bool {
        for (&pid, p) in &self.packed {
            for c in p.chunks() {
                if !c.each(|seq, o| f(pid, seq, o)) {
                    return false;
                }
            }
        }
        for (&(pid, seq), &o) in &self.loose {
            if !f(pid, seq, o) {
                return false;
            }
        }
        true
    }

    /// Collect every held `(producer_id, producer_seq, offset)` below offset `min`.
    #[cfg(all(feature = "retention", feature = "relay"))]
    pub(crate) fn keys_below(&self, min: u64) -> Vec<(u64, u64, u64)> {
        let mut out = Vec::new();
        for (&pid, p) in &self.packed {
            for c in p.chunks() {
                if min <= c.offset_lo {
                    continue;
                }
                for (i, run) in c.runs.iter().enumerate() {
                    for j in run.at..c.run_end(i) {
                        if let Some(off) = c.offs.get(j) {
                            if !crate::store::dedup_retains_from_cut(off, min) {
                                let seq = run.seq0.saturating_add(j.saturating_sub(run.at) as u64);
                                out.push((pid, seq, off));
                            }
                        }
                    }
                }
            }
        }
        for (&(pid, seq), &off) in &self.loose {
            if !crate::store::dedup_retains_from_cut(off, min) {
                out.push((pid, seq, off));
            }
        }
        out
    }

    /// Every held key and its offset, sorted.
    #[cfg(test)]
    pub(crate) fn entries(&self) -> Vec<((u64, u64), u64)> {
        let mut out = Vec::with_capacity(self.len);
        self.each(|pid, seq, o| {
            out.push(((pid, seq), o));
            true
        });
        out.sort_unstable();
        out
    }

    /// The heap the index holds, by its maps' and vectors' capacities. Tree node
    /// storage is a conservative upper bound because std exposes no node capacity.
    #[cfg(test)]
    pub(crate) fn heap_bytes(&self) -> usize {
        let mut b = tally::map_bytes(
            self.loose.capacity(),
            std::mem::size_of::<((u64, u64), u64)>(),
        );
        b += tally::map_bytes(self.packed.capacity(), std::mem::size_of::<(u64, Packed)>());
        for p in self.packed.values() {
            b += match p {
                Packed::Flat(v) => v.capacity() * std::mem::size_of::<Chunk>(),
                Packed::Ring(v) => {
                    std::mem::size_of::<VecDeque<Chunk>>()
                        + v.capacity() * std::mem::size_of::<Chunk>()
                }
                // BTreeMap exposes no allocation count. A conservative upper bound:
                // every node except an underfull root holds at least five entries.
                Packed::Tree(m) => {
                    m.len().div_ceil(5) * (11 * (8 + std::mem::size_of::<Chunk>()) + 12 * 8 + 16)
                }
            };
            for c in p.chunks() {
                b += c.runs.capacity() * std::mem::size_of::<Run>() + c.offs.heap_bytes();
            }
        }
        b
    }

    /// The mutant the negative control runs: every lookup forgets the last key of its run.
    #[cfg(test)]
    pub(crate) fn mutant_forgetting_run_ends() -> DedupIndex {
        DedupIndex {
            forget_run_end: true,
            ..DedupIndex::default()
        }
    }
}

/// Two indexes are equal when they hold the same keys at the same offsets, however each one
/// happens to store them: which keys are packed and where its chunks split depend on the
/// order the keys came in and the cuts since.
impl PartialEq for DedupIndex {
    fn eq(&self, other: &DedupIndex) -> bool {
        // Keys are distinct in each, so equal counts and every key of one held in the other
        // at its offset make the sets equal.
        if self.len != other.len {
            return false;
        }
        for (&pid, p) in &self.packed {
            for c in p.chunks() {
                for (i, run) in c.runs.iter().enumerate() {
                    for j in run.at..c.run_end(i) {
                        let Some(o) = c.offs.get(j) else {
                            return false;
                        };
                        let seq = run.seq0.saturating_add(j.saturating_sub(run.at) as u64);
                        if other.lookup(pid, seq) != Some(o) {
                            return false;
                        }
                    }
                }
            }
        }
        for (&(pid, seq), &o) in &self.loose {
            if other.lookup(pid, seq) != Some(o) {
                return false;
            }
        }
        true
    }
}

/// What the tests count of the index's work, per thread: the entries an insert moved within
/// its vectors, and the most scratch one retention cut built. A test may also lower the
/// chunk size on its own thread.
#[cfg(test)]
mod tally {
    use std::cell::Cell;

    thread_local! {
        static RING_DIRS: Cell<bool> = const { Cell::new(true) };
        static START_RING: Cell<bool> = const { Cell::new(false) };
        static BULK_MOVES: Cell<bool> = const { Cell::new(true) };
        static PREFIX_MOVED: Cell<u64> = const { Cell::new(0) };
        static ISOLATE_RUNS: Cell<bool> = const { Cell::new(true) };
        static OFFSET_MOVED: Cell<u64> = const { Cell::new(0) };
        static DIRECTORY_MOVED: Cell<u64> = const { Cell::new(0) };
        static MOVED: Cell<u64> = const { Cell::new(0) };
        static SCRATCH: Cell<usize> = const { Cell::new(0) };
        static RETENTION_SCAN: Cell<usize> = const { Cell::new(0) };
        static FLAT_SHIFT_MAX: Cell<usize> = const { Cell::new(super::FLAT_SHIFT_MAX) };
        static PACK_MIN: Cell<usize> = const { Cell::new(super::PACK_MIN) };
        static CHUNK_CAP: Cell<usize> = const { Cell::new(super::CHUNK) };
    }

    pub(super) fn ring_dirs() -> bool {
        RING_DIRS.with(Cell::get)
    }
    pub(super) fn set_ring_dirs(enabled: bool) {
        RING_DIRS.with(|c| c.set(enabled));
    }
    pub(super) fn start_ring() -> bool {
        START_RING.with(Cell::get)
    }
    pub(super) fn set_start_ring(enabled: bool) {
        START_RING.with(|c| c.set(enabled));
    }

    pub(super) fn bulk_moves() -> bool {
        BULK_MOVES.with(Cell::get)
    }

    pub(super) fn set_bulk_moves(enabled: bool) {
        BULK_MOVES.with(|c| c.set(enabled));
    }

    pub(super) fn prefix_moved(n: usize) {
        PREFIX_MOVED.with(|c| c.set(c.get().saturating_add(n as u64)));
    }

    pub(super) fn take_prefix_moved() -> u64 {
        PREFIX_MOVED.with(|c| c.replace(0))
    }

    pub(super) fn isolate_runs() -> bool {
        ISOLATE_RUNS.with(Cell::get)
    }

    pub(super) fn set_isolate_runs(enabled: bool) {
        ISOLATE_RUNS.with(|c| c.set(enabled));
    }

    pub(super) fn offset_moved(n: usize) {
        OFFSET_MOVED.with(|c| c.set(c.get().saturating_add(n as u64)));
        moved(n);
    }

    pub(super) fn take_offset_moved() -> u64 {
        OFFSET_MOVED.with(|c| c.replace(0))
    }

    pub(super) fn retention_scan(n: usize) {
        RETENTION_SCAN.with(|c| c.set(c.get().saturating_add(n)));
    }

    pub(super) fn take_retention_scan() -> usize {
        RETENTION_SCAN.with(|c| c.replace(0))
    }

    pub(super) fn directory_moved(n: usize) {
        DIRECTORY_MOVED.with(|c| c.set(c.get().saturating_add(n as u64)));
        moved(n);
    }

    pub(super) fn take_directory_moved() -> u64 {
        DIRECTORY_MOVED.with(|c| c.replace(0))
    }

    pub(super) fn moved(n: usize) {
        MOVED.with(|c| c.set(c.get().saturating_add(n as u64)));
    }

    pub(super) fn scratch(bytes: usize) {
        SCRATCH.with(|c| c.set(c.get().max(bytes)));
    }

    /// The entries moved and the most scratch since the last take, and start again.
    pub(super) fn take() -> (u64, usize) {
        (MOVED.with(|c| c.replace(0)), SCRATCH.with(|c| c.replace(0)))
    }

    pub(super) fn flat_shift_max() -> usize {
        FLAT_SHIFT_MAX.with(Cell::get)
    }

    pub(super) fn set_flat_shift_max(max: usize) {
        FLAT_SHIFT_MAX.with(|c| c.set(max));
    }

    pub(super) fn pack_min() -> usize {
        PACK_MIN.with(Cell::get)
    }

    pub(super) fn set_pack_min(min: usize) {
        PACK_MIN.with(|c| c.set(min.clamp(2, super::PACK_CAP)));
    }

    pub(super) fn chunk_cap() -> usize {
        CHUNK_CAP.with(Cell::get)
    }

    /// Lower (or restore) this thread's chunk size.
    pub(super) fn set_chunk_cap(cap: usize) {
        CHUNK_CAP.with(|c| c.set(cap.max(2)));
    }

    /// A `HashMap` of `cap` usable entries of `entry` bytes: its buckets (a power of two at
    /// most 7/8 full) and a control byte each.
    pub(super) fn map_bytes(cap: usize, entry: usize) -> usize {
        if cap == 0 {
            return 0;
        }
        let buckets = (cap.saturating_mul(8) / 7).next_power_of_two();
        buckets * (entry + 1)
    }
}

#[cfg(test)]
mod tests {
    //! The index against the map it replaced, over random publish streams.

    use super::*;
    use crate::store::ACK_SEQ_BASE;

    /// xorshift64*: a tiny deterministic PRNG (std-only, reproducible per seed).
    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n.max(1)
        }
    }

    /// One producer's habit: how it picks its next seq.
    #[derive(Clone, Copy)]
    enum Habit {
        /// `1, 2, 3, …`
        Consecutive,
        /// Increasing, with gaps.
        Gapped,
        /// Anywhere in a small range: re-sends, backfills and repeats.
        Scattered,
        /// Near `u64::MAX`, where `seq + 1` overflows.
        Top,
        /// Alternately its own consecutive seqs and acks (`ACK_SEQ_BASE | input`) of
        /// inputs that sometimes run.
        Acking,
    }

    /// The broker's two ways of meeting a key: a publish answers a held key from the index
    /// and inserts only a new one; a replica's record and an open's rebuild insert every
    /// record, replacing a held key's offset.
    fn publish(
        idx: &mut DedupIndex,
        map: &mut HashMap<(u64, u64), Offset>,
        key: (u64, u64),
        head: &mut u64,
        replace: bool,
    ) -> Result<(), String> {
        let got = idx.get(key.0, key.1);
        let want = map.get(&key).copied();
        if got != want {
            return Err(format!("get{key:?}: index {got:?}, map {want:?}"));
        }
        if want.is_none() || replace {
            idx.insert(key.0, key.1, Offset(*head));
            map.insert(key, Offset(*head));
        }
        *head += 1;
        Ok(())
    }

    fn compare(idx: &DedupIndex, map: &HashMap<(u64, u64), Offset>) -> Result<(), String> {
        if idx.len() != map.len() {
            return Err(format!("len: index {}, map {}", idx.len(), map.len()));
        }
        for p in idx.packed.values() {
            if let Packed::Tree(chunks) = p {
                for (&key, c) in chunks {
                    if key != c.first_seq() {
                        return Err("stale tree directory key".to_string());
                    }
                }
            }
            let mut prev_last = None;
            for c in p.chunks() {
                if c.len() == 0
                    || c.len() > chunk_cap()
                    || prev_last.is_some_and(|last| c.first_seq() <= last)
                {
                    return Err("invalid chunk boundaries".to_string());
                }
                prev_last = Some(c.last_seq());
                if !c.each(|_, off| c.offset_lo <= off && off <= c.offset_hi) {
                    return Err("unsound chunk offset bounds".to_string());
                }
            }
        }
        for (&(pid, seq), &off) in map {
            let got = idx.get(pid, seq);
            if got != Some(off) {
                return Err(format!("get({pid}, {seq}): index {got:?}, map {off:?}"));
            }
            for probe in [seq.wrapping_add(1), seq.wrapping_sub(1)] {
                let (g, w) = (idx.get(pid, probe), map.get(&(pid, probe)).copied());
                if g != w {
                    return Err(format!("get({pid}, {probe}): index {g:?}, map {w:?}"));
                }
            }
        }
        let mut want: Vec<((u64, u64), u64)> = map.iter().map(|(k, o)| (*k, o.0)).collect();
        want.sort_unstable();
        if idx.entries() != want {
            return Err("the entries differ".to_string());
        }
        Ok(())
    }

    /// One seeded stream: producers with mixed habits publish, replicas replace, retention
    /// cuts the oldest offsets, and an open rebuilds the index from the retained records in
    /// offset order; after every step the index answers every question the map answers.
    fn stream(seed: u64, make: fn() -> DedupIndex) -> Result<(), String> {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
        let mut idx = make();
        let mut map: HashMap<(u64, u64), Offset> = HashMap::new();
        let habits = [
            Habit::Consecutive,
            Habit::Gapped,
            Habit::Scattered,
            Habit::Top,
            Habit::Acking,
        ];
        let producers = 1 + rng.below(6);
        let mut next_seq: Vec<u64> = (0..producers).map(|_| 1 + rng.below(4)).collect();
        let habit: Vec<Habit> = (0..producers)
            .map(|_| habits[rng.below(habits.len() as u64) as usize])
            .collect();
        let mut input: Vec<u64> = (0..producers).map(|_| rng.below(1 << 20)).collect();
        let mut head = rng.below(1 << 40);
        let mut base = head;
        for step in 0..600 {
            let roll = rng.below(100);
            if roll < 80 {
                let p = rng.below(producers) as usize;
                let seq = match habit[p] {
                    Habit::Consecutive => next_seq[p],
                    Habit::Gapped => next_seq[p] + rng.below(3),
                    Habit::Scattered => rng.below(64),
                    Habit::Top => u64::MAX - rng.below(8),
                    Habit::Acking => {
                        if rng.below(2) == 0 {
                            next_seq[p]
                        } else {
                            input[p] += 1 + rng.below(2);
                            ACK_SEQ_BASE | input[p]
                        }
                    }
                };
                if seq < ACK_SEQ_BASE || !matches!(habit[p], Habit::Acking) {
                    next_seq[p] = seq.saturating_add(1);
                }
                // A duplicate of a held key, now and then, from any producer.
                let key = if rng.below(10) == 0 && !map.is_empty() {
                    let mut all: Vec<(u64, u64)> = map.keys().copied().collect();
                    all.sort_unstable();
                    all[rng.below(all.len() as u64) as usize]
                } else {
                    (p as u64 * 1_000_003, seq)
                };
                let replace = rng.below(8) == 0;
                publish(&mut idx, &mut map, key, &mut head, replace)
                    .map_err(|e| format!("seed {seed} step {step}: {e}"))?;
            } else if roll < 88 {
                // A jump in the head: other records (wills, commits) took offsets.
                head += rng.below(1 << 33);
            } else if roll < 96 {
                // A retention cut to somewhere between the base and the head.
                base += rng.below(head.saturating_sub(base) + 1);
                idx.retain_from(base);
                map.retain(|_, off| off.0 >= base);
            } else {
                // An open: rebuilt from the retained keys in offset order.
                let mut by_off: Vec<(Offset, (u64, u64))> =
                    map.iter().map(|(k, o)| (*o, *k)).collect();
                by_off.sort_unstable();
                let mut again = make();
                for (off, (pid, seq)) in by_off {
                    again.insert(pid, seq, off);
                }
                again.shrink_to_fit();
                if again != idx {
                    return Err(format!(
                        "seed {seed} step {step}: the rebuilt index differs"
                    ));
                }
                idx = again;
            }
            compare(&idx, &map).map_err(|e| format!("seed {seed} step {step}: {e}"))?;
        }
        Ok(())
    }

    fn check_insert(
        idx: &mut DedupIndex,
        map: &mut HashMap<(u64, u64), Offset>,
        pid: u64,
        seq: u64,
        off: u64,
    ) {
        idx.insert(pid, seq, Offset(off));
        map.insert((pid, seq), Offset(off));
        compare(idx, map).expect("exact mapping after insert");
    }

    #[test]
    fn short_producers_stay_loose_and_cross_the_threshold_in_both_directions() {
        for descending in [false, true] {
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for i in 0..PACK_MIN as u64 - 1 {
                let seq = if descending { u64::MAX - i } else { i };
                check_insert(&mut idx, &mut map, 7, seq, i);
                assert!(idx.packed.is_empty());
            }
            // Replace a held key while loose, then carry that exact replacement
            // through promotion (including the widest representable offset span).
            let replacement = if descending { u64::MAX } else { 0 };
            check_insert(&mut idx, &mut map, 7, replacement, u64::MAX);
            let seq = if descending {
                u64::MAX - PACK_MIN as u64 + 1
            } else {
                PACK_MIN as u64 - 1
            };
            check_insert(&mut idx, &mut map, 7, seq, 500);
            assert!(idx.loose.is_empty());
            assert!(idx.packed.contains_key(&7));
            let p = &idx.packed[&7];
            assert!(matches!(p, Packed::Flat(v) if v.capacity() == 1));
            idx.retain_from(4);
            map.retain(|_, off| off.0 >= 4);
            compare(&idx, &map).expect("cut retains replacement and exact keys");
        }
    }

    #[test]
    fn a_bridge_promotes_both_whole_runs_and_packed_inserts_absorb_leftover_runs() {
        let mut idx = DedupIndex::new();
        let mut map = HashMap::new();
        // Two maximal subthreshold runs use the full bounded promotion scratch.
        for seq in (0..PACK_MIN as u64 - 1).chain(PACK_MIN as u64..2 * PACK_MIN as u64 - 1) {
            check_insert(&mut idx, &mut map, 1, seq, seq + 10);
        }
        // Other short runs of the same producer must also survive promotion.
        for seq in (100..100 + PACK_MIN as u64 - 1).chain(200..200 + PACK_MIN as u64 - 1) {
            check_insert(&mut idx, &mut map, 1, seq, seq + 10);
        }
        assert!(idx.packed.is_empty());
        check_insert(&mut idx, &mut map, 1, PACK_MIN as u64 - 1, u64::MAX);
        assert_eq!(idx.loose.len(), 2 * (PACK_MIN - 1));
        check_insert(&mut idx, &mut map, 1, 99, 999); // Entire right loose run joins.
        assert_eq!(idx.loose.len(), PACK_MIN - 1);
        check_insert(&mut idx, &mut map, 1, 200 + PACK_MIN as u64 - 1, 1000);
        assert!(idx.loose.is_empty()); // Entire left loose run joins.
        idx.retain_from(115);
        map.retain(|_, off| off.0 >= 115);
        compare(&idx, &map).expect("retention after three migrations");
    }

    #[test]
    fn gaps_and_retention_do_not_prematurely_promote_or_change_retry_offsets() {
        let mut idx = DedupIndex::new();
        let mut map = HashMap::new();
        for seq in 0..100u64 {
            check_insert(&mut idx, &mut map, 3, seq * 2, seq);
        }
        assert!(idx.packed.is_empty(), "sparse keys keep hash-map storage");
        for seq in 0..PACK_MIN as u64 - 1 {
            check_insert(&mut idx, &mut map, 4, seq, seq % 3);
        }
        idx.retain_from(1);
        map.retain(|_, off| off.0 >= 1);
        compare(&idx, &map).expect("holes in short loose run after retention");
        check_insert(&mut idx, &mut map, 4, PACK_MIN as u64 - 1, 100);
        assert!(!idx.packed.contains_key(&4));
        for seq in 0..PACK_MIN as u64 {
            if !map.contains_key(&(4, seq)) {
                check_insert(&mut idx, &mut map, 4, seq, 200 + seq);
            }
        }
        assert!(idx.packed.contains_key(&4));
        let mut reopened = DedupIndex::new();
        let mut by_offset: Vec<_> = map.iter().map(|(&key, &off)| (off, key)).collect();
        by_offset.sort_unstable();
        for (off, (pid, seq)) in by_offset {
            reopened.insert(pid, seq, off);
        }
        reopened.shrink_to_fit();
        compare(&reopened, &map).expect("rebuild agrees through mixed sparse/packed keys");
        assert_eq!(idx, reopened);
    }

    #[test]
    fn startup_migration_restores_every_removed_key_if_a_neighbour_is_missing() {
        // A plan can be treated as stale without making any existing index
        // state malformed: deliberately omit one of its expected neighbours.
        for missing in [997u64, 1001, 1003] {
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for seq in 996..=1003 {
                if seq != 1000 && seq != missing {
                    let off = u64::MAX - seq;
                    idx.loose.insert((7, seq), off);
                    map.insert((7, seq), Offset(off));
                }
            }
            idx.loose.insert((9, 42), 11);
            map.insert((9, 42), Offset(11));
            map.insert((7, 1000), Offset(123));
            idx.len = map.len(); // The caller accounts for its new key first.
            idx.pack_loose_run(7, 1000, 123, 4, 3);
            assert!(idx.packed.is_empty());
            compare(&idx, &map).expect("migration rollback preserves every key");
            check_insert(&mut idx, &mut map, 7, 1000, 456);
            idx.retain_from(100);
            map.retain(|_, off| off.0 >= 100);
            compare(&idx, &map).expect("retry and cut after rollback agree");
        }
    }

    #[test]
    fn startup_plan_endpoint_overflow_or_underflow_preserves_all_loose_keys() {
        for (seq, left, right) in [(0, 1, 0), (1, 2, 0), (u64::MAX, 0, 1), (u64::MAX - 1, 0, 2)] {
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for key in [0, 1, 2, u64::MAX - 2, u64::MAX - 1, u64::MAX] {
                if key != seq {
                    let off = key.saturating_add(100);
                    idx.loose.insert((7, key), off);
                    map.insert((7, key), Offset(off));
                }
            }
            map.insert((7, seq), Offset(123));
            idx.len = map.len();
            idx.pack_loose_run(7, seq, 123, left, right);
            assert!(idx.packed.is_empty());
            compare(&idx, &map).expect("invalid endpoints preserve every loose key");
            check_insert(&mut idx, &mut map, 7, seq, 456);
        }
    }

    #[test]
    fn startup_plans_at_both_sequence_endpoints_pack_the_complete_valid_run() {
        for (seq, left, right) in [(0, 0, PACK_MIN - 1), (u64::MAX, PACK_MIN - 1, 0)] {
            let first = seq - left as u64;
            let n = left + right + 1;
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for d in 0..n {
                let key = first + d as u64;
                if key != seq {
                    idx.loose.insert((7, key), d as u64 + 1000);
                    map.insert((7, key), Offset(d as u64 + 1000));
                }
            }
            map.insert((7, seq), Offset(123));
            idx.len = map.len();
            idx.pack_loose_run(7, seq, 123, left, right);
            assert!(idx.packed.contains_key(&7));
            assert!(idx.loose.is_empty());
            compare(&idx, &map).expect("valid endpoint plan packs every key exactly once");
            check_insert(&mut idx, &mut map, 7, seq, u64::MAX);
            idx.retain_from(1004);
            map.retain(|_, off| off.0 >= 1004);
            compare(&idx, &map).expect("replacement and cut after endpoint packing agree");
        }
    }

    #[test]
    fn oversized_startup_plan_falls_back_before_removing_any_key() {
        for (left, right) in [(2 * PACK_CAP, 0), (usize::MAX, usize::MAX)] {
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for seq in 1..=4 {
                idx.loose.insert((7, seq), seq + 50);
                map.insert((7, seq), Offset(seq + 50));
            }
            map.insert((7, 5), Offset(100));
            idx.len = map.len();
            idx.pack_loose_run(7, 5, 100, left, right);
            assert!(idx.packed.is_empty());
            compare(&idx, &map).expect("oversized migration keeps all loose keys");
        }
    }

    #[test]
    fn promotions_release_fleet_startup_capacity_without_per_producer_allocations() {
        const PRODUCERS: u64 = 4096;
        let mut idx = DedupIndex::new();
        for seq in 0..PACK_MIN as u64 - 1 {
            for pid in 0..PRODUCERS {
                idx.insert(pid, seq, Offset(seq * PRODUCERS + pid));
            }
        }
        assert!(idx.packed.is_empty());
        assert!(idx.loose.capacity() > 16_000);
        for pid in 0..PRODUCERS {
            idx.insert(
                pid,
                PACK_MIN as u64 - 1,
                Offset((PACK_MIN as u64 - 1) * PRODUCERS + pid),
            );
        }
        assert!(idx.loose.is_empty());
        assert!(
            idx.loose.capacity() <= 64,
            "{} dead slots",
            idx.loose.capacity()
        );
        assert_eq!(idx.packed.len(), PRODUCERS as usize);
        for seq in 0..PACK_MIN as u64 {
            for pid in 0..PRODUCERS {
                assert_eq!(idx.get(pid, seq), Some(Offset(seq * PRODUCERS + pid)));
            }
        }
    }

    /// Every seed, at the shipped chunk size and at sizes small enough that a stream of a
    /// few hundred keys fills, splits, opens and joins chunks.
    #[test]
    fn the_index_answers_every_question_the_map_answers() {
        for threshold in [2, PACK_MIN] {
            tally::set_pack_min(threshold);
            for cap in [CHUNK, 2, 3, 8] {
                tally::set_chunk_cap(cap);
                for seed in 0..400 {
                    if let Err(e) = stream(seed, DedupIndex::new) {
                        panic!("packing {threshold} chunk {cap}: {e}");
                    }
                }
            }
        }
        tally::set_chunk_cap(CHUNK);
        tally::set_pack_min(PACK_MIN);
    }

    #[test]
    fn tree_directory_answers_the_map_across_retries_cuts_and_reopens() {
        tally::set_flat_shift_max(0); // Even a full tail split promotes.
        for cap in [2, 3, 8] {
            tally::set_chunk_cap(cap);
            for seed in 0..400 {
                if let Err(e) = stream(seed, DedupIndex::new) {
                    panic!("tree chunk {cap}: {e}");
                }
            }
        }
        tally::set_chunk_cap(CHUNK);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn ring_directory_answers_the_map_through_wrapped_edits_cuts_and_reopens() {
        tally::set_start_ring(true);
        tally::set_flat_shift_max(usize::MAX); // Keep the forced ring for every edit.
        for cap in [2, 3, 8] {
            tally::set_chunk_cap(cap);
            for seed in 0..400 {
                if let Err(e) = stream(seed, DedupIndex::new) {
                    panic!("ring chunk {cap}: {e}");
                }
            }
        }
        tally::set_chunk_cap(CHUNK);
        tally::set_start_ring(false);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn boxed_ring_preserves_flat_metadata_size_and_short_producer_storage() {
        assert!(
            std::mem::size_of::<Packed>()
                <= std::mem::size_of::<Vec<Chunk>>() + std::mem::size_of::<usize>()
        );
        let mut idx = DedupIndex::new();
        for seq in 0..PACK_MIN as u64 {
            idx.insert(1, seq, Offset(seq));
        }
        assert!(matches!(&idx.packed[&1], Packed::Flat(v) if v.capacity() == 1));
    }

    #[test]
    fn end_edits_wrap_a_ring_and_only_effective_cuts_make_it_contiguous() {
        tally::set_chunk_cap(2);
        tally::set_flat_shift_max(4);
        let mut idx = DedupIndex::new();
        let mut map = HashMap::new();
        for seq in 100..108u64 {
            check_insert(&mut idx, &mut map, 1, seq, seq - 100);
        }
        check_insert(&mut idx, &mut map, 1, 99, 8);
        assert!(
            matches!(&idx.packed[&1], Packed::Ring(v) if !v.as_slices().1.is_empty()),
            "front insert must wrap after converting full flat storage"
        );
        for i in 1..20u64 {
            check_insert(&mut idx, &mut map, 1, 99 - i, 8 + i);
        }
        let before = match &idx.packed[&1] {
            Packed::Ring(v) => (
                v.as_slices().0.as_ptr(),
                v.as_slices().0.len(),
                v.as_slices().1.as_ptr(),
                v.as_slices().1.len(),
            ),
            _ => panic!("end edits stay in the ring"),
        };
        idx.retain_from(0);
        match &idx.packed[&1] {
            Packed::Ring(v) => assert_eq!(
                before,
                (
                    v.as_slices().0.as_ptr(),
                    v.as_slices().0.len(),
                    v.as_slices().1.as_ptr(),
                    v.as_slices().1.len()
                )
            ),
            _ => panic!("unchanged cut cannot promote"),
        }
        idx.retain_from(12);
        map.retain(|_, off| off.0 >= 12);
        compare(&idx, &map).expect("wrapped ring cut agrees");
        assert!(matches!(&idx.packed[&1], Packed::Ring(v) if v.as_slices().1.is_empty()));
        idx.shrink_to_fit();
        compare(&idx, &map).expect("ring shrink preserves mapping");
        tally::set_chunk_cap(CHUNK);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn costly_ring_middle_split_promotes_to_tree_before_editing_chunks() {
        tally::set_chunk_cap(2);
        tally::set_flat_shift_max(2);
        let mut chunks = VecDeque::new();
        let mut map = HashMap::new();
        for i in 0..32u64 {
            let pairs = [(4 * i, 2 * i), (4 * i + 2, 2 * i + 1)];
            chunks.push_back(Chunk::of(&pairs));
            for (seq, off) in pairs {
                map.insert((1, seq), Offset(off));
            }
        }
        let mut idx = DedupIndex::new();
        idx.len = map.len();
        idx.packed.insert(1, Packed::Ring(Box::new(chunks)));
        check_insert(&mut idx, &mut map, 1, 4 * 16 + 1, u64::MAX);
        assert!(matches!(&idx.packed[&1], Packed::Tree(_)));
        idx.retain_from(31);
        map.retain(|_, off| off.0 >= 31);
        compare(&idx, &map).expect("tree cut after ring transition agrees");
        tally::set_chunk_cap(CHUNK);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn append_only_directory_stays_flat_beyond_promotion_threshold() {
        tally::set_chunk_cap(2);
        let mut idx = DedupIndex::new();
        let _ = tally::take_directory_moved();
        for seq in 0..10_000u64 {
            idx.insert(1, seq, Offset(seq));
        }
        assert!(matches!(idx.packed.get(&1), Some(Packed::Flat(v)) if v.len() > FLAT_SHIFT_MAX));
        assert_eq!(tally::take_directory_moved(), 0);
        for seq in 0..10_000u64 {
            assert_eq!(idx.get(1, seq), Some(Offset(seq)));
        }
        tally::set_chunk_cap(CHUNK);
    }

    #[test]
    fn descending_and_interleaved_streams_bound_flat_directory_moves() {
        tally::set_chunk_cap(8);
        for descending in [false, true] {
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            let _ = tally::take_directory_moved();
            for i in 0..100_000u64 {
                let seq = if descending {
                    100_000 - i
                } else if i % 2 == 0 {
                    i / 2
                } else {
                    ACK_SEQ_BASE | (i / 2)
                };
                idx.insert(1, seq, Offset(i));
                map.insert((1, seq), Offset(i));
            }
            assert!(matches!(
                idx.packed.get(&1),
                Some(Packed::Ring(_)) | Some(Packed::Tree(_))
            ));
            // Count the real flat header moves and the single promotion. Subsequent
            // tree edits use std's logarithmic B-tree insertion, not vector shifts.
            let moved = tally::take_directory_moved();
            assert!(
                moved <= 3 * (FLAT_SHIFT_MAX * FLAT_SHIFT_MAX) as u64,
                "{moved}"
            );
            compare(&idx, &map).expect("tree agrees before retention");
            idx.retain_from(50_001);
            map.retain(|_, off| off.0 >= 50_001);
            idx.insert(1, 0, Offset(u64::MAX));
            map.insert((1, 0), Offset(u64::MAX));
            idx.insert(1, u64::MAX, Offset(0));
            map.insert((1, u64::MAX), Offset(0));
            idx.retain_from(50_001);
            map.retain(|_, off| off.0 >= 50_001);
            idx.shrink_to_fit();
            compare(&idx, &map).expect("tree agrees after rekeying and retention");
        }
        tally::set_chunk_cap(CHUNK);
    }

    /// A deterministic comparison against the retained flat algorithm. Run explicitly:
    /// targo --unverified test --release -p astream-broker --lib directory_microbench -- --ignored --nocapture
    #[test]
    #[ignore = "explicit performance comparison"]
    fn directory_microbench() {
        use std::time::Instant;
        for cap in [32, CHUNK] {
            for shape in ["ordered", "acks", "descending"] {
                for n in [100_000u64, 400_000] {
                    for adaptive in [false, true] {
                        tally::set_chunk_cap(cap);
                        tally::set_flat_shift_max(if adaptive {
                            FLAT_SHIFT_MAX
                        } else {
                            usize::MAX
                        });
                        let mut idx = DedupIndex::new();
                        let _ = tally::take_directory_moved();
                        let start = Instant::now();
                        for i in 0..n {
                            let seq = match shape {
                                "acks" if i % 2 == 1 => ACK_SEQ_BASE | (i / 2),
                                "acks" => i / 2,
                                "descending" => n - i,
                                _ => i,
                            };
                            idx.insert(1, seq, Offset(i));
                        }
                        let elapsed = start.elapsed();
                        println!("DIRECTORY shape={shape} chunk_cap={cap} records={n} adaptive={adaptive} ns_per_insert={} header_moves={} heap_bytes_upper={}",
                        elapsed.as_nanos() / u128::from(n), tally::take_directory_moved(), idx.heap_bytes());
                        assert_eq!(idx.len(), n as usize);
                        for i in 0..n {
                            let seq = match shape {
                                "acks" if i % 2 == 1 => ACK_SEQ_BASE | (i / 2),
                                "acks" => i / 2,
                                "descending" => n - i,
                                _ => i,
                            };
                            assert_eq!(idx.get(1, seq), Some(Offset(i)));
                        }
                    }
                }
            }
        }
        tally::set_chunk_cap(CHUNK);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn bulk_helpers_preserve_clamping_and_noncopy_ownership() {
        use std::cell::RefCell;
        use std::rc::Rc;
        struct Tracked {
            id: usize,
            drops: Rc<RefCell<Vec<usize>>>,
        }
        impl Drop for Tracked {
            fn drop(&mut self) {
                self.drops.borrow_mut().push(self.id);
            }
        }
        for bulk in [false, true] {
            tally::set_bulk_moves(bulk);
            for len in 0..16 {
                for idx in (0..len + 3).chain(std::iter::once(usize::MAX)) {
                    let drops = Rc::new(RefCell::new(Vec::new()));
                    let mut values: Vec<_> = (0..len)
                        .map(|id| Tracked {
                            id,
                            drops: Rc::clone(&drops),
                        })
                        .collect();
                    let mut ids: Vec<_> = (0..len).collect();
                    vec_insert_at(
                        &mut values,
                        idx,
                        Tracked {
                            id: len,
                            drops: Rc::clone(&drops),
                        },
                    );
                    ids.insert(idx.min(len), len);
                    assert_eq!(values.iter().map(|v| v.id).collect::<Vec<_>>(), ids);
                    assert!(
                        drops.borrow().is_empty(),
                        "movement cannot drop a live value"
                    );
                    let removed = vec_remove_at(&mut values, idx);
                    let expected = if idx < ids.len() {
                        Some(ids.remove(idx))
                    } else {
                        None
                    };
                    assert_eq!(removed.as_ref().map(|v| v.id), expected);
                    assert!(
                        drops.borrow().is_empty(),
                        "remove returns ownership without dropping"
                    );
                    drop(removed);
                    assert_eq!(*drops.borrow(), expected.into_iter().collect::<Vec<_>>());
                    assert_eq!(values.iter().map(|v| v.id).collect::<Vec<_>>(), ids);
                    drop(values);
                    let mut seen = drops.borrow().clone();
                    seen.sort_unstable();
                    assert_eq!(
                        seen,
                        (0..=len).collect::<Vec<_>>(),
                        "every allocation dropped once"
                    );
                }
            }
        }
        tally::set_bulk_moves(true);
    }

    #[test]
    fn bulk_prefix_preserves_all_copy_suffixes_and_capacity() {
        for bulk in [false, true] {
            tally::set_bulk_moves(bulk);
            for len in 0..64 {
                for cut in (0..len + 3).chain(std::iter::once(usize::MAX)) {
                    let mut values: Vec<_> = (0..len as u64).collect();
                    let capacity = values.capacity();
                    let expected = values[cut.min(len)..].to_vec();
                    vec_drop_prefix(&mut values, cut);
                    assert_eq!(values, expected);
                    assert_eq!(values.capacity(), capacity);
                    let mut zst = vec![(); len];
                    vec_drop_prefix(&mut zst, cut);
                    assert_eq!(zst.len(), len.saturating_sub(cut));
                }
            }
        }
        tally::set_bulk_moves(true);
    }

    /// Same-process comparison with the retained swap loops. Both modes preserve
    /// identical logical movement counters and mappings. Run explicitly in release.
    #[test]
    #[ignore = "explicit bulk movement performance comparison"]
    fn bulk_movement_microbench() {
        use std::time::Instant;
        for shape in ["descending", "scattered", "ordered", "8:1"] {
            for n in [100_000u64, 400_000] {
                for adaptive in [false, true] {
                    tally::set_flat_shift_max(if adaptive { FLAT_SHIFT_MAX } else { usize::MAX });
                    for bulk in [false, true] {
                        tally::set_bulk_moves(bulk);
                        let mut idx = DedupIndex::new();
                        // Force a packed producer before arbitrary seqs arrive,
                        // while still validating all timed replacements below.
                        if shape == "scattered" {
                            for seq in 0..PACK_MIN as u64 {
                                idx.insert(1, seq, Offset(seq));
                            }
                        }
                        let _ = tally::take_offset_moved();
                        let _ = tally::take_directory_moved();
                        let start = Instant::now();
                        for i in 0..n {
                            let seq = if shape == "scattered" {
                                i * 104_729 % n // Coprime to both measured counts.
                            } else {
                                burst_key(shape, i, n)
                            };
                            idx.insert(1, seq, Offset(i + PACK_MIN as u64));
                        }
                        let elapsed = start.elapsed();
                        println!("BULK shape={shape} records={n} adaptive={adaptive} bulk={bulk} ns_per_insert={} offset_moves={} header_moves={} heap_bytes_upper={}",
                            elapsed.as_nanos() / u128::from(n), tally::take_offset_moved(),
                            tally::take_directory_moved(), idx.heap_bytes());
                        for i in 0..n {
                            let seq = if shape == "scattered" {
                                i * 104_729 % n
                            } else {
                                burst_key(shape, i, n)
                            };
                            assert_eq!(idx.get(1, seq), Some(Offset(i + PACK_MIN as u64)));
                        }
                        assert_eq!(idx.len(), n as usize);
                    }
                }
            }
        }
        // Actual ordered retention, including sparse run headers as well as offsets.
        const CUTS: usize = 4096;
        for stride in [1u64, 2] {
            let pairs: Vec<_> = (0..CHUNK as u64).map(|i| (i * stride, i)).collect();
            for cut in [1u64, CHUNK as u64 / 2] {
                for bulk in [false, true] {
                    tally::set_bulk_moves(bulk);
                    let mut chunks: Vec<_> = (0..CUTS).map(|_| Chunk::of(&pairs)).collect();
                    let _ = tally::take_prefix_moved();
                    let start = Instant::now();
                    for c in &mut chunks {
                        assert_eq!(c.retain_from(cut), cut as usize);
                    }
                    let elapsed = start.elapsed();
                    println!("PREFIX stride={stride} cuts={CUTS} cut={cut} bulk={bulk} ns_per_cut={} moved={}",
                        elapsed.as_nanos() / CUTS as u128, tally::take_prefix_moved());
                    for c in &chunks {
                        assert_eq!(c.pairs(), pairs[cut as usize..]);
                    }
                }
            }
        }
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
        tally::set_bulk_moves(true);
    }

    fn directory_key(shape: &str, i: u64, n: u64) -> u64 {
        match shape {
            "scattered" => i * 104_729 % n,
            "ends" if i % 2 == 0 => (1u64 << 32) - i / 2,
            "ends" => (1u64 << 32) + i / 2 + 1,
            _ => burst_key(shape, i, n),
        }
    }

    /// End-heavy and random directory workloads, with the prior tree-only
    /// adaptation retained as a test switch. All modes use bulk offset movement.
    #[test]
    #[ignore = "explicit adaptive directory performance comparison"]
    fn ring_directory_microbench() {
        use std::time::Instant;
        for shape in ["descending", "ends", "scattered", "8:1", "ordered"] {
            for n in [400_000u64, 4_000_000] {
                for mode in ["flat", "legacy_tree", "adaptive"] {
                    tally::set_flat_shift_max(if mode == "flat" {
                        usize::MAX
                    } else {
                        FLAT_SHIFT_MAX
                    });
                    tally::set_ring_dirs(mode != "legacy_tree");
                    let mut idx = DedupIndex::new();
                    if shape == "scattered" {
                        for seq in 0..PACK_MIN as u64 {
                            idx.insert(1, seq, Offset(seq));
                        }
                    }
                    let _ = tally::take_offset_moved();
                    let _ = tally::take_directory_moved();
                    let start = Instant::now();
                    for i in 0..n {
                        idx.insert(1, directory_key(shape, i, n), Offset(i + PACK_MIN as u64));
                    }
                    let elapsed = start.elapsed();
                    let kind = match &idx.packed[&1] {
                        Packed::Flat(_) => "flat",
                        Packed::Ring(_) => "ring",
                        Packed::Tree(_) => "tree",
                    };
                    println!("RING shape={shape} records={n} mode={mode} directory={kind} ns_per_insert={} offset_moves={} header_moves={} heap_bytes_upper={}",
                        elapsed.as_nanos() / u128::from(n), tally::take_offset_moved(), tally::take_directory_moved(), idx.heap_bytes());
                    for i in 0..n {
                        assert_eq!(
                            idx.get(1, directory_key(shape, i, n)),
                            Some(Offset(i + PACK_MIN as u64))
                        );
                    }
                    assert_eq!(idx.len(), n as usize);
                }
            }
        }
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
        tally::set_ring_dirs(true);
    }

    fn seed_burst(idx: &mut DedupIndex) {
        for seq in 0..CHUNK as u64 {
            idx.insert(1, seq, Offset(seq));
        }
        for seq in 0..CHUNK as u64 / 2 {
            idx.insert(1, ACK_SEQ_BASE | seq, Offset(CHUNK as u64 + seq));
        }
    }

    fn burst_key(shape: &str, i: u64, n: u64) -> u64 {
        let ratio = match shape {
            "8:1" => 8,
            "32:1" => 32,
            "1:1" => 1,
            "burst" => return CHUNK as u64 + i,
            "descending" => return n - i,
            _ => return i,
        };
        let group = i / (ratio + 1);
        let within = i % (ratio + 1);
        if within == ratio {
            ACK_SEQ_BASE | group
        } else {
            group * ratio + within
        }
    }

    /// Compare the exact pre-isolation policy in the same binary; all knobs are
    /// test-local. Run explicitly with --release -- --ignored --nocapture.
    #[test]
    #[ignore = "explicit run isolation performance comparison"]
    fn burst_isolation_microbench() {
        use std::time::Instant;
        for shape in ["burst", "8:1", "32:1", "1:1", "descending", "ordered"] {
            for n in [100_000u64, 400_000] {
                for isolate in [false, true] {
                    tally::set_isolate_runs(isolate);
                    let mut idx = DedupIndex::new();
                    let seed = if shape == "burst" {
                        seed_burst(&mut idx);
                        CHUNK as u64 + CHUNK as u64 / 2
                    } else {
                        0
                    };
                    let _ = tally::take_offset_moved();
                    let _ = tally::take_directory_moved();
                    let start = Instant::now();
                    for i in 0..n {
                        idx.insert(1, burst_key(shape, i, n), Offset(seed + i));
                    }
                    let elapsed = start.elapsed();
                    println!("BURST shape={shape} chunk_cap={CHUNK} records={n} isolate={isolate} ns_per_insert={} offset_moves={} header_moves={} heap_bytes_upper={} chunks={}",
                        elapsed.as_nanos() / u128::from(n), tally::take_offset_moved(),
                        tally::take_directory_moved(), idx.heap_bytes(), idx.packed[&1].chunks().count());
                    for i in 0..n {
                        assert_eq!(idx.get(1, burst_key(shape, i, n)), Some(Offset(seed + i)));
                    }
                    assert_eq!(idx.len(), (seed + n) as usize);
                }
            }
        }
        tally::set_isolate_runs(true);
    }

    #[test]
    fn isolation_removes_burst_offset_shifts_in_flat_and_tree_directories() {
        for shift_max in [usize::MAX, 0] {
            tally::set_flat_shift_max(shift_max);
            for isolate in [false, true] {
                tally::set_isolate_runs(isolate);
                let mut idx = DedupIndex::new();
                seed_burst(&mut idx);
                let _ = tally::take_offset_moved();
                for seq in CHUNK as u64..CHUNK as u64 + CHUNK as u64 / 2 {
                    idx.insert(1, seq, Offset(CHUNK as u64 / 2 + seq));
                }
                assert_eq!(
                    tally::take_offset_moved(),
                    if isolate {
                        0
                    } else {
                        (CHUNK * CHUNK / 4) as u64
                    }
                );
                assert!(match &idx.packed[&1] {
                    Packed::Flat(_) => shift_max == usize::MAX,
                    Packed::Ring(_) => false,
                    Packed::Tree(_) => shift_max == 0,
                });
                let mut map = HashMap::new();
                for seq in 0..CHUNK as u64 {
                    map.insert((1, seq), Offset(seq));
                }
                for seq in 0..CHUNK as u64 / 2 {
                    map.insert((1, ACK_SEQ_BASE | seq), Offset(CHUNK as u64 + seq));
                }
                for seq in CHUNK as u64..CHUNK as u64 + CHUNK as u64 / 2 {
                    map.insert((1, seq), Offset(CHUNK as u64 / 2 + seq));
                }
                compare(&idx, &map).expect("burst mapping and retries agree");
                idx.insert(1, 0, Offset(u64::MAX));
                map.insert((1, 0), Offset(u64::MAX));
                idx.retain_from(CHUNK as u64 + CHUNK as u64 / 4);
                map.retain(|_, off| off.0 >= CHUNK as u64 + CHUNK as u64 / 4);
                compare(&idx, &map).expect("retention after isolation agrees");
                let mut rebuilt = DedupIndex::new();
                let mut by_offset: Vec<_> = map.iter().map(|(&key, &off)| (off, key)).collect();
                by_offset.sort_unstable();
                for (off, (pid, seq)) in by_offset {
                    rebuilt.insert(pid, seq, off);
                }
                rebuilt.shrink_to_fit();
                assert_eq!(rebuilt, idx);
            }
        }
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
        tally::set_isolate_runs(true);
    }

    #[test]
    fn long_run_split_uses_its_boundary_and_small_runs_split_in_halves() {
        let ordinary = CHUNK - 31;
        let pairs: Vec<_> = (0..ordinary as u64)
            .map(|seq| (seq, seq))
            .chain((0..31u64).map(|seq| (ACK_SEQ_BASE | seq, ordinary as u64 + seq)))
            .collect();
        let c = Chunk::of(&pairs);
        tally::set_isolate_runs(false);
        assert_eq!(c.split_point(ordinary as u64), CHUNK / 2);
        tally::set_isolate_runs(true);
        assert_eq!(c.split_point(ordinary as u64), ordinary);
        // A nonadjacent hole insertion cannot create a tiny upper chunk through
        // this rule, even when its preceding run happens to be long.
        assert_eq!(c.split_point(ordinary as u64 + 10), CHUNK / 2);
        let pairs: Vec<_> = (0..31u64)
            .map(|seq| (seq, seq))
            .chain((0..ordinary as u64).map(|seq| (ACK_SEQ_BASE | seq, 31 + seq)))
            .collect();
        assert_eq!(Chunk::of(&pairs).split_point(31), CHUNK / 2);
    }

    #[test]
    fn run_boundary_split_handles_the_maximum_sequence() {
        let first = u64::MAX - CHUNK as u64 - 10;
        let seq = first + CHUNK as u64 - 1;
        let pairs: Vec<_> = (0..CHUNK as u64 - 1)
            .map(|d| (first + d, d))
            .chain(std::iter::once((u64::MAX, u64::MAX)))
            .collect();
        for tree in [false, true] {
            let c = Chunk::of(&pairs);
            assert_eq!(c.split_point(seq), CHUNK - 1);
            let mut p = if tree {
                Packed::Tree([(c.first_seq(), c)].into_iter().collect())
            } else {
                Packed::Flat(vec![c])
            };
            assert!(p.put(seq, u64::MAX - 1));
            assert_eq!(p.chunks().count(), 2);
            assert_eq!(p.get(seq), Some(u64::MAX - 1));
            for &(key, off) in &pairs {
                assert_eq!(p.get(key), Some(off));
            }
        }
    }

    #[test]
    fn unequal_rate_streams_separate_once_then_append_without_tail_shifts() {
        for shift_max in [usize::MAX, 0] {
            tally::set_flat_shift_max(shift_max);
            for shape in ["8:1", "32:1"] {
                let mut idx = DedupIndex::new();
                let mut map = HashMap::new();
                let _ = tally::take_offset_moved();
                for i in 0..100_000u64 {
                    let seq = burst_key(shape, i, 100_000);
                    idx.insert(1, seq, Offset(i));
                    map.insert((1, seq), Offset(i));
                }
                // Only the first mixed chunk can shift offsets. Once a long run
                // splits at the boundary, following chunks remain independent.
                assert!(tally::take_offset_moved() <= (CHUNK * CHUNK) as u64);
                assert!(idx.packed[&1].chunks().count() <= 100_000usize.div_ceil(CHUNK) + 2);
                compare(&idx, &map).expect("unequal rate exact mappings");
                // A replica's late replacement creates an out-of-order offset;
                // retention and reopen must still agree with the reference map.
                idx.insert(1, 0, Offset(u64::MAX));
                map.insert((1, 0), Offset(u64::MAX));
                idx.retain_from(50_001);
                map.retain(|_, off| off.0 >= 50_001);
                compare(&idx, &map).expect("cut across separated runs");
                let mut rebuilt = DedupIndex::new();
                let mut by_offset: Vec<_> = map.iter().map(|(&key, &off)| (off, key)).collect();
                by_offset.sort_unstable();
                for (off, (pid, seq)) in by_offset {
                    rebuilt.insert(pid, seq, off);
                }
                rebuilt.shrink_to_fit();
                assert_eq!(rebuilt, idx);
            }
        }
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn descending_gap_backfills_fill_partial_chunks_without_fragmenting() {
        for shift_max in [usize::MAX, 0] {
            tally::set_flat_shift_max(shift_max);
            let mut idx = DedupIndex::new();
            seed_burst(&mut idx);
            for i in 0..4 * CHUNK as u64 {
                let seq = ACK_SEQ_BASE / 2 - i;
                idx.insert(1, seq, Offset(2 * CHUNK as u64 + i));
            }
            assert!(idx.packed[&1].chunks().count() <= 8);
            for i in 0..4 * CHUNK as u64 {
                assert_eq!(
                    idx.get(1, ACK_SEQ_BASE / 2 - i),
                    Some(Offset(2 * CHUNK as u64 + i))
                );
            }
        }
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    #[test]
    fn isolation_requires_forward_adjacency_and_a_real_gap() {
        assert!(isolate_forward_run(10, 11, 100));
        assert!(!isolate_forward_run(10, 11, 12));
        assert!(!isolate_forward_run(10, 50, 100));
        assert!(!isolate_forward_run(u64::MAX, 0, 100));
        assert!(!isolate_forward_run(u64::MAX - 2, u64::MAX - 1, u64::MAX));
    }

    /// Memory and startup CPU for fleets of short-lived producers. Run explicitly:
    /// targo --unverified test --release -p astream-broker --lib short_producer_microbench -- --ignored --nocapture
    #[test]
    #[ignore = "explicit short producer performance comparison"]
    fn short_producer_microbench() {
        use std::time::Instant;
        const PRODUCERS: u64 = 50_000;
        for threshold in [2, PACK_MIN, PACK_CAP] {
            tally::set_pack_min(threshold);
            for keys in [2u64, 3, 4, 8, 16] {
                let mut idx = DedupIndex::new();
                let start = Instant::now();
                for pid in 0..PRODUCERS {
                    for seq in 0..keys {
                        idx.insert(pid, seq, Offset(pid * keys + seq));
                    }
                }
                let insert = start.elapsed();
                let bytes = idx.heap_bytes();
                let start = Instant::now();
                for pid in 0..PRODUCERS {
                    for seq in 0..keys {
                        assert_eq!(idx.get(pid, seq), Some(Offset(pid * keys + seq)));
                    }
                }
                let lookup = start.elapsed();
                idx.shrink_to_fit();
                println!("SHORT_PRODUCER packing_min={threshold} producers={PRODUCERS} keys={keys} ns_per_insert={} ns_per_lookup={} heap_bytes_upper={bytes} shrunk_heap_bytes_upper={}",
                insert.as_nanos() / u128::from(PRODUCERS * keys), lookup.as_nanos() / u128::from(PRODUCERS * keys), idx.heap_bytes());
            }
        }
        tally::set_pack_min(PACK_MIN);
    }

    #[cfg(all(feature = "retention", feature = "relay"))]
    #[test]
    fn keys_below_skips_proven_chunks_in_both_directories() {
        for threshold in [0, usize::MAX] {
            tally::set_chunk_cap(3);
            tally::set_flat_shift_max(threshold);
            let mut idx = DedupIndex::new();
            let mut map = HashMap::new();
            for i in 0..50u64 {
                let seq = 50 - i;
                idx.insert(1, seq, Offset(i + 100));
                map.insert((1, seq), Offset(i + 100));
            }
            // Widen bounds in both directions, then compare every fence and cut.
            for (seq, off) in [(48, 500), (1, 0), (49, u64::MAX)] {
                idx.insert(1, seq, Offset(off));
                map.insert((1, seq), Offset(off));
            }
            for min in [0, 1, 100, 125, 500, u64::MAX] {
                let mut got = idx.keys_below(min);
                got.sort_unstable();
                let mut want: Vec<_> = map
                    .iter()
                    .filter(|(_, off)| off.0 < min)
                    .map(|(&(pid, seq), &off)| (pid, seq, off.0))
                    .collect();
                want.sort_unstable();
                assert_eq!(got, want);
            }
        }
        tally::set_chunk_cap(CHUNK);
        tally::set_flat_shift_max(FLAT_SHIFT_MAX);
    }

    /// The negative control: an index that forgets the last key of each run is caught.
    #[test]
    fn an_index_that_forgets_a_runs_last_key_is_caught() {
        tally::set_pack_min(2);
        for cap in [CHUNK, 3] {
            tally::set_chunk_cap(cap);
            let mut caught = 0;
            for seed in 0..400 {
                if stream(seed, DedupIndex::mutant_forgetting_run_ends).is_err() {
                    caught += 1;
                }
            }
            assert_eq!(caught, 400, "chunk {cap}: every seed catches the mutant");
        }
    }

    #[test]
    fn a_consecutive_producer_costs_four_bytes_a_key_and_its_chunks_one_run_each() {
        let mut idx = DedupIndex::new();
        let mut off = 0u64;
        for seq in 1..=10_000u64 {
            for pid in 0..4u64 {
                idx.insert(pid, seq, Offset(off));
                off += 1;
            }
        }
        idx.shrink_to_fit();
        assert!(idx.loose.is_empty(), "every key runs beside another");
        for p in idx.packed.values() {
            assert!(matches!(p, Packed::Flat(_)), "monotone append stays flat");
            assert_eq!(p.chunks().count(), 10_000usize.div_ceil(CHUNK));
            let mut keys = 0;
            for c in p.chunks() {
                assert_eq!(c.runs.len(), 1);
                assert!(c.ordered);
                assert!(matches!(&c.offs, Offs::Narrow { v, .. } if v.capacity() == v.len()));
                keys += c.len();
            }
            assert_eq!(keys, 10_000);
        }
        let per_key = idx.heap_bytes() as f64 / 40_000.0;
        assert!(per_key < 4.25, "{per_key} B a key");
        assert_eq!(idx.get(3, 10_000), Some(Offset(off - 1)));
        assert_eq!(idx.get(0, 10_001), None);
    }

    /// A producer that publishes and acks under one id (an ack's seq is
    /// `ACK_SEQ_BASE | input`, above every ordinary seq) inserts its ordinary keys below
    /// every ack key it holds. Each insert moves a bounded number of entries, whether its
    /// acks are sparse (runs of one) or run, live or rebuilt by an open in offset order.
    #[test]
    fn a_producer_that_publishes_and_acks_moves_a_bounded_number_of_entries_a_key() {
        const N: u64 = 20_000;
        for stride in [1u64, 3] {
            let mut idx = DedupIndex::new();
            let mut map: HashMap<(u64, u64), Offset> = HashMap::new();
            let _ = tally::take();
            let mut off = 0u64;
            for k in 1..=N {
                for seq in [k, ACK_SEQ_BASE | (k * stride)] {
                    idx.insert(7, seq, Offset(off));
                    map.insert((7, seq), Offset(off));
                    off += 1;
                }
            }
            let (moved, _) = tally::take();
            let bound = 2 * N * 2 * CHUNK as u64;
            assert!(
                moved <= bound,
                "stride {stride}: {moved} entries moved for {} keys, over {bound}",
                2 * N
            );
            if let Err(e) = compare(&idx, &map) {
                panic!("stride {stride}: {e}");
            }
            let mut by_off: Vec<(Offset, (u64, u64))> = map.iter().map(|(k, o)| (*o, *k)).collect();
            by_off.sort_unstable();
            let mut again = DedupIndex::new();
            for (o, (pid, seq)) in by_off {
                again.insert(pid, seq, o);
            }
            let (moved, _) = tally::take();
            assert!(
                moved <= bound,
                "stride {stride}: the rebuild moved {moved} entries, over {bound}"
            );
            assert!(again == idx, "stride {stride}: the rebuild differs");
        }
    }

    /// Producers that publish one key each (`asb pub` with no `--id`: its process id and a
    /// nanosecond seq) cost no more than the map's one entry a key.
    #[test]
    fn one_key_producers_hold_no_more_than_the_map() {
        let mut idx = DedupIndex::new();
        let mut map: HashMap<(u64, u64), Offset> = HashMap::new();
        for pid in 0..50_000u64 {
            let seq = 1_793_000_000_000_000_000 + pid * 7_919;
            idx.insert(pid, seq, Offset(pid));
            map.insert((pid, seq), Offset(pid));
        }
        idx.shrink_to_fit();
        map.shrink_to_fit();
        let want = tally::map_bytes(map.capacity(), std::mem::size_of::<((u64, u64), Offset)>());
        assert!(
            idx.heap_bytes() <= want,
            "the index holds {} B for 50,000 one-key producers, the map {want}",
            idx.heap_bytes()
        );
        if let Err(e) = compare(&idx, &map) {
            panic!("{e}");
        }
    }

    /// Maintenance of unordered replica chunks must depend on overlapping chunks,
    /// rather than every retained key. Count inspected offsets, not wall time.
    #[test]
    fn retention_bounds_skip_unaffected_and_expired_unordered_chunks() {
        let mut chunks: Vec<_> = (0..256u64)
            .map(|i| {
                let base = 10_000 + i * CHUNK as u64;
                let pairs: Vec<_> = (0..CHUNK as u64)
                    .map(|seq| (seq, base + CHUNK as u64 - 1 - seq))
                    .collect();
                Chunk::of(&pairs)
            })
            .collect();
        let _ = tally::take_retention_scan();
        for c in &mut chunks {
            assert!(!c.ordered);
            assert_eq!(c.retain_from(10_000), 0);
        }
        assert_eq!(tally::take_retention_scan(), 0);
        for c in &mut chunks {
            assert_eq!(c.retain_from(u64::MAX), CHUNK);
            assert_eq!(c.len(), 0);
        }
        assert_eq!(tally::take_retention_scan(), 0);
    }

    #[test]
    fn retention_bounds_survive_replacements_and_extreme_offsets() {
        let mut c = Chunk::of(&[(1, 0), (2, 20), (3, 10)]);
        c.set(0, 30); // A conservative low bound remains at zero.
        let _ = tally::take_retention_scan();
        assert_eq!(c.retain_from(5), 0);
        assert_eq!(tally::take_retention_scan(), 3);
        assert_eq!(c.retain_from(5), 0);
        assert_eq!(tally::take_retention_scan(), 0);
        assert_eq!(c.retain_from(10), 0);
        assert_eq!(tally::take_retention_scan(), 0);
        c.set(1, 0); // Replacement must lower the bound again.
        c.insert(4, u64::MAX);
        assert_eq!(c.retain_from(5), 1);
        assert_eq!(c.pairs(), vec![(1, 30), (3, 10), (4, u64::MAX)]);
        c.set(0, u64::MAX);
        assert_eq!(c.retain_from(u64::MAX), 1);
        assert_eq!(c.pairs(), vec![(1, u64::MAX), (4, u64::MAX)]);
        assert_eq!(c.retain_from(u64::MAX), 0);

        let mut c = Chunk::of(&[(1, u64::MAX), (2, 0)]);
        c.set(0, 1); // A stale upper bound must only cause extra work.
        assert_eq!(c.retain_from(2), 2);
        assert_eq!(c.len(), 0);
    }

    /// A retention cut builds no scratch beyond one chunk's keys: not when one stray key
    /// (an ack's) sits mid-log, nor when a re-sent old seq lands inside the order with an
    /// offset above its neighbours'.
    #[test]
    fn a_cut_builds_no_scratch_beyond_a_chunk() {
        const N: u64 = 200_000;
        let mut idx = DedupIndex::new();
        let mut map: HashMap<(u64, u64), Offset> = HashMap::new();
        let mut off = 0u64;
        for seq in 1..=N {
            idx.insert(1, seq, Offset(off));
            map.insert((1, seq), Offset(off));
            off += 1;
            if seq == N / 2 {
                idx.insert(1, ACK_SEQ_BASE | 5, Offset(off));
                map.insert((1, ACK_SEQ_BASE | 5), Offset(off));
                off += 1;
            }
        }
        let bound = 16 * CHUNK;
        for (cut, resend) in [(1_000u64, None), (2_000, Some(1_000u64)), (3_000, None)] {
            if let Some(seq) = resend {
                idx.insert(1, seq, Offset(off));
                map.insert((1, seq), Offset(off));
                off += 1;
            }
            let _ = tally::take();
            idx.retain_from(cut);
            map.retain(|_, o| o.0 >= cut);
            let (_, scratch) = tally::take();
            assert!(
                scratch <= bound,
                "the cut to {cut} built {scratch} B of scratch, over {bound}"
            );
            if let Err(e) = compare(&idx, &map) {
                panic!("cut {cut}: {e}");
            }
        }
    }

    #[test]
    fn offsets_spanning_more_than_a_u32_are_kept_whole_and_narrowed_after_a_cut() {
        tally::set_pack_min(2);
        let mut idx = DedupIndex::new();
        idx.insert(1, 1, Offset(5));
        idx.insert(1, 2, Offset(5 + (1 << 33)));
        let chunk = |idx: &DedupIndex| -> (bool, bool) {
            let c = idx.packed[&1].chunks().next().expect("first chunk");
            (matches!(c.offs, Offs::Wide(_)), c.ordered)
        };
        assert_eq!(chunk(&idx), (true, true));
        assert_eq!(idx.get(1, 1), Some(Offset(5)));
        assert_eq!(idx.get(1, 2), Some(Offset(5 + (1 << 33))));
        idx.retain_from(6);
        assert_eq!(idx.get(1, 1), None);
        assert_eq!(idx.get(1, 2), Some(Offset(5 + (1 << 33))));
        assert_eq!(idx.len(), 1);
        // A re-sent 1 lands before 2 at a later offset: the chunk is unordered, and its
        // filter narrows what fits again.
        idx.insert(1, 1, Offset(6 + (1 << 33)));
        assert_eq!(chunk(&idx), (true, false));
        idx.retain_from(6 + (1 << 33));
        assert_eq!(chunk(&idx), (false, true));
        assert_eq!(idx.entries(), vec![((1, 1), 6 + (1 << 33))]);
    }

    #[test]
    fn a_resent_old_seq_lands_inside_the_order_and_joins_its_neighbours() {
        tally::set_pack_min(2);
        let mut idx = DedupIndex::new();
        for (seq, off) in [(1, 0), (2, 1), (4, 2), (5, 3)] {
            idx.insert(9, seq, Offset(off));
        }
        let runs = |idx: &DedupIndex| {
            idx.packed[&9]
                .chunks()
                .next()
                .expect("first chunk")
                .runs
                .clone()
        };
        assert_eq!(runs(&idx).len(), 2);
        assert!(idx.loose.is_empty());
        idx.insert(9, 3, Offset(4));
        assert_eq!(runs(&idx).len(), 1, "3 joins 1..=2 and 4..=5");
        assert!(!idx.packed[&9].chunks().next().expect("first chunk").ordered);
        assert_eq!(idx.get(9, 3), Some(Offset(4)));
        idx.retain_from(2);
        assert_eq!(
            idx.entries(),
            vec![((9, 3), 4), ((9, 4), 2), ((9, 5), 3)],
            "the cut drops 1 and 2 and keeps the back-filled 3"
        );
        assert_eq!(runs(&idx), vec![Run { seq0: 3, at: 0 }]);
    }

    /// Under the test-only two-key threshold, exercise both neighbours joining a
    /// promotion and subsequent sparse keys joining that producer's packed chunks.
    #[test]
    fn a_lone_key_stays_loose_until_a_neighbour_packs_it() {
        tally::set_pack_min(2);
        let mut idx = DedupIndex::new();
        idx.insert(4, 10, Offset(0));
        idx.insert(4, 12, Offset(1));
        assert_eq!(idx.loose.len(), 2);
        assert!(idx.packed.is_empty());
        idx.insert(4, 11, Offset(2));
        assert!(idx.loose.is_empty());
        assert_eq!(
            idx.packed[&4].chunks().next().expect("first chunk").runs,
            vec![Run { seq0: 10, at: 0 }]
        );
        assert_eq!(
            idx.entries(),
            vec![((4, 10), 0), ((4, 11), 2), ((4, 12), 1)]
        );
        // A sparse key of the packed producer is a run of one; another producer's lone key
        // stays loose; a replace stays where the key is.
        idx.insert(4, 20, Offset(3));
        idx.insert(5, 20, Offset(4));
        idx.insert(4, 20, Offset(5));
        idx.insert(5, 20, Offset(6));
        idx.insert(4, 11, Offset(7));
        assert_eq!(
            idx.packed[&4].chunks().next().expect("first chunk").runs,
            vec![Run { seq0: 10, at: 0 }, Run { seq0: 20, at: 3 }]
        );
        assert_eq!(idx.loose.get(&(5, 20)), Some(&6));
        assert_eq!(idx.loose.len(), 1);
        assert_eq!(idx.get(4, 20), Some(Offset(5)));
        assert_eq!(idx.get(4, 11), Some(Offset(7)));
        assert_eq!(idx.len(), 5);
    }
}
