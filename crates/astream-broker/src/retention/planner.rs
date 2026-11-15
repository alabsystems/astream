// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE PLANNING, I/O-free (see the parent module's docs): the [`Ledger`] of what the hold
//! rules gave up, the tick's stamps, the [`View`] one planning reads, the [`plan`] it takes
//! and the [`Plan`] it answers, the [`oldest`] offset a read can reach, and where each class
//! is whole across a rules change ([`carried_since`]). Nothing here reads a file or a clock:
//! the held store (`held.rs`) and the log (`store.rs`) hand it what they hold and apply what
//! it decides.
//!
//! Its items are the crate's, and in a test or debug build they are also `pub`
//! (`retention`'s re-export, under `cfg(any(test, debug_assertions))`, never a cargo
//! feature), so a simulation of this broker plans every cut as the broker's tick does
//! (aterm's deterministic fabric simulation, its item B05).

use super::{
    record_bytes, slack, Class, Retention, Rule, FLOOR_SCAN_MAX, LEDGER_BYTES_MAX, LEDGER_MAX,
};
use crate::brecord::BrokerRecord;
use crate::store::is_hidden_subject;
use astream_wire::Filter;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

/// THE LEDGER of what the hold rules gave up, record by record (R4's addendum, A9): each
/// record's offset and subject and the order it was given up in, so a tail below the base
/// can be told how many records of its filter it will not be delivered
/// (`BrokerLog::gap_notice`). It is WHOLE FROM an offset:
/// at and above it every record a hold rule gave up is named; below it records went that
/// it does not name. In memory only, never in the held store's file, so a restart starts
/// one whole from the base it opens at. Bounded: past `LEDGER_MAX` records or
/// `LEDGER_BYTES_MAX` bytes of names the lowest offsets go, and it is whole only from
/// above them. A planning collects its give-ups in one ([`Plan::given`]), which the held
/// store's takes when the job lands.
#[derive(Debug, Default)]
pub struct Ledger {
    /// By offset: the order it was given up in (`seq`) and its subject.
    at: BTreeMap<u64, (u64, String)>,
    bytes: usize,
    /// How many records have been named, ever: the `seq` of the newest.
    seq: u64,
    whole: u64,
}

impl Ledger {
    /// Name the record at `off`, of `subject`, given up (nothing below where it is whole).
    pub fn note(&mut self, off: u64, subject: &str) {
        if off < self.whole {
            return;
        }
        self.seq = self.seq.saturating_add(1);
        if let Some((_, old)) = self.at.insert(off, (self.seq, subject.to_string())) {
            self.bytes = self.bytes.saturating_sub(old.len());
        }
        self.bytes = self.bytes.saturating_add(subject.len());
        while self.at.len() > LEDGER_MAX || self.bytes > LEDGER_BYTES_MAX {
            let Some((o, (_, s))) = self.at.pop_first() else {
                break;
            };
            self.bytes = self.bytes.saturating_sub(s.len());
            self.whole = self.whole.max(o.saturating_add(1));
        }
    }

    /// Whole from `off` only, from here: what it names below is forgotten (records went
    /// there that it was never told of: a compaction no rules planned, an open).
    pub fn whole_from(&mut self, off: u64) {
        if off <= self.whole {
            return;
        }
        self.whole = off;
        while let Some((&o, _)) = self.at.first_key_value() {
            if o >= off {
                break;
            }
            if let Some((_, (_, s))) = self.at.pop_first() {
                self.bytes = self.bytes.saturating_sub(s.len());
            }
        }
    }

    /// Take what one planning gave up (`given`), after what this names.
    pub fn take(&mut self, given: Ledger) {
        self.whole_from(given.whole);
        for (off, (_, subject)) in given.at {
            self.note(off, &subject);
        }
    }

    /// From where every record a hold rule gave up is named.
    pub const fn whole(&self) -> u64 {
        self.whole
    }

    /// How many records have been named, ever (the newest's order).
    pub const fn seq(&self) -> u64 {
        self.seq
    }

    /// How many records it names now.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.at.len()
    }

    /// How many records of `filter` it names in `from..to` that a tail TOLD up to `told`
    /// when the ledger stood at `seen` was not counted: each at or above `told`, and below
    /// it each given up since. At most `LEDGER_MAX` subjects matched, under the log lock,
    /// once per landed retention per tail below the base.
    pub fn count(&self, filter: &Filter, from: u64, to: u64, told: u64, seen: u64) -> u64 {
        let mut n = 0u64;
        for (&off, (seq, subject)) in self.at.range(from..to.max(from)) {
            if (off >= told || *seq > seen) && filter.matches_str(subject) {
                n = n.saturating_add(1);
            }
        }
        n
    }
}

/// Whether a [`Ledger`] whole from `from` names every record of `filter` retention gave up
/// from `from` on: every class the filter can reach (`Retention::reached_by`) keeps its
/// records one by one ([`Keep::All`](super::Keep::All) hold), and is whole from at or below `from` (`since`,
/// by class; the base for a class it does not name). The prefix rule's records and a
/// last-value class's are dropped as a range by the cut, never one by one, and below where
/// a class is whole older rules dropped its records: there no count is given.
pub fn counted_from(
    rules: Option<&Retention>,
    since: &[u64],
    base: u64,
    from: u64,
    filter: &Filter,
) -> bool {
    let Some(rules) = rules else {
        return false;
    };
    for c in rules.reached_by(filter) {
        if !rules.rule(c).holds_records() || since.get(c).copied().unwrap_or(base) > from {
            return false;
        }
    }
    true
}

/// A record the held store carries, the time the tick first saw it, and its optional
/// broker-stamped monotone wall time (`bt_ms`, `REQUIREMENTS` R3).
#[derive(Debug, Clone)]
pub struct Held {
    pub rec: Arc<BrokerRecord>,
    pub at_ms: u64,
    pub bt_ms: Option<u64>,
}

/// The tick's stamps: `(head, ms)`, heads rising: every record below `head` was first seen
/// by the tick at `ms` or earlier.
pub type Stamps = Vec<(u64, u64)>;

/// The most stamps a log keeps: past it, two neighbours merge into the later one, so a
/// record never reads older than it is.
pub const STAMPS_MAX: usize = 4096;

/// Stamp every record below `head` the tick has not seen yet with `now` (never before the
/// last stamp), and keep at most `STAMPS_MAX`.
pub fn stamp(stamps: &mut Stamps, head: u64, now: u64) {
    let (last_head, last_ms) = match stamps.last() {
        Some(&s) => s,
        None => (0, 0),
    };
    if head > last_head || stamps.is_empty() {
        stamps.push((head, now.max(last_ms)));
    }
    if stamps.len() > STAMPS_MAX {
        let mut merged = Vec::with_capacity(STAMPS_MAX / 2 + 1);
        let mut it = stamps.chunks(2);
        for pair in &mut it {
            if let Some(&later) = pair.last() {
                merged.push(later);
            }
        }
        *stamps = merged;
    }
}

/// Drop the stamps no retained record needs: every one at or below `base`, but never the
/// newest. That one stays (at or below the base once a cut reached it) so the log still
/// knows when a tick last stamped it: a cut a caller asks for between ticks
/// (`BrokerLog::retain_before_carrying_state`) plans on that clock, and with no stamp left it
/// would stamp what it carries at 0, which the next tick gives up as aged at once. A stamp at
/// or below the base names no retained record, so `stamped_at` never reads it for one.
pub fn prune_stamps(stamps: &mut Stamps, base: u64) {
    let below = stamps
        .iter()
        .take_while(|&&(h, _)| h <= base)
        .count()
        .min(stamps.len().saturating_sub(1));
    if below > 0 {
        // A copy of what stays, not `drain`, whose panic on a range past the length the
        // verified lane does not model.
        *stamps = stamps.get(below..).unwrap_or(&[]).to_vec();
    }
}

/// Cut the stamps back to `head`: every record below it keeps the stamp it had, and none at
/// or above it has one (a stamp past `head` covers only the records below it from here). An
/// open whose log ends below its stamps cuts them so, as the held store's `S` frame replays.
pub fn clamp_stamps(stamps: &mut Stamps, head: u64) {
    let keep = stamps.partition_point(|&(h, _)| h <= head);
    let below = match keep.checked_sub(1) {
        Some(i) => match stamps.get(i) {
            Some(&(h, _)) => h,
            None => 0,
        },
        None => 0,
    };
    let straddle = match stamps.get(keep) {
        Some(&(_, ms)) if below < head => Some(ms),
        _ => None,
    };
    if keep < stamps.len() {
        // A copy of what stays, as `prune_stamps` takes it.
        *stamps = stamps.get(..keep).unwrap_or(&[]).to_vec();
    }
    if let Some(ms) = straddle {
        stamps.push((head, ms));
    }
}

/// When the tick first saw the record at `off`: the first stamp above it, or `now` for one
/// no tick has stamped yet.
pub fn stamped_at(stamps: &[(u64, u64)], off: u64, now: u64) -> u64 {
    let i = stamps.partition_point(|&(h, _)| h <= off);
    match stamps.get(i) {
        Some(&(_, ms)) => ms,
        None => now,
    }
}

/// What the planning reads of one retained record: its offset, its subject (which
/// decides its class) and its bytes ([`record_bytes`]); and, when the entry carries it,
/// the whole record, which the planning needs only for a record below the cut that a
/// hold rule carries.
#[cfg(any(test, debug_assertions))]
pub trait Planned {
    /// The record's offset.
    fn offset(&self) -> u64;
    /// The record's subject.
    fn subject(&self) -> &str;
    /// The record's bytes, as [`record_bytes`] counts them.
    fn bytes(&self) -> u64;
    /// The whole record, or `None` for an entry that carries only the summary.
    fn whole(&self) -> Option<Arc<BrokerRecord>>;
}

#[cfg(any(test, debug_assertions))]
impl Planned for Arc<BrokerRecord> {
    fn offset(&self) -> u64 {
        self.seq.0
    }
    fn subject(&self) -> &str {
        &self.subject
    }
    fn bytes(&self) -> u64 {
        record_bytes(self)
    }
    fn whole(&self) -> Option<Arc<BrokerRecord>> {
        Some(Arc::clone(self))
    }
}

/// One retained record as the planning reads it: what [`Planned`] gives, and its broker time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Entry<'a> {
    pub(crate) offset: u64,
    pub(crate) subject: &'a str,
    pub(crate) bytes: u64,
    pub(crate) bt: Option<u64>,
}

/// The retained records a planning reads, from the base, in offset order: a [`View`]'s
/// slice, or the log's paged tier (`tier.rs`), which keeps no struct per record to slice.
pub(crate) trait Records {
    /// A walk of records' entries with their indices, in offset order.
    type Entries<'a>: Iterator<Item = (usize, Entry<'a>)>
    where
        Self: 'a;
    /// Record `i`'s entry.
    fn entry(&self, i: usize) -> Option<Entry<'_>>;
    /// Records `from..to`'s entries with their indices (`to` clamped to the count), each
    /// [`entry`](Self::entry)'s answer and skipping an index that answers none: what a
    /// planning's walks read, so records held in pages are walked a page at a time.
    fn entries(&self, from: usize, to: usize) -> Self::Entries<'_>;
    /// Record `i` whole, or `None` for records held only as entries.
    fn whole(&self, i: usize) -> Option<Arc<BrokerRecord>>;
}

/// [`Records::entries`] by [`Records::entry`] an index, for records a slice holds.
#[cfg(any(test, debug_assertions))]
pub(crate) struct ByIndex<'a, S: ?Sized> {
    recs: &'a S,
    i: usize,
    hi: usize,
}

#[cfg(any(test, debug_assertions))]
impl<'a, S: Records + ?Sized> ByIndex<'a, S> {
    /// Records `from..to`'s entries (`to` at most their count).
    pub(crate) fn new(recs: &'a S, from: usize, to: usize) -> ByIndex<'a, S> {
        ByIndex {
            recs,
            i: from,
            hi: to,
        }
    }
}

#[cfg(any(test, debug_assertions))]
impl<'a, S: Records + ?Sized> Iterator for ByIndex<'a, S> {
    type Item = (usize, Entry<'a>);

    fn next(&mut self) -> Option<(usize, Entry<'a>)> {
        while self.i < self.hi {
            let i = self.i;
            self.i = i.saturating_add(1);
            if let Some(e) = self.recs.entry(i) {
                return Some((i, e));
            }
        }
        None
    }
}

/// A [`View`]'s records: the slice, and the broker times beside it.
#[cfg(any(test, debug_assertions))]
struct Listed<'a, R> {
    records: &'a [R],
    bts: &'a [Option<u64>],
}

#[cfg(any(test, debug_assertions))]
impl<R: Planned> Records for Listed<'_, R> {
    type Entries<'a>
        = ByIndex<'a, Self>
    where
        Self: 'a;

    fn entries(&self, from: usize, to: usize) -> ByIndex<'_, Self> {
        ByIndex::new(self, from, to.min(self.records.len()))
    }

    fn entry(&self, i: usize) -> Option<Entry<'_>> {
        let r = self.records.get(i)?;
        Some(Entry {
            offset: r.offset(),
            subject: r.subject(),
            bytes: r.bytes(),
            bt: self.bts.get(i).copied().flatten(),
        })
    }

    fn whole(&self, i: usize) -> Option<Arc<BrokerRecord>> {
        self.records.get(i)?.whole()
    }
}

/// What the planning reads beside the records: a [`View`] without them.
pub(crate) struct Scene<'a> {
    pub(crate) base: u64,
    pub(crate) ceiling: u64,
    pub(crate) stamps: &'a [(u64, u64)],
    pub(crate) groups: &'a HashMap<String, u64>,
    pub(crate) held: &'a BTreeMap<u64, Held>,
    pub(crate) now: u64,
}

/// What the planning reads: the log as one moment saw it.
#[cfg(any(test, debug_assertions))]
pub struct View<'a, R: Planned = Arc<BrokerRecord>> {
    /// The log's base: its oldest retained offset.
    pub base: u64,
    /// The cut never rises above it: the subscriber-visible head (and, replicated, what every
    /// follower holds).
    pub ceiling: u64,
    /// The retained records, from the base, in offset order (whole, or summaries).
    pub records: &'a [R],
    /// Optional broker-stamped wall times aligned with `records`.
    pub record_bts: &'a [Option<u64>],
    /// The tick's stamps ([`stamp`]), taken at `now` before the planning.
    pub stamps: &'a [(u64, u64)],
    /// The groups' durable commits (`upto`, inclusive).
    pub groups: &'a HashMap<String, u64>,
    /// The held store, by offset (every one below the base).
    pub held: &'a BTreeMap<u64, Held>,
    /// The tick's clock, in ms: what ages are measured against.
    pub now: u64,
}

/// Why a hold rule gave a record up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Why {
    /// Every reader it names read it.
    Read,
    /// Past the rule's age.
    Aged,
    /// Past the class's bytes.
    Bytes,
}

/// What one planning decided: the cut, the records newly held, the held ones given up, and
/// the floors that rise.
#[derive(Debug, Default)]
pub struct Plan {
    /// The cut: the log's base after the planning, at or above the view's base and never
    /// above its ceiling.
    pub cut: u64,
    /// Records below the cut, at or above the base, to carry: each with its stamp.
    pub carry: Vec<Held>,
    /// Indices into `View::records` (with `(at_ms, bt_ms)`) of carried records whose view
    /// entry held only a summary (`Planned::whole` was `None`).
    pub(crate) carry_unloaded: Vec<(usize, u64, Option<u64>)>,
    /// Held offsets (below the base) given up.
    pub remove: Vec<u64>,
    /// Subject floors that rise, to the offset after the newest record of it given up.
    pub floors: BTreeMap<String, u64>,
    /// Unread records given up, by subject and why: how many, for the log line.
    pub lost: BTreeMap<(String, Why), u64>,
    /// Every record given up, read or not, one by one: what the held store's [`Ledger`]
    /// takes when the job lands.
    pub given: Ledger,
    /// Each class's bytes in the retained suffix the cut keeps.
    pub kept: Vec<u64>,
    /// What the planning leaves each class before it is past its own bytes, retained above
    /// the cut and held both: the class can take this many more bytes of its own records
    /// before it asks for a tick. `u64::MAX` for a class that bounds no bytes; `0` for one
    /// still past them (a caller's cut below the rules'); a quarter of its bytes for one
    /// the cut could not bring within them because the visible head held it back, so it
    /// does not ask again for every record while that lasts.
    pub room: Vec<u64>,
    /// The least of [`room`](Self::room): `u64::MAX` with no class that bounds bytes.
    pub headroom: u64,
}

impl Plan {
    /// Whether the plan changes nothing.
    pub fn is_empty(&self, base: u64) -> bool {
        self.cut <= base
            && self.carry.is_empty()
            && self.carry_unloaded.is_empty()
            && self.remove.is_empty()
            && self.floors.is_empty()
    }

    fn give_up(&mut self, offset: u64, subject: &str, why: Why) {
        let floor = offset.saturating_add(1);
        let f = self.floors.entry(subject.to_string()).or_insert(0);
        *f = (*f).max(floor);
        self.given.note(offset, subject);
        if why != Why::Read {
            let n = self.lost.entry((subject.to_string(), why)).or_insert(0);
            *n = n.saturating_add(1);
        }
    }
}

/// What one walk of the retained records finds: each class's bytes in them, and the
/// offset just above the newest prefix record past its rule's age (the base for none).
struct Walk {
    bytes: Vec<u64>,
    aged_to: u64,
}

fn walk<S: Records + ?Sized>(rules: &Retention, v: &Scene<'_>, recs: &S) -> Walk {
    let mut bytes = rules.per_class(0u64);
    let mut aged_to = v.base;
    for (_, rec) in recs.entries(0, usize::MAX) {
        let c = rules.class_of(rec.subject);
        if let Some(slot) = bytes.get_mut(c) {
            *slot = slot.saturating_add(rec.bytes);
        }
        let rule = rules.rule(c);
        if rule.class == Class::Prefix {
            let age = v
                .now
                .saturating_sub(stamped_at(v.stamps, rec.offset, v.now));
            if rule.aged(age) {
                aged_to = aged_to.max(rec.offset.saturating_add(1));
            }
        }
    }
    Walk { bytes, aged_to }
}

/// What each class may keep after the planning: its `max_bytes`, or, for a class past them
/// (`has`, retained and still-wanted held), the lower of them and what it has less a
/// [`slack`] (`u64::MAX` for a class that bounds no bytes).
fn limits(rules: &Retention, retained: &[u64], held: &[u64]) -> Vec<u64> {
    let mut out = rules.per_class(u64::MAX);
    for (c, slot) in out.iter_mut().enumerate() {
        let Some(max) = rules.rule(c).max_bytes else {
            continue;
        };
        let has = match (retained.get(c), held.get(c)) {
            (Some(&r), Some(&h)) => r.saturating_add(h),
            (Some(&r), None) => r,
            (None, Some(&h)) => h,
            (None, None) => 0,
        };
        *slot = if has > max {
            max.min(has.saturating_sub(slack(max)))
        } else {
            max
        };
    }
    out
}

/// THE CUT the rules take on `v`: walking up from the base, each class's oldest retained
/// records go below the cut until what the class keeps above it is within its `limit`, and
/// every prefix record past its age is below it. Not yet held to the ceiling.
fn natural_cut<S: Records + ?Sized>(
    rules: &Retention,
    v: &Scene<'_>,
    recs: &S,
    w: &Walk,
    limit: &[u64],
) -> u64 {
    let mut need = rules.per_class(0u64);
    let mut left = 0usize;
    for (c, n) in need.iter_mut().enumerate() {
        let has = w.bytes.get(c).copied().unwrap_or(0);
        let lim = limit.get(c).copied().unwrap_or(u64::MAX);
        *n = has.saturating_sub(lim);
        if *n > 0 {
            left = left.saturating_add(1);
        }
    }
    let mut cut = v.base;
    for (_, rec) in recs.entries(0, usize::MAX) {
        if left == 0 && rec.offset >= w.aged_to {
            break;
        }
        let c = rules.class_of(rec.subject);
        if let Some(n) = need.get_mut(c) {
            if *n > 0 {
                *n = n.saturating_sub(rec.bytes);
                if *n == 0 {
                    left = left.saturating_sub(1);
                }
            }
        }
        cut = rec.offset.saturating_add(1);
    }
    cut.max(w.aged_to)
}

/// THE PLANNING: the cut (`forced`, when the caller names one, else `natural_cut`), and
/// what the hold rules do about it — carry each record below it that a [`Keep::All`](super::Keep::All) hold
/// rule still wants, give up the held records read or aged since, and keep each class
/// within its limit (its bytes, at least a `slack` under what it had when it was past
/// them) by giving up its oldest, retained above the cut counted first — and the room each
/// class has left.
/// [`plan`], over a view whose entries may be summaries: `load(i)` gives the whole record
/// at index `i` of `v.records` for an entry that does not carry it, and is asked only for
/// a record below the cut that a hold rule carries. A record that cannot be loaded cannot
/// be carried, so the planning changes nothing (the cut stays at the base) rather than
/// cut away a record its rule still holds.
#[cfg(any(test, debug_assertions))]
pub fn plan_with<R: Planned>(
    rules: &Retention,
    v: &View<'_, R>,
    forced: Option<u64>,
    load: impl Fn(usize) -> Option<Arc<BrokerRecord>>,
) -> Plan {
    let mut p = plan(rules, v, forced);
    for (idx, at_ms, bt_ms) in std::mem::take(&mut p.carry_unloaded) {
        let Some(rec) = load(idx) else {
            return Plan {
                cut: v.base,
                headroom: u64::MAX,
                room: rules.per_class(u64::MAX),
                ..Plan::default()
            };
        };
        p.carry.push(Held { rec, at_ms, bt_ms });
    }
    p
}

/// THE PLANNING over a [`View`]: its slice of records and the broker times beside them
/// (the broker's own tick plans the same way over its packed tier, `plan_over`).
#[cfg(any(test, debug_assertions))]
pub fn plan<R: Planned>(rules: &Retention, v: &View<'_, R>, forced: Option<u64>) -> Plan {
    let scene = Scene {
        base: v.base,
        ceiling: v.ceiling,
        stamps: v.stamps,
        groups: v.groups,
        held: v.held,
        now: v.now,
    };
    let recs = Listed {
        records: v.records,
        bts: v.record_bts,
    };
    plan_over(rules, &scene, &recs, forced)
}

/// THE PLANNING over `v` and its retained records `recs`, from its base in offset order: a
/// record `recs` cannot give whole is carried as `Plan::carry_unloaded`, for the caller to
/// load.
pub(crate) fn plan_over<S: Records + ?Sized>(
    rules: &Retention,
    v: &Scene<'_>,
    recs: &S,
    forced: Option<u64>,
) -> Plan {
    let mut p = Plan {
        cut: v.base,
        headroom: u64::MAX,
        ..Plan::default()
    };
    // The class's held candidates, oldest first: (offset, bytes, from the store or new).
    let mut by_class: Vec<Vec<(u64, u64, bool)>> = rules.per_class(Vec::new());
    let mut held = rules.per_class(0u64);
    for (&off, h) in v.held {
        let c = rules.class_of(&h.rec.subject);
        let rule = rules.rule(c);
        // A record its rule no longer holds (the rules changed) goes as a read one does.
        let why = if !rule.holds_records() || rule.read(&h.rec.subject, off, v.groups) {
            Some(Why::Read)
        } else if rule.aged(v.now.saturating_sub(h.at_ms)) {
            Some(Why::Aged)
        } else {
            None
        };
        match why {
            Some(w) => {
                p.remove.push(off);
                p.give_up(off, &h.rec.subject, w);
            }
            None => {
                let b = record_bytes(&h.rec);
                if let Some(list) = by_class.get_mut(c) {
                    list.push((off, b, false));
                }
                if let Some(slot) = held.get_mut(c) {
                    *slot = slot.saturating_add(b);
                }
            }
        }
    }
    let w = walk(rules, v, recs);
    let limit = limits(rules, &w.bytes, &held);
    let want = match forced {
        Some(c) => c,
        None => natural_cut(rules, v, recs, &w, &limit),
    };
    let cut = want.min(v.ceiling).max(v.base);
    // The visible head held the cut back: a class may still be past its bytes.
    let capped = want > cut;
    p.cut = cut;
    let kept = kept_bytes(rules, v, recs, cut);
    let below = usize::try_from(cut.saturating_sub(v.base)).unwrap_or(usize::MAX);
    let mut fresh: BTreeMap<u64, (usize, u64, Option<u64>)> = BTreeMap::new();
    for (idx, rec) in recs.entries(0, below) {
        let (off, subject) = (rec.offset, rec.subject);
        if is_hidden_subject(subject) {
            continue;
        }
        let c = rules.class_of(subject);
        let rule = rules.rule(c);
        if !rule.holds_records() {
            continue;
        }
        let at_ms = stamped_at(v.stamps, off, v.now);
        if rule.read(subject, off, v.groups) {
            p.give_up(off, subject, Why::Read);
        } else if rule.aged(v.now.saturating_sub(at_ms)) {
            p.give_up(off, subject, Why::Aged);
        } else {
            if let Some(list) = by_class.get_mut(c) {
                list.push((off, rec.bytes, true));
            }
            fresh.insert(off, (idx, at_ms, rec.bt));
        }
    }
    // Each class within its limit: what it keeps above the cut first, then its held
    // records, the newest kept and the oldest given up.
    let mut room = rules.per_class(u64::MAX);
    for (c, list) in by_class.iter().enumerate() {
        let rule = rules.rule(c);
        let Some(max) = rule.max_bytes else {
            continue;
        };
        let above = kept.get(c).copied().unwrap_or(0);
        let budget = limit.get(c).copied().unwrap_or(max).saturating_sub(above);
        let mut total: u64 = 0;
        for &(_, b, _) in list {
            total = total.saturating_add(b);
        }
        for &(off, b, is_new) in list {
            if total <= budget {
                break;
            }
            total = total.saturating_sub(b);
            let subj = if is_new {
                match fresh.remove(&off) {
                    Some((idx, _, _)) => recs.entry(idx).map(|e| e.subject),
                    None => None,
                }
            } else {
                p.remove.push(off);
                match v.held.get(&off) {
                    Some(h) => Some(h.rec.subject.as_str()),
                    None => None,
                }
            };
            if let Some(subj) = subj {
                p.give_up(off, subj, Why::Bytes);
            }
        }
        let used = above.saturating_add(total);
        let left = if used <= max {
            max.saturating_sub(used)
        } else if capped {
            slack(max)
        } else {
            0
        };
        if let Some(slot) = room.get_mut(c) {
            *slot = left;
        }
        p.headroom = p.headroom.min(left);
    }
    p.kept = kept;
    p.room = room;
    for (idx, at_ms, bt_ms) in fresh.into_values() {
        match recs.whole(idx) {
            Some(whole) => p.carry.push(Held {
                rec: whole,
                at_ms,
                bt_ms,
            }),
            None => p.carry_unloaded.push((idx, at_ms, bt_ms)),
        }
    }
    p.remove.sort_unstable();
    p.remove.dedup();
    p
}

/// Each class's bytes in the retained suffix from `cut`.
fn kept_bytes<S: Records + ?Sized>(
    rules: &Retention,
    v: &Scene<'_>,
    recs: &S,
    cut: u64,
) -> Vec<u64> {
    let mut acc = rules.per_class(0u64);
    let skip = usize::try_from(cut.saturating_sub(v.base)).unwrap_or(usize::MAX);
    for (_, rec) in recs.entries(skip, usize::MAX) {
        let c = rules.class_of(rec.subject);
        if let Some(slot) = acc.get_mut(c) {
            *slot = slot.saturating_add(rec.bytes);
        }
    }
    acc
}

/// The OLDEST offset of `filter`: the offset AT AND ABOVE WHICH THE FILTER IS COMPLETE, every
/// record of it the rules still want readable and none given up. The greatest of the floors
/// of what it matches: the base for what the prefix rule and the last-value rules can match
/// (and for everything, with no rules); for what a [`Keep::All`](super::Keep::All) hold rule can match, from
/// where its class is whole (`since`, by class: the base for a class it does not name), the
/// `spill` (the floors folded together to keep them bounded) and the floor of every matching
/// subject that gave records up. Past `FLOOR_SCAN_MAX` subjects it answers the greatest of
/// all floors (`floor_max`) instead: larger, never smaller. So it is not the lowest record a
/// read of the filter can reach: of a filter whose subjects have different floors (two
/// reader groups' mail, a hold class beside the prefix or a last-value class), records some
/// subject still holds can lie below it, which a tail and a told `Fetch`
/// (`BrokerLog::fetch_told`) deliver, and the range below it is told as a gap notice.
pub fn oldest(
    rules: Option<&Retention>,
    base: u64,
    since: &[u64],
    floors: &BTreeMap<String, u64>,
    spill: u64,
    floor_max: u64,
    filter: &Filter,
) -> u64 {
    let Some(rules) = rules else {
        return base;
    };
    let mut o = 0u64;
    let mut holds = false;
    for c in rules.reached_by(filter) {
        if rules.rule(c).holds_records() {
            holds = true;
            o = o.max(since.get(c).copied().unwrap_or(base).min(base));
        } else {
            o = o.max(base);
        }
    }
    if !holds {
        return o;
    }
    o = o.max(spill.min(base));
    let prefix = crate::store::literal_prefix(filter);
    let mut seen = 0usize;
    let range = floors.range::<str, _>((
        std::ops::Bound::Included(prefix),
        std::ops::Bound::Unbounded,
    ));
    for (subject, &f) in range {
        if !subject.starts_with(prefix) {
            break;
        }
        seen = seen.saturating_add(1);
        if seen > FLOOR_SCAN_MAX {
            return o.max(floor_max.min(base));
        }
        if filter.matches_str(subject) {
            o = o.max(f.min(base));
        }
    }
    o
}

/// FROM WHERE EACH CLASS OF `new` IS WHOLE when it replaces `old` at the base `base`, `old`
/// whole from `old_since` class by class: a class that keeps records ([`Keep::All`](super::Keep::All) hold)
/// takes the latest of where the old classes its subjects can have been in became whole —
/// the old classes whose filter can share a subject with its own (`Retention::reached_by`),
/// or, for the default class, every old class whose filter no new rule names and the old
/// default — an old class that kept none of them below the base (the prefix, a last-value
/// rule) counting as the base, since its records there were dropped, not carried. Every
/// other class, and every class without old rules, starts at the base. SOUND: a class is
/// never answered whole from below where some subject of it was last kept whole, so a
/// rules change that only retunes a class's bounds keeps its held records readable, and a
/// class new to the rules is told where its records start.
pub fn carried_since(
    old: Option<&Retention>,
    old_since: &[u64],
    new: &Retention,
    base: u64,
) -> Vec<u64> {
    let mut out = new.per_class(base);
    let Some(old) = old else {
        return out;
    };
    let named: Vec<&str> = new.rules.iter().filter_map(Rule::filter).collect();
    for (c, slot) in out.iter_mut().enumerate() {
        if !new.rule(c).holds_records() {
            continue;
        }
        let from = match new.rules.get(c).and_then(|r| r.filter.as_ref()) {
            Some(f) => old.reached_by(f),
            None => old.reached_by_default_of(&named),
        };
        let mut since = 0u64;
        for o in from {
            let s = if old.rule(o).holds_records() {
                old_since.get(o).copied().unwrap_or(base)
            } else {
                base
            };
            since = since.max(s);
        }
        *slot = since.min(base);
    }
    out
}
