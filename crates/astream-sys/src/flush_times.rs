// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! HOW LONG THIS PROCESS'S FLUSHES TOOK, and when the slow ones ran ([`flush_times`]).
//!
//! Every flush the crate makes ([`full_sync`](crate::full_sync),
//! [`full_sync_data`](crate::full_sync_data), [`barrier_sync`](crate::barrier_sync),
//! [`plain_fsync`](crate::plain_fsync)) goes through one door, [`timed`]: at its entry the
//! call is counted in its kind ([`flush_tally`](crate::flush_tally), exact as the call
//! begins) and the clock is read; at its exit the clock is read again, the span is added to
//! its kind's total, and a span slower than [`SLOW_FLUSH_NS`] is kept, with its kind, start
//! and end, in a ring of the last [`SLOW_FLUSHES_KEPT`].
//!
//! # The clock
//!
//! [`clock_ns`] is the one clock every time here is on, and a caller that wants to line its
//! own spans up with a flush reads it too. On Apple it is `CLOCK_UPTIME_RAW` (the cordon's
//! `clock_gettime_nsec_np`), the clock `mach_absolute_time` counts and std's `Instant` reads
//! there: it is the machine's, so two processes' readings on one boot compare, and it stops
//! while the machine sleeps ([`FlushClock::Machine`]). Elsewhere it is an `Instant` since this
//! process first read it, which compares only within the process ([`FlushClock::Process`]):
//! the cordon declares no clock off Apple. [`FLUSH_CLOCK`] says which one this build reads.
//!
//! # The ring
//!
//! Lock-free, for any number of flushing threads: a slow flush takes the next index
//! (`fetch_add`), claims the slot that index falls in by a compare-and-swap of the slot's tag
//! to the odd "being written" value of its index, writes its fields and publishes the even
//! "written" value; a reader takes a slot whose tag reads even, and the same before and after
//! its fields (a sequence lock). A writer that finds its slot being written, or already holding
//! a later index, keeps nothing: the count still has it ([`FlushTimes::slow_count`]), and only
//! 64 slow flushes running at once within one claim could make that happen.
//!
//! # Which flushes a reading missed
//!
//! Every kept flush carries its index ([`SlowFlush::index`]), the one the slot's tag names, so
//! a reader can tell exactly which slow flushes a ring lost, to its turning over or to a write
//! the reading raced. A window between two readings is the slow flushes indexed from the
//! earlier one's [`FlushTimes::slow_count`] to the later one's, and the later reading holds the
//! window whole exactly when its ring holds every index in it ([`FlushTimes::missed`] is 0);
//! otherwise it says how many it lost, at whatever count the process has reached. Two orders
//! make the indices and the count agree. A writer takes its index after it reads its flush's
//! end, with release ordering, and a reading loads the count after it reads the slots, with
//! acquire ordering: so every flush the ring holds has an index below its reading's count, and
//! every index below a reading's count is a flush whose end no `clock_ns` read after that
//! reading precedes (on a clock whose readings follow the order of the threads' memory
//! accesses, as a monotonic clock's do).
//!
//! # Which flushes a reading cannot see yet
//!
//! A flush still running as a reading is taken, or between its end and its index, is in
//! neither its count nor its ring: it is a later reading's. The reading counts it instead
//! ([`FlushTimes::running`]): every call through the door that had begun and not yet
//! returned. A call returns once its span is noted (its index taken and its slot written, when
//! slow), with release ordering, and a reading loads the returned calls (acquire) before the
//! begun ones and both before the count, so a reading whose `running` is 0 saw every call
//! begun by then return with its index below its count: its ring and count account for every
//! slow flush that began before it, and a window of it held whole holds each one that ran
//! there. A reading with calls running cannot say that of them.
//!
//! # What the tests check of these orders
//!
//! The tests check what the orders give wherever a reading can see it: every held index below
//! its reading's count, every window's misses exactly, `running` counting each call inside the
//! door. They do not tell the release and acquire orders above from relaxed ones: a reordering
//! that only a weaker memory order allows is not one a deterministic test provokes, and a
//! stress test that waited for one would be timing-dependent. Those orders are argued here,
//! from the memory model, and not tested.

use std::io;
use std::sync::atomic::{fence, AtomicU64, AtomicU8, Ordering};

/// A flush slower than this many nanoseconds (1 ms) is kept in the ring ([`flush_times`]).
pub const SLOW_FLUSH_NS: u64 = 1_000_000;

/// How many slow flushes the ring keeps: the last 64.
pub const SLOW_FLUSHES_KEPT: usize = 64;

/// Which of the crate's flushes a call was: the kinds [`FlushTally`](crate::FlushTally) counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FlushKind {
    /// [`full_sync`](crate::full_sync) or [`full_sync_data`](crate::full_sync_data).
    Full,
    /// [`barrier_sync`](crate::barrier_sync).
    Barrier,
    /// [`plain_fsync`](crate::plain_fsync).
    Plain,
}

impl FlushKind {
    /// Every kind, in [`FlushTally`](crate::FlushTally)'s order.
    pub const ALL: [FlushKind; 3] = [FlushKind::Full, FlushKind::Barrier, FlushKind::Plain];

    /// Its name: `full`, `barrier` or `plain`.
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            FlushKind::Full => "full",
            FlushKind::Barrier => "barrier",
            FlushKind::Plain => "plain",
        }
    }

    /// The kind [`FlushKind::word`] names.
    #[must_use]
    pub fn from_word(word: &str) -> Option<FlushKind> {
        FlushKind::ALL.into_iter().find(|k| k.word() == word)
    }

    const fn index(self) -> usize {
        match self {
            FlushKind::Full => 0,
            FlushKind::Barrier => 1,
            FlushKind::Plain => 2,
        }
    }
}

/// Which clock [`clock_ns`] reads ([`FLUSH_CLOCK`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FlushClock {
    /// The machine's monotonic clock (Apple's `CLOCK_UPTIME_RAW`): readings in two processes
    /// on one boot compare.
    Machine,
    /// An `Instant` since this process first read it: readings compare within the process
    /// only.
    Process,
}

impl FlushClock {
    /// Its name: `machine` or `process` (one length, so a fixed-width record that carries it
    /// is one length either way).
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            FlushClock::Machine => "machine",
            FlushClock::Process => "process",
        }
    }

    /// The clock [`FlushClock::word`] names.
    #[must_use]
    pub fn from_word(word: &str) -> Option<FlushClock> {
        [FlushClock::Machine, FlushClock::Process]
            .into_iter()
            .find(|c| c.word() == word)
    }
}

/// The clock this build's [`clock_ns`] reads.
pub const FLUSH_CLOCK: FlushClock = if cfg!(target_vendor = "apple") {
    FlushClock::Machine
} else {
    FlushClock::Process
};

/// Now, in nanoseconds, on the clock every time in [`flush_times`] is on ([`FLUSH_CLOCK`]
/// says which; the module docs say what each compares with).
#[must_use]
pub fn clock_ns() -> u64 {
    #[cfg(target_vendor = "apple")]
    {
        crate::apple::uptime_raw_ns()
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        static EPOCH: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
        let epoch = *EPOCH.get_or_init(std::time::Instant::now);
        u64::try_from(epoch.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }
}

/// One flush slower than [`SLOW_FLUSH_NS`], as the ring keeps it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SlowFlush {
    /// Its place among this process's slow flushes, from 0: each takes the next as it returns,
    /// so no two share one, and a reader names a flush its ring lost by the index missing
    /// ([`FlushTimes::missed`]).
    pub index: u64,
    /// Which flush it was.
    pub kind: FlushKind,
    /// [`clock_ns`] as the call began, after its count.
    pub start_ns: u64,
    /// [`clock_ns`] as the call returned.
    pub end_ns: u64,
}

impl SlowFlush {
    /// How long it took.
    #[must_use]
    pub const fn ns(&self) -> u64 {
        self.end_ns.saturating_sub(self.start_ns)
    }
}

/// How long this process's flushes took ([`flush_times`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlushTimes {
    /// The clock every time here is on ([`FLUSH_CLOCK`]).
    pub clock: FlushClock,
    /// Nanoseconds spent in [`full_sync`](crate::full_sync) and
    /// [`full_sync_data`](crate::full_sync_data) calls that have returned.
    pub full_ns: u64,
    /// Nanoseconds spent in [`barrier_sync`](crate::barrier_sync) calls that have returned.
    pub barrier_ns: u64,
    /// Nanoseconds spent in [`plain_fsync`](crate::plain_fsync) calls that have returned.
    pub plain_ns: u64,
    /// How many flushes slower than [`SLOW_FLUSH_NS`] have returned and taken their index:
    /// every one, kept in [`FlushTimes::slow`] or not, read after the ring, so each kept index
    /// is below it.
    pub slow_count: u64,
    /// The slow flushes the ring holds, oldest first (by [`SlowFlush::index`], each once): at
    /// most [`SLOW_FLUSHES_KEPT`], the last ones (one a writer was finishing as this was read
    /// is left out).
    pub slow: Vec<SlowFlush>,
    /// How many calls had begun and not yet returned as this was read: flushes it has no time
    /// and no index of, which may be slow and may have begun at any time before it. 0 means
    /// every call begun by then had returned, each slow one with its index below
    /// [`FlushTimes::slow_count`] (the module docs say in which order these are read).
    pub running: u64,
}

impl FlushTimes {
    /// The total of `kind`.
    #[must_use]
    pub const fn total_ns(&self, kind: FlushKind) -> u64 {
        match kind {
            FlushKind::Full => self.full_ns,
            FlushKind::Barrier => self.barrier_ns,
            FlushKind::Plain => self.plain_ns,
        }
    }

    /// How many of the slow flushes indexed from `from` (an earlier reading's
    /// [`FlushTimes::slow_count`]) up to this reading's count its ring does not hold: 0
    /// exactly when it holds that window whole ([`slow_flushes_missed`]).
    #[must_use]
    pub fn missed(&self, from: u64) -> u64 {
        slow_flushes_missed(self.slow.iter().copied(), self.slow_count, from)
    }
}

/// How many of the slow flushes indexed from `from` up to `slow_count` the flushes `held` (a
/// ring as [`FlushTimes::slow`] holds it, oldest first, or a copy of one) leave out: the
/// window's length less the indices in it that `held` names, each counted once and only in
/// rising order. 0 exactly when every index in the window is held; a window that starts at or
/// past `slow_count` is empty and misses nothing. [`FlushTimes::missed`] reads by it, and so
/// can a reader that keeps its own copy of a reading.
#[must_use]
pub fn slow_flushes_missed(
    held: impl IntoIterator<Item = SlowFlush>,
    slow_count: u64,
    from: u64,
) -> u64 {
    let mut last: Option<u64> = None;
    let mut inside = 0u64;
    for f in held {
        if last.is_some_and(|l| f.index <= l) {
            continue;
        }
        last = Some(f.index);
        if (from..slow_count).contains(&f.index) {
            inside += 1;
        }
    }
    slow_count.saturating_sub(from).saturating_sub(inside)
}

/// One place in the ring: its tag (0 never written; `2i + 1` while index `i` is written;
/// `2i + 2` once it is) and the flush's fields.
struct Slot {
    tag: AtomicU64,
    kind: AtomicU8,
    start: AtomicU64,
    end: AtomicU64,
}

impl Slot {
    const fn new() -> Slot {
        Slot {
            tag: AtomicU64::new(0),
            kind: AtomicU8::new(0),
            start: AtomicU64::new(0),
            end: AtomicU64::new(0),
        }
    }
}

/// A kind as a slot stores it: never 0, so a slot's zero reads as no kind.
const fn kind_code(kind: FlushKind) -> u8 {
    match kind {
        FlushKind::Full => 1,
        FlushKind::Barrier => 2,
        FlushKind::Plain => 3,
    }
}

const fn code_kind(code: u8) -> Option<FlushKind> {
    match code {
        1 => Some(FlushKind::Full),
        2 => Some(FlushKind::Barrier),
        3 => Some(FlushKind::Plain),
        _ => None,
    }
}

/// The counts, the totals and the ring: the process's one is [`LEDGER`]; a test keeps its own.
pub(crate) struct Ledger {
    counts: [AtomicU64; 3],
    totals: [AtomicU64; 3],
    /// The door's calls that have returned, each once its span is noted.
    returned: AtomicU64,
    next: AtomicU64,
    slots: [Slot; SLOW_FLUSHES_KEPT],
}

impl Ledger {
    pub(crate) const fn new() -> Ledger {
        Ledger {
            counts: [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)],
            totals: [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)],
            returned: AtomicU64::new(0),
            next: AtomicU64::new(0),
            slots: [const { Slot::new() }; SLOW_FLUSHES_KEPT],
        }
    }

    /// `kind`'s calls so far, each counted as it began.
    pub(crate) fn count(&self, kind: FlushKind) -> u64 {
        self.counts[kind.index()].load(Ordering::Relaxed)
    }

    /// The door every flush goes through: count it, read the clock, flush, read the clock,
    /// note the span, then count its return. Release: a reading that counts the return (an
    /// acquire load) sees the index the note took.
    fn timed(&self, kind: FlushKind, flush: impl FnOnce() -> io::Result<()>) -> io::Result<()> {
        self.timed_on(&clock_ns, kind, flush)
    }

    /// [`Ledger::timed`] on `clock`, which a test injects so a call's span is what it says,
    /// not however long a loaded machine took to run it.
    fn timed_on(
        &self,
        clock: &impl Fn() -> u64,
        kind: FlushKind,
        flush: impl FnOnce() -> io::Result<()>,
    ) -> io::Result<()> {
        let _ = self.counts[kind.index()].fetch_add(1, Ordering::Relaxed);
        let start = clock();
        let answer = flush();
        let _ = self.note(kind, start, clock());
        let _ = self.returned.fetch_add(1, Ordering::Release);
        answer
    }

    /// A `kind` flush ran from `start` to `end`: its total, and when it was slow its index
    /// (returned) and the ring.
    fn note(&self, kind: FlushKind, start: u64, end: u64) -> Option<u64> {
        let ns = end.saturating_sub(start);
        let _ = self.totals[kind.index()].fetch_add(ns, Ordering::Relaxed);
        (ns > SLOW_FLUSH_NS).then(|| {
            let index = self.take();
            self.put(index, kind, start, end);
            index
        })
    }

    /// The next slow flush's index. Release: a reading whose count is past it (an acquire load)
    /// comes after the end this flush read, which its caller read first.
    fn take(&self) -> u64 {
        self.next.fetch_add(1, Ordering::Release)
    }

    /// Write slow flush `index` into its slot, unless a writer holds the slot or a later
    /// index is already in it.
    fn put(&self, index: u64, kind: FlushKind, start: u64, end: u64) {
        if let Some(slot) = self.claim(index) {
            Self::publish(slot, index, kind, start, end);
        }
    }

    /// Claim the slot `index` falls in: its tag set to `index`'s odd value, unless a writer
    /// holds it (an odd tag) or it already holds `index` or a later one (`None`, keeping
    /// nothing).
    fn claim(&self, index: u64) -> Option<&Slot> {
        let slot = &self.slots[(index % SLOW_FLUSHES_KEPT as u64) as usize];
        let writing = index.saturating_mul(2).saturating_add(1);
        let mut seen = slot.tag.load(Ordering::Relaxed);
        loop {
            if seen & 1 == 1 || seen >= writing {
                return None;
            }
            match slot.tag.compare_exchange_weak(
                seen,
                writing,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Some(slot),
                Err(now) => seen = now,
            }
        }
    }

    /// Write a claimed slot's fields and publish `index`'s even tag.
    fn publish(slot: &Slot, index: u64, kind: FlushKind, start: u64, end: u64) {
        let writing = index.saturating_mul(2).saturating_add(1);
        // The fields' stores may not be seen ahead of the odd tag.
        fence(Ordering::Release);
        slot.kind.store(kind_code(kind), Ordering::Relaxed);
        slot.start.store(start, Ordering::Relaxed);
        slot.end.store(end, Ordering::Relaxed);
        slot.tag.store(writing.saturating_add(1), Ordering::Release);
    }

    /// The returned calls (acquire: each one's index is seen), then the begun ones, the totals,
    /// every slot that reads whole, oldest first by its index, and then the count (acquire:
    /// every flush below it read its end before this reading's next clock read, and every kept
    /// index is below it).
    pub(crate) fn times(&self) -> FlushTimes {
        let returned = self.returned.load(Ordering::Acquire);
        let begun: u64 = FlushKind::ALL.iter().map(|&kind| self.count(kind)).sum();
        let mut kept: Vec<SlowFlush> = Vec::with_capacity(SLOW_FLUSHES_KEPT);
        for slot in &self.slots {
            let before = slot.tag.load(Ordering::Acquire);
            if before == 0 || before & 1 == 1 {
                continue;
            }
            let kind = slot.kind.load(Ordering::Relaxed);
            let start_ns = slot.start.load(Ordering::Relaxed);
            let end_ns = slot.end.load(Ordering::Relaxed);
            // The fields' loads may not be seen after the second read of the tag.
            fence(Ordering::Acquire);
            if slot.tag.load(Ordering::Relaxed) != before {
                continue;
            }
            if let Some(kind) = code_kind(kind) {
                kept.push(SlowFlush {
                    index: before / 2 - 1,
                    kind,
                    start_ns,
                    end_ns,
                });
            }
        }
        kept.sort_unstable_by_key(|f| f.index);
        let total = |kind: FlushKind| self.totals[kind.index()].load(Ordering::Relaxed);
        FlushTimes {
            clock: FLUSH_CLOCK,
            full_ns: total(FlushKind::Full),
            barrier_ns: total(FlushKind::Barrier),
            plain_ns: total(FlushKind::Plain),
            slow_count: self.next.load(Ordering::Acquire),
            slow: kept,
            running: begun.saturating_sub(returned),
        }
    }
}

/// This process's counts, totals and ring.
pub(crate) static LEDGER: Ledger = Ledger::new();

/// `flush` as a `kind` flush of this process: counted as it begins, timed, and kept in the
/// ring when slow ([`LEDGER`]).
pub(crate) fn timed(kind: FlushKind, flush: impl FnOnce() -> io::Result<()>) -> io::Result<()> {
    LEDGER.timed(kind, flush)
}

/// How long the flushes this process has asked this crate for took, by kind, and the last
/// [`SLOW_FLUSHES_KEPT`] of them slower than [`SLOW_FLUSH_NS`], each with its index, kind,
/// start and end on [`clock_ns`]'s clock, so a reader can say which it missed
/// ([`FlushTimes::missed`]). A flush's time joins its total as it returns, while
/// [`flush_tally`](crate::flush_tally) counts it as it begins, so a reading taken while a
/// flush runs counts the call, has none of its time yet and counts it running
/// ([`FlushTimes::running`]). A flush through
/// [`File::sync_data`](std::fs::File::sync_data) or [`File::sync_all`](std::fs::File::sync_all)
/// directly is no call here and has no time here. Process-wide, as the tally is.
#[must_use]
pub fn flush_times() -> FlushTimes {
    LEDGER.times()
}

#[cfg(test)]
mod tests {
    use super::*;

    const MS: u64 = 1_000_000;

    /// A clock each read of which is 100 ns past the last: a call timed on it spans 100 ns per
    /// read between its two, however long the machine took to run it.
    fn stepping() -> impl Fn() -> u64 {
        let now = std::cell::Cell::new(0u64);
        move || now.replace(now.get() + 100)
    }

    /// A FLUSH IS KEPT ONLY WHEN SLOWER THAN 1 MS, and every one joins its kind's total and
    /// count, whatever it answers. Exactly 1 ms is not slow; 1 ms and 1 ns is, and takes the
    /// first index.
    #[test]
    fn a_flush_joins_its_total_and_only_a_slow_one_the_ring() {
        let ledger = Ledger::new();
        let span = |ledger: &Ledger, kind, start, ns| ledger.note(kind, start, start + ns);
        assert_eq!(span(&ledger, FlushKind::Full, 10, MS), None);
        assert_eq!(span(&ledger, FlushKind::Barrier, 20, 300), None);
        assert_eq!(span(&ledger, FlushKind::Plain, 5 * MS, MS + 1), Some(0));
        let failed = ledger.timed_on(&stepping(), FlushKind::Barrier, || {
            Err(io::Error::other("refused"))
        });
        assert!(failed.is_err(), "the flush's own answer comes back");
        let t = ledger.times();
        assert_eq!(t.clock, FLUSH_CLOCK);
        assert_eq!((t.full_ns, t.plain_ns), (MS, MS + 1));
        assert_eq!(
            t.barrier_ns,
            300 + 100,
            "the timed barrier adds its span: {t:?}"
        );
        assert_eq!(
            (
                ledger.count(FlushKind::Full),
                ledger.count(FlushKind::Barrier)
            ),
            (0, 1),
            "only the door counts a call: note is its exit alone"
        );
        assert_eq!(t.slow_count, 1);
        assert_eq!(
            t.slow,
            vec![SlowFlush {
                index: 0,
                kind: FlushKind::Plain,
                start_ns: 5 * MS,
                end_ns: 6 * MS + 1,
            }]
        );
        assert_eq!(t.slow[0].ns(), MS + 1);
        assert_eq!(t.total_ns(FlushKind::Plain), MS + 1);
        assert_eq!(
            (t.missed(0), t.missed(1)),
            (0, 0),
            "its one slow flush, held"
        );
    }

    /// THE RING KEEPS THE LAST 64, OLDEST FIRST, each with its index, and counts every slow
    /// flush: 100 of them leave the 37th to the 100th, indices 36 to 99. A window from index 36
    /// on is whole; one from 35 misses exactly the one flush the ring turned over last, one
    /// from 0 the first 36; a window that starts at the count, or past it, is empty.
    #[test]
    fn the_ring_keeps_the_last_64_oldest_first() {
        let ledger = Ledger::new();
        for i in 0..100u64 {
            let index = ledger.note(
                FlushKind::ALL[(i % 3) as usize],
                i * 10 * MS,
                i * 10 * MS + 2 * MS,
            );
            assert_eq!(index, Some(i), "the next index");
        }
        let t = ledger.times();
        assert_eq!(t.slow_count, 100);
        assert_eq!(t.slow.len(), SLOW_FLUSHES_KEPT);
        for (at, f) in t.slow.iter().enumerate() {
            let i = 36 + at as u64;
            assert_eq!(f.index, i, "slot {at}");
            assert_eq!(f.start_ns, i * 10 * MS, "slot {at}");
            assert_eq!(f.kind, FlushKind::ALL[(i % 3) as usize], "slot {at}");
            assert_eq!(f.ns(), 2 * MS);
        }
        assert_eq!(
            [36, 35, 0, 100, 200].map(|from| t.missed(from)),
            [0, 1, 36, 0, 0]
        );
        assert_eq!(
            slow_flushes_missed(
                t.slow.iter().copied().chain(t.slow.iter().copied()),
                100,
                36
            ),
            0,
            "a held index counts once, however often it is named"
        );
    }

    /// A SLOT IN FLUX IS NEVER READ: one whose tag is odd (a writer between its claim and its
    /// publish) is left out, and so is one whose tag moved while its fields were read. A writer
    /// that finds a later index in its slot keeps nothing there, and one that finds the slot
    /// being written keeps nothing either; the count has both. NEGATIVE CONTROL: the same
    /// slot with its even tag back reads.
    #[test]
    fn a_slot_in_flux_or_overtaken_is_never_read_as_a_flush() {
        let ledger = Ledger::new();
        ledger.put(64, FlushKind::Full, 640, 640 + 2 * MS);
        ledger.put(0, FlushKind::Plain, 0, 2 * MS);
        let t = ledger.times();
        assert_eq!(
            t.slow,
            vec![SlowFlush {
                index: 64,
                kind: FlushKind::Full,
                start_ns: 640,
                end_ns: 640 + 2 * MS,
            }],
            "the later index stays in its slot"
        );
        let slot = &ledger.slots[0];
        slot.tag.store(129, Ordering::Release);
        ledger.put(128, FlushKind::Barrier, 1, 2 * MS);
        assert!(
            ledger.times().slow.is_empty(),
            "an odd tag reads as no flush"
        );
        assert_eq!(
            slot.start.load(Ordering::Relaxed),
            640,
            "a held slot is not written"
        );
        slot.tag.store(130, Ordering::Release);
        assert_eq!(
            ledger.times().slow.len(),
            1,
            "CONTROL: the even tag back, the slot reads"
        );
    }

    /// A deterministic stream of numbers for the interleavings below (splitmix64).
    struct Seeded(u64);

    impl Seeded {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n.max(1)
        }
    }

    /// Where one simulated writer is in a slow flush's write: between flushes, its index taken,
    /// or its slot claimed.
    enum Step<'a> {
        Idle,
        Taken(u64),
        Claimed(u64, &'a Slot),
    }

    /// How many of `[from, to)` `held` (a reading's indices, rising) leaves out.
    fn absent(held: &[u64], from: u64, to: u64) -> u64 {
        (from..to)
            .filter(|i| held.binary_search(i).is_err())
            .count() as u64
    }

    /// A READER NEVER CLAIMS A WINDOW WHOLE THAT IT MISSED, over seeded interleavings of up to
    /// five writers' three steps (take an index, claim its slot, publish it) and readings taken
    /// between any two steps: a writer that lags while the others wrap the ring finds its slot
    /// overtaken or held and keeps nothing, and a reading taken between a writer's index and
    /// its publish finds that flush counted and not yet kept. Every flush a reading holds is
    /// the one its index names, every held index is below its reading's count, and for every
    /// earlier reading, [`FlushTimes::missed`] from its count is exactly the number of indices
    /// in the window the later reading does not hold, so a window it calls whole (0) holds every
    /// slow flush of the window. NEGATIVE CONTROL: the same readings with their indices dropped,
    /// judged as a reader without them must (the window's count of flushes, the newest ones the
    /// ring holds, whole when it holds that many), claim a window whole that is not, here
    /// whenever a raced or overtaken write left a window's flush out while an older one stayed.
    #[test]
    fn a_reader_never_claims_a_window_whole_that_it_missed() {
        let mut wrong_without_indices = 0u64;
        let mut lost_writes = 0u64;
        for seed in 0..300u64 {
            let mut rng = Seeded(seed);
            let ledger = Ledger::new();
            let writers = 1 + rng.below(5) as usize;
            let lag = 1 + rng.below(96);
            let mut left: Vec<u64> = (0..writers).map(|_| 1 + rng.below(60)).collect();
            let mut steps: Vec<Step<'_>> = (0..writers).map(|_| Step::Idle).collect();
            // Each index's flush, as its writer took it: (kind, start, end).
            let mut truth: Vec<Option<(FlushKind, u64, u64)>> = Vec::new();
            let mut readings = vec![ledger.times()];
            let mut clock = 0u64;
            loop {
                let live: Vec<usize> = (0..writers)
                    .filter(|&w| left[w] > 0 || !matches!(steps[w], Step::Idle))
                    .collect();
                if live.is_empty() {
                    break;
                }
                // Writer 0 lags, acting once in `lag` times it is picked, so others wrap past it.
                let w = live[rng.below(live.len() as u64) as usize];
                if w == 0 && live.len() > 1 && rng.below(lag) != 0 {
                    continue;
                }
                clock += 3 * MS;
                steps[w] = match std::mem::replace(&mut steps[w], Step::Idle) {
                    Step::Idle => {
                        left[w] -= 1;
                        let kind = FlushKind::ALL[w % 3];
                        let index = ledger.take();
                        let flush = (kind, clock - 2 * MS - (index % 7), clock);
                        if truth.len() <= index as usize {
                            truth.resize(index as usize + 1, None);
                        }
                        truth[index as usize] = Some(flush);
                        Step::Taken(index)
                    }
                    Step::Taken(index) => match ledger.claim(index) {
                        Some(slot) => Step::Claimed(index, slot),
                        None => {
                            lost_writes += 1;
                            Step::Idle
                        }
                    },
                    Step::Claimed(index, slot) => {
                        let (kind, start, end) = truth[index as usize].expect("taken");
                        Ledger::publish(slot, index, kind, start, end);
                        Step::Idle
                    }
                };
                if rng.below(4) == 0 {
                    readings.push(ledger.times());
                }
            }
            readings.push(ledger.times());
            for (at, later) in readings.iter().enumerate() {
                let held: Vec<u64> = later.slow.iter().map(|f| f.index).collect();
                assert!(
                    held.windows(2).all(|p| p[0] < p[1]),
                    "seed {seed}: rising, each once: {held:?}"
                );
                for f in &later.slow {
                    assert!(
                        f.index < later.slow_count,
                        "seed {seed}: {f:?} past the count"
                    );
                    assert_eq!(
                        truth[f.index as usize],
                        Some((f.kind, f.start_ns, f.end_ns)),
                        "seed {seed}: a held flush is the one its index names"
                    );
                }
                for earlier in &readings[..=at] {
                    let (from, to) = (earlier.slow_count, later.slow_count);
                    let missing = absent(&held, from, to);
                    assert_eq!(
                        later.missed(from),
                        missing,
                        "seed {seed}: the window {from}..{to}, held {held:?}"
                    );
                    // The control: no indices, the window's count of the newest flushes held.
                    let n = (to - from) as usize;
                    let stripped: Vec<(FlushKind, u64, u64)> = later
                        .slow
                        .iter()
                        .map(|f| (f.kind, f.start_ns, f.end_ns))
                        .collect();
                    if n <= stripped.len() {
                        let claimed = &stripped[stripped.len() - n..];
                        let window: Vec<(FlushKind, u64, u64)> =
                            (from..to).filter_map(|i| truth[i as usize]).collect();
                        if claimed != window.as_slice() {
                            wrong_without_indices += 1;
                            assert!(missing > 0, "seed {seed}: wrong only where one is missing");
                        }
                    }
                }
            }
        }
        assert!(
            lost_writes > 0,
            "the interleavings lost no write: they test nothing"
        );
        assert!(
            wrong_without_indices > 0,
            "NEGATIVE CONTROL: a reader without indices never claimed a missed window whole"
        );
    }

    /// NEGATIVE CONTROL, by hand: a full ring of 64 flushes, then a 65th whose index is taken
    /// and whose write a reading races. Without its index, the reading holds 64 flushes for a
    /// window that counted one, and a reader that takes the newest as the window's claims it
    /// whole with the flush from before the window; with indices it misses exactly the one.
    #[test]
    fn a_raced_write_is_named_by_its_index_and_fools_a_reader_without_one() {
        let ledger = Ledger::new();
        for i in 0..64u64 {
            let _ = ledger.note(FlushKind::Full, i * 10 * MS, i * 10 * MS + 2 * MS);
        }
        let before = ledger.times();
        let index = ledger.take();
        let slot = ledger.claim(index).expect("its slot holds an older index");
        let raced = ledger.times();
        assert_eq!((before.slow_count, raced.slow_count), (64, 65));
        assert_eq!(
            raced.missed(before.slow_count),
            1,
            "the raced one, by its index"
        );
        let newest = raced.slow.last().expect("63 held");
        assert!(
            newest.index < before.slow_count,
            "CONTROL: the newest held is from before the window, which a reader without \
             indices would take as the window's one: {newest:?}"
        );
        Ledger::publish(slot, index, FlushKind::Barrier, 640 * MS, 643 * MS);
        let after = ledger.times();
        assert_eq!(
            after.missed(before.slow_count),
            0,
            "published, the window is whole"
        );
        assert_eq!(after.slow.last().map(|f| f.index), Some(64));
    }

    /// MANY WRITERS AT ONCE: every slow flush is counted, the ring holds 64 whole ones, and
    /// no read is a mix of two (each flush's end is its start plus a span its start encodes);
    /// each held flush is the one its index names, below its reading's count, and a window
    /// between two readings that misses none holds every index in it.
    #[test]
    fn many_writers_leave_a_ring_of_whole_flushes() {
        let ledger = Ledger::new();
        let (readings, taken) = std::thread::scope(|s| {
            let writers: Vec<_> = (0..8u64)
                .map(|thread| {
                    let ledger = &ledger;
                    s.spawn(move || {
                        let mut taken = Vec::with_capacity(500);
                        for i in 0..500u64 {
                            let start = (thread << 32) | i;
                            let ns = 2 * MS + (start % 997);
                            let kind = FlushKind::ALL[(thread % 3) as usize];
                            let index = ledger.note(kind, start, start + ns).expect("slow");
                            taken.push((index, start));
                        }
                        taken
                    })
                })
                .collect();
            let mut readings = Vec::with_capacity(200);
            for _ in 0..200 {
                let t = ledger.times();
                for f in &t.slow {
                    assert_eq!(f.ns(), 2 * MS + (f.start_ns % 997), "a torn read: {f:?}");
                    assert_eq!(f.kind, FlushKind::ALL[((f.start_ns >> 32) % 3) as usize]);
                }
                readings.push(t);
            }
            let taken: Vec<(u64, u64)> = writers
                .into_iter()
                .flat_map(|w| w.join().expect("a writer"))
                .collect();
            (readings, taken)
        });
        let t = ledger.times();
        assert_eq!(t.slow_count, 8 * 500);
        assert!(t.slow.len() <= SLOW_FLUSHES_KEPT);
        let mut start_of = vec![None; 8 * 500];
        for (index, start) in taken {
            assert!(
                start_of[index as usize].replace(start).is_none(),
                "index {index} twice"
            );
        }
        for (at, later) in readings.iter().chain([&t]).enumerate() {
            for f in &later.slow {
                assert!(f.index < later.slow_count, "{f:?} past its reading's count");
                assert_eq!(start_of[f.index as usize], Some(f.start_ns), "{f:?}");
            }
            let held: Vec<u64> = later.slow.iter().map(|f| f.index).collect();
            if let Some(earlier) = at.checked_sub(1).map(|e| &readings[e]) {
                let (from, to) = (earlier.slow_count, later.slow_count);
                assert_eq!(later.missed(from), absent(&held, from, to), "{from}..{to}");
            }
        }
    }

    /// NO HELD FLUSH ENDS AFTER THE CLOCK READ THAT FOLLOWS ITS READING: writers that read
    /// their end from the clock and a reader that reads the clock after each reading. It sees
    /// only the flushes a ring holds, which the slot's sequence lock orders whatever orders the
    /// count is taken and loaded with: that every flush below a count, held or not, ended
    /// before the next clock read is argued in the module docs and tested by nothing.
    #[test]
    fn no_held_flush_ends_after_the_clock_read_that_follows_its_reading() {
        let ledger = Ledger::new();
        std::thread::scope(|s| {
            for _ in 0..4 {
                let ledger = &ledger;
                s.spawn(move || {
                    for _ in 0..500 {
                        let end = clock_ns();
                        let _ = ledger.note(FlushKind::Full, end.saturating_sub(2 * MS), end);
                    }
                });
            }
            for _ in 0..500 {
                let t = ledger.times();
                let after = clock_ns();
                for f in &t.slow {
                    assert!(
                        f.end_ns <= after,
                        "{f:?}, below the count {}, ends after {after}",
                        t.slow_count
                    );
                }
            }
        });
    }

    /// A CALL INSIDE THE DOOR IS RUNNING until it returns: a reading taken inside a flush
    /// counts it (and one inside a flush inside it, two), with none of its time and no index;
    /// once it returns, failed or not, it runs no more, its time joins its total and its index
    /// is below the count. A note alone, no call through the door, never runs.
    #[test]
    fn a_reading_counts_each_call_inside_the_door_running() {
        let ledger = Ledger::new();
        let _ = ledger.note(FlushKind::Full, 0, 2 * MS);
        assert_eq!(ledger.times().running, 0, "a note alone is no call");
        let mut inside = Vec::new();
        let clock = stepping();
        let answer = ledger.timed_on(&clock, FlushKind::Barrier, || {
            inside.push(ledger.times());
            ledger.timed_on(&clock, FlushKind::Plain, || {
                inside.push(ledger.times());
                Err(io::Error::other("refused"))
            })
        });
        assert!(answer.is_err(), "the inner flush's answer comes back");
        let after = ledger.times();
        assert_eq!(
            inside.iter().map(|t| t.running).collect::<Vec<_>>(),
            [1, 2],
            "one call, then a call inside it"
        );
        assert!(
            inside.iter().all(|t| t.barrier_ns == 0 && t.plain_ns == 0),
            "a running call has no time yet: {inside:?}"
        );
        assert_eq!(after.running, 0, "both returned, the failed one too");
        assert_eq!(
            after.slow_count, 1,
            "the note's index, and none for fast calls"
        );
        assert_eq!(
            (after.barrier_ns, after.plain_ns),
            (300, 100),
            "its time, once it returned: {after:?}"
        );
    }

    /// MANY CALLS RUNNING AT ONCE are each counted, and none once they have returned: four
    /// threads each hold their flush open at a barrier while the reader reads, then let it
    /// return. NEGATIVE CONTROL: the reading before any call began counts none.
    #[test]
    fn calls_running_on_many_threads_are_each_counted_until_they_return() {
        let ledger = Ledger::new();
        let before = ledger.times();
        let gate = std::sync::Barrier::new(5);
        let during = std::thread::scope(|s| {
            let calls: Vec<_> = (0..4usize)
                .map(|thread| {
                    let (ledger, gate) = (&ledger, &gate);
                    s.spawn(move || {
                        ledger.timed(FlushKind::ALL[thread % 3], || {
                            let _ = gate.wait();
                            let _ = gate.wait();
                            Ok(())
                        })
                    })
                })
                .collect();
            let _ = gate.wait();
            let during = ledger.times();
            let _ = gate.wait();
            for call in calls {
                assert!(call.join().expect("a call").is_ok());
            }
            during
        });
        let after = ledger.times();
        assert_eq!(
            (before.running, during.running, after.running),
            (0, 4, 0),
            "none, all four inside the door, none once they returned"
        );
    }

    /// The clock never goes back within a process, and its words read back.
    #[test]
    fn the_clock_is_monotonic_and_its_words_read_back() {
        let a = clock_ns();
        let b = clock_ns();
        assert!(b >= a, "{a} then {b}");
        for c in [FlushClock::Machine, FlushClock::Process] {
            assert_eq!(FlushClock::from_word(c.word()), Some(c));
            assert_eq!(c.word().len(), 7, "one length either way");
        }
        for k in FlushKind::ALL {
            assert_eq!(FlushKind::from_word(k.word()), Some(k));
        }
        assert_eq!(FlushKind::from_word("fsync"), None);
    }
}
