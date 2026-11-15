// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! WHAT A TIER'S READERS AND WRITERS DID, counted: the pushes, the one-record reads by index,
//! the walks and the rows they read, the pages a filtered read passed whole and the times it
//! asked its filter of a subject, and the values read from the wide maps. A measurement says by it how much of the pages' code a piece of
//! work ran (aterm's attach bench reads it around each restart, its item D10f), so a cost is
//! put down to the tier, or not, by a count rather than a guess. Only a test or debug build
//! counts (`Counters` and the broker's readers of them): a shipped broker keeps no counters.
//! `TierTally` is compiled in every build, so a reader such as aterm's bench names astream's
//! counts rather than keeping a copy of them.

#[cfg(any(test, debug_assertions))]
use std::sync::atomic::{AtomicU64, Ordering};

/// A tier's counts since its log was opened ([`BrokerLog::tier_tally`](crate::BrokerLog),
/// [`Broker::tier_tally`](crate::Broker)). A replica's rebuild of the tier carries them on.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TierTally {
    /// Records pushed: each promoted record (a publish's, a batch's, a replica's) once. An
    /// open's build of the tier from the records it recovered is not counted.
    pub pushes: u64,
    /// One-record reads by index (`summary`, `at`, `bt`), each finding its record's page: a
    /// cold read is two (its frame's start and the next one's).
    pub lookups: u64,
    /// The values read from the wide maps (a frame start or broker time no column holds), by a
    /// lookup or a walk's row; 0 in a log whose frames are contiguous and whose broker times
    /// rise within a page.
    pub wide: u64,
    /// The walks begun over a range of summaries: a `Stats` reading, a filtered read's pass
    /// (`Tier::passing`, whose records are rows here, not lookups) or a wake plan's,
    /// compaction's, the retention planning's (each of its passes one).
    pub walks: u64,
    /// The rows those walks read.
    pub rows: u64,
    /// The pages a filtered read's pass (`Tier::passing`, a walk counted in `walks`) passed
    /// whole, none of their ids a subject the read wants: their records are not in `rows`.
    pub passed_pages: u64,
    /// The times a filtered read's pass asked its filter of a subject: at most once a page a
    /// subject, and not again in a later page while the pass's 256 verdict slots (slot
    /// `id % 256`) keep its verdict. So this is not a count of distinct subjects: a pass whose
    /// pages name more than 256 asks again of one whose slot another took, and a page the pass
    /// reads fewer records of than it names subjects asks only of those its unhidden records
    /// name.
    pub verdicts: u64,
}

impl TierTally {
    /// What `self` counted since `before` (each count less `before`'s, saturating at 0).
    #[must_use]
    pub fn since(self, before: TierTally) -> TierTally {
        TierTally {
            pushes: self.pushes.saturating_sub(before.pushes),
            lookups: self.lookups.saturating_sub(before.lookups),
            wide: self.wide.saturating_sub(before.wide),
            walks: self.walks.saturating_sub(before.walks),
            rows: self.rows.saturating_sub(before.rows),
            passed_pages: self.passed_pages.saturating_sub(before.passed_pages),
            verdicts: self.verdicts.saturating_sub(before.verdicts),
        }
    }
}

/// The counts a tier keeps, as atomics because its readers hold it shared (under the log's
/// lock, so they never contend).
#[cfg(any(test, debug_assertions))]
#[derive(Debug, Default)]
pub(crate) struct Counters {
    pushes: AtomicU64,
    lookups: AtomicU64,
    wide: AtomicU64,
    walks: AtomicU64,
    rows: AtomicU64,
    passed_pages: AtomicU64,
    verdicts: AtomicU64,
}

/// One kind of count.
#[cfg(any(test, debug_assertions))]
#[derive(Clone, Copy, Debug)]
pub(crate) enum Count {
    Push,
    Lookup,
    Wide,
    Walk,
    Rows,
    PassedPage,
    Verdict,
}

#[cfg(any(test, debug_assertions))]
impl Counters {
    fn cell(&self, c: Count) -> &AtomicU64 {
        match c {
            Count::Push => &self.pushes,
            Count::Lookup => &self.lookups,
            Count::Wide => &self.wide,
            Count::Walk => &self.walks,
            Count::Rows => &self.rows,
            Count::PassedPage => &self.passed_pages,
            Count::Verdict => &self.verdicts,
        }
    }

    /// Count `n` more of `c`.
    pub(crate) fn add(&self, c: Count, n: u64) {
        self.cell(c).fetch_add(n, Ordering::Relaxed);
    }

    /// The counts now.
    pub(crate) fn read(&self) -> TierTally {
        let r = |c| self.cell(c).load(Ordering::Relaxed);
        TierTally {
            pushes: r(Count::Push),
            lookups: r(Count::Lookup),
            wide: r(Count::Wide),
            walks: r(Count::Walk),
            rows: r(Count::Rows),
            passed_pages: r(Count::PassedPage),
            verdicts: r(Count::Verdict),
        }
    }

    /// Fresh counters holding `self`'s counts (a rebuilt tier's).
    pub(crate) fn carried(&self) -> Counters {
        let t = self.read();
        Counters {
            pushes: AtomicU64::new(t.pushes),
            lookups: AtomicU64::new(t.lookups),
            wide: AtomicU64::new(t.wide),
            walks: AtomicU64::new(t.walks),
            rows: AtomicU64::new(t.rows),
            passed_pages: AtomicU64::new(t.passed_pages),
            verdicts: AtomicU64::new(t.verdicts),
        }
    }
}
