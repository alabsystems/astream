// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE SLOT VECTOR the paged tier replaced (aterm D10c's `tier::Slot`, kept for tests): one
//! packed 24-byte slot for every retained record, its frame start, broker time, interned
//! subject id and plaintext-frame bytes with the has-time and hidden flags, record `i` at
//! offset `base + i`, and the hot window as each resident record's offset and charge.
//!
//! In a test build every [`Tier`](super::Tier) keeps one beside its pages, fed the same
//! pushes, cuts, truncations and budgets, and [`Tier::check_shadow`](super::Tier) holds every
//! answer the pages give to this one's: the differential half of `broker.paged-tier`.

use std::collections::VecDeque;

use super::{Subjects, Summary, BYTES_MASK, HAS_BT, HIDDEN};

/// One retained record, packed: 24 bytes.
#[derive(Clone, Copy, Debug)]
struct Slot {
    /// Byte at which the record's frame starts in the log file.
    at: u64,
    /// Its broker time (`bt=`), when `meta` says it has one; `0` otherwise.
    bt: u64,
    /// Its subject's id in [`Subjects`].
    subject: u32,
    /// Its plaintext-frame bytes ([`BYTES_MASK`]), [`HAS_BT`] and [`HIDDEN`].
    meta: u32,
}

const _: () = assert!(std::mem::size_of::<Slot>() == 24);

/// Today's slot vector, its hot window as offsets and charges.
#[derive(Default)]
pub(super) struct Slots {
    slots: Vec<Slot>,
    base: u64,
    /// The resident records' offsets and charges, oldest first.
    hot: VecDeque<(u64, usize)>,
    hot_bytes: usize,
    budget: usize,
    subjects: Subjects,
}

impl Slots {
    pub(super) fn with_budget(budget: usize) -> Slots {
        Slots {
            budget,
            ..Slots::default()
        }
    }

    /// Append record `off` (subject, `meta`, broker time, frame start), charged `cost`.
    pub(super) fn push(
        &mut self,
        off: u64,
        subject: &str,
        meta: u32,
        bt: Option<u64>,
        at: u64,
        cost: usize,
    ) {
        self.push_warm(off, subject, meta, bt, at, cost);
        self.evict();
    }

    /// Append record `off` as a cold one (an open's prefix outside the window).
    pub(super) fn push_cold(
        &mut self,
        off: u64,
        subject: &str,
        meta: u32,
        bt: Option<u64>,
        at: u64,
    ) {
        if self.slots.is_empty() {
            self.base = off;
        }
        let s = Slot {
            at,
            bt: bt.unwrap_or(0),
            subject: self.subjects.take(subject),
            meta,
        };
        self.slots.push(s);
    }

    /// Append record `off` to the hot window without evicting (an open's resident suffix).
    pub(super) fn push_warm(
        &mut self,
        off: u64,
        subject: &str,
        meta: u32,
        bt: Option<u64>,
        at: u64,
        cost: usize,
    ) {
        self.push_cold(off, subject, meta, bt, at);
        self.hot_bytes = self.hot_bytes.saturating_add(cost);
        self.hot.push_back((off, cost));
    }

    fn evict(&mut self) {
        while self.hot_bytes > self.budget && self.hot.len() > 1 {
            let Some((_, cost)) = self.hot.pop_front() else {
                break;
            };
            self.hot_bytes = self.hot_bytes.saturating_sub(cost);
        }
    }

    pub(super) fn set_budget(&mut self, budget: usize) {
        self.budget = budget;
        self.evict();
    }

    fn first_hot(&self) -> usize {
        self.slots.len().saturating_sub(self.hot.len())
    }

    pub(super) fn len(&self) -> usize {
        self.slots.len()
    }

    pub(super) fn resident(&self) -> usize {
        self.hot.len()
    }

    pub(super) fn resident_bytes(&self) -> usize {
        self.hot_bytes
    }

    pub(super) fn live_subjects(&self) -> usize {
        self.subjects.live()
    }

    /// The offset of the resident record at index `i`, if it is resident.
    pub(super) fn hot(&self, i: usize) -> Option<u64> {
        let j = i.checked_sub(self.first_hot())?;
        self.hot.get(j).map(|&(off, _)| off)
    }

    pub(super) fn summary(&self, i: usize) -> Option<Summary<'_>> {
        let s = self.slots.get(i)?;
        Some(Summary {
            off: self.base.checked_add(i as u64)?,
            subject: self.subjects.name(s.subject),
            bytes: u64::from(s.meta & BYTES_MASK),
            hidden: s.meta & HIDDEN != 0,
        })
    }

    pub(super) fn at(&self, i: usize) -> Option<u64> {
        self.slots.get(i).map(|s| s.at)
    }

    pub(super) fn bt(&self, i: usize) -> Option<u64> {
        let s = self.slots.get(i)?;
        if s.meta & HAS_BT != 0 {
            Some(s.bt)
        } else {
            None
        }
    }

    pub(super) fn truncate(&mut self, keep: usize) {
        if keep >= self.slots.len() {
            return;
        }
        let first = self.first_hot();
        if keep <= first {
            self.hot.clear();
            self.hot_bytes = 0;
        } else {
            let keep_hot = keep - first;
            while self.hot.len() > keep_hot {
                if let Some((_, cost)) = self.hot.pop_back() {
                    self.hot_bytes = self.hot_bytes.saturating_sub(cost);
                }
            }
        }
        for i in keep..self.slots.len() {
            if let Some(id) = self.slots.get(i).map(|s| s.subject) {
                self.subjects.give(id);
            }
        }
        self.slots.truncate(keep);
    }

    pub(super) fn drain_front(&mut self, n: usize, shift: u64) {
        let n = n.min(self.slots.len());
        let first = self.first_hot();
        for _ in 0..n.saturating_sub(first) {
            if let Some((_, cost)) = self.hot.pop_front() {
                self.hot_bytes = self.hot_bytes.saturating_sub(cost);
            }
        }
        for i in 0..n {
            if let Some(id) = self.slots.get(i).map(|s| s.subject) {
                self.subjects.give(id);
            }
        }
        self.slots.drain(..n);
        for s in &mut self.slots {
            s.at = s.at.saturating_sub(shift);
        }
        self.base = self.base.saturating_add(n as u64);
    }

    /// Move record `i`'s frame start to `at` (a test's mutation, mirrored).
    pub(super) fn set_at(&mut self, i: usize, at: u64) {
        if let Some(s) = self.slots.get_mut(i) {
            s.at = at;
        }
    }
}

/// The retention planning over the slot vector, as over the tier's pages.
#[cfg(feature = "retention")]
impl crate::retention::Records for Slots {
    type Entries<'a> = crate::retention::ByIndex<'a, Slots>;

    fn entries(&self, from: usize, to: usize) -> crate::retention::ByIndex<'_, Slots> {
        crate::retention::ByIndex::new(self, from, to.min(self.len()))
    }

    fn entry(&self, i: usize) -> Option<crate::retention::Entry<'_>> {
        let s = self.summary(i)?;
        Some(crate::retention::Entry {
            offset: s.offset(),
            subject: s.subject(),
            bytes: s.bytes(),
            bt: self.bt(i),
        })
    }

    fn whole(&self, _i: usize) -> Option<std::sync::Arc<crate::brecord::BrokerRecord>> {
        None
    }
}
