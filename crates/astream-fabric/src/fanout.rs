// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared lock-amortizing fan-out read-page cache (`docs/DESIGN-aterm-fabric.md` §13).
//!
//! When dozens of concurrent `tail_loop` subscribers wake on `Condvar::notify_all()`,
//! having every subscriber lock `Mutex<BrokerLog>` and re-scan `read_from` individually
//! serializes fan-out under producer contention. [`FanoutPageCache`] amortizes hot-tail
//! fan-out: the first reader (or publisher flush) populates an immutable `Arc<FanoutPage>`
//! covering `[base_offset, end_offset)`, and every subsequent subscriber at `cursor`
//! satisfying `fanout_hit_in_window(cursor, base_offset, end_offset)` slices its page out
//! of that shared `Arc` in O(page) without touching `BrokerLog`!

#![allow(clippy::question_mark)]

use astream_broker::BrokerRecord;
use astream_wire::{Filter, Offset};
use std::sync::{Arc, RwLock};

#[cfg(clean_islands)]
#[path = "fanout_island.rs"]
mod fanout_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn fanout_cursor_advance(cur_off: u64, next_off: u64) -> u64 {
    if cur_off < next_off {
        next_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fanout_page_clamp(requested: u64, max_page: u64) -> u64 {
    if requested < max_page {
        requested
    } else {
        max_page
    }
}
#[cfg(clean_islands)]
pub use fanout_island::{fanout_cursor_advance, fanout_page_clamp};

contract_fn! {
    /// Contracted check that `cursor < end_off` inside a cached hot-tail page.
    #[must_use]
    pub const fn fanout_cursor_below_end(cursor: u64, end_off: u64) -> bool
    clauses [ensures result == (cursor < end_off)]
    {
        cursor < end_off
    }
}

/// Check that `cursor` lies inside a cached `[base, end_off)` hot-tail page.
#[inline]
#[must_use]
pub const fn fanout_hit_in_window(cursor: u64, base: u64, end_off: u64) -> bool {
    base <= cursor && fanout_cursor_below_end(cursor, end_off)
}

/// Maximum number of records held in a single hot-tail [`FanoutPage`].
pub const MAX_FANOUT_PAGE_RECORDS: usize = 512;

/// Immutable contiguous slice of committed records `[base_offset, end_offset)`.
#[derive(Debug, Clone)]
pub struct FanoutPage {
    pub base_offset: u64,
    pub end_offset: u64,
    pub records: Arc<[Arc<BrokerRecord>]>,
}

impl FanoutPage {
    /// Construct a bounded hot-tail page starting at `base_offset`.
    pub fn from_records(base_offset: u64, src: &[Arc<BrokerRecord>]) -> Self {
        let take = fanout_page_clamp(src.len() as u64, MAX_FANOUT_PAGE_RECORDS as u64) as usize;
        let cap = if take < MAX_FANOUT_PAGE_RECORDS {
            take
        } else {
            MAX_FANOUT_PAGE_RECORDS
        };
        let mut v = {
            let _ = cap;
            Vec::new()
        };
        let mut i = 0usize;
        while i < take {
            let Some(rec) = src.get(i) else {
                break;
            };
            v.push(Arc::clone(rec));
            i = i.saturating_add(1);
        }
        let end_offset = base_offset.saturating_add(v.len() as u64);
        Self {
            base_offset,
            end_offset,
            records: Arc::from(v),
        }
    }

    /// Drain up to `max_items` matching `filter` starting at `cursor`, returning
    /// `(matching_records, next_cursor)` when `cursor` hits this cached window.
    pub fn read_matching(
        &self,
        cursor: Offset,
        filter: &Filter,
        max_items: usize,
    ) -> Option<(Vec<Arc<BrokerRecord>>, Offset)> {
        if !fanout_hit_in_window(cursor.0, self.base_offset, self.end_offset) {
            return None;
        }
        let limit = fanout_page_clamp(max_items as u64, MAX_FANOUT_PAGE_RECORDS as u64) as usize;
        let start_idx = (cursor.0.saturating_sub(self.base_offset)) as usize;
        let out_cap = if limit < 64 { limit } else { 64 };
        let mut out = {
            let _ = out_cap;
            Vec::new()
        };
        let mut idx = start_idx;
        let mut next_cur = cursor.0;
        while out.len() < limit {
            let Some(rec) = self.records.get(idx) else {
                break;
            };
            let rec_end = self
                .base_offset
                .saturating_add(idx as u64)
                .saturating_add(1);
            next_cur = fanout_cursor_advance(next_cur, rec_end);
            if !astream_broker::is_hidden_record(rec) && filter.matches_str(&rec.subject) {
                out.push(Arc::clone(rec));
            }
            idx = idx.saturating_add(1);
        }
        Some((out, Offset(next_cur)))
    }
}

/// Concurrent reader-shared hot-tail page cache for high-fanout subscriptions.
#[derive(Debug, Default)]
pub struct FanoutPageCache {
    latest: RwLock<Option<Arc<FanoutPage>>>,
}

impl FanoutPageCache {
    pub fn new() -> Self {
        Self {
            latest: RwLock::new(None),
        }
    }

    /// Publish a freshly committed tail page if its `end_offset` advances the cache.
    pub fn publish_tail(&self, base_offset: u64, records: &[Arc<BrokerRecord>]) {
        if records.is_empty() {
            return;
        }
        let page = Arc::new(FanoutPage::from_records(base_offset, records));
        if let Ok(mut guard) = self.latest.write() {
            let replace = match &*guard {
                None => true,
                Some(prev) => page.end_offset >= prev.end_offset,
            };
            if replace {
                *guard = Some(page);
            }
        }
    }

    /// Invalidate cached records if a replica truncation or retention cut rewrites offsets.
    pub fn invalidate(&self) {
        if let Ok(mut guard) = self.latest.write() {
            *guard = None;
        }
    }

    /// Attempt to serve `(matching_records, next_cursor)` from the shared `RwLock` read path
    /// without acquiring `Mutex<BrokerLog>`.
    pub fn try_read(
        &self,
        cursor: Offset,
        filter: &Filter,
        max_items: usize,
    ) -> Option<(Vec<Arc<BrokerRecord>>, Offset)> {
        let page = match self.latest.read() {
            Ok(guard) => match &*guard {
                Some(p) => Arc::clone(p),
                None => return None,
            },
            Err(_) => return None,
        };
        page.read_matching(cursor, filter, max_items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_rec(seq: u64, subj: &str, body: &[u8]) -> Arc<BrokerRecord> {
        Arc::new(BrokerRecord {
            seq: Offset(seq),
            producer_id: 1,
            producer_seq: seq + 1,
            subject: subj.to_string(),
            body: body.to_vec(),
            commit: None,
        })
    }

    #[test]
    fn shared_fanout_cache_serves_filtered_pages_and_advances_cursor_monotonically() {
        let cache = FanoutPageCache::new();
        let batch = vec![
            sample_rec(10, "/fleet/a/out", b"1"),
            sample_rec(11, "/fleet/b/out", b"2"),
            sample_rec(12, "/fleet/a/out", b"3"),
            sample_rec(13, "/fleet/a/out", b"4"),
        ];
        cache.publish_tail(10, &batch);

        let filter = Filter::new("/fleet/a/*").unwrap();
        assert!(
            cache.try_read(Offset(9), &filter, 16).is_none(),
            "below base misses"
        );
        assert!(
            cache.try_read(Offset(14), &filter, 16).is_none(),
            "at end misses"
        );

        let (hit1, next1) = cache.try_read(Offset(10), &filter, 2).expect("cache hit");
        assert_eq!(hit1.len(), 2);
        assert_eq!(hit1[0].seq, Offset(10));
        assert_eq!(hit1[1].seq, Offset(12));
        assert_eq!(next1, Offset(13));

        let (hit2, next2) = cache.try_read(next1, &filter, 16).expect("second hit");
        assert_eq!(hit2.len(), 1);
        assert_eq!(hit2[0].seq, Offset(13));
        assert_eq!(next2, Offset(14));
    }

    #[test]
    fn shared_fanout_cache_skips_broker_internal_hidden_records() {
        let cache = FanoutPageCache::new();
        let hidden_commit = sample_rec(20, "/a/commit", b"c");
        let hidden_retire = Arc::new(BrokerRecord {
            seq: Offset(21),
            producer_id: 0,
            producer_seq: 0,
            subject: "/a/retire".to_string(),
            body: b"/fleet/a/out".to_vec(),
            commit: None,
        });
        let visible = sample_rec(22, "/fleet/a/out", b"ok");
        cache.publish_tail(20, &[hidden_commit, hidden_retire, visible]);

        let all_filter = Filter::new("/>").unwrap();
        let (rows, next) = cache.try_read(Offset(20), &all_filter, 16).expect("hit");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].seq, Offset(22));
        assert_eq!(next, Offset(23));
    }
}
