// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pinned-head paginated `Last` snapshot cursor & prefix-range bound planner.
//!
//! Ensures multi-round `Last` queries over large subject maps (`BTreeMap<String, Offset>`)
//! hold `shared.log` for bounded `scan_budget` steps per round (`last_scan_entries_clamp`),
//! restrict BTree iteration to the filter's literal prefix `[lo, hi_exclusive)` when one
//! exists, and emit ONLY rows strictly visible at the first round's `pinned_head`
//! (`last_row_visible_at_pin`) so an early round's row is never paired with a later
//! round's resume head. Backed by Clean TLA+ island `Astream.Broker.TlaLastSnapshotCursor`.

#![allow(
    clippy::manual_unwrap_or_default,
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use astream_wire::Filter;
use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "last_radix_cursor_island.rs"]
mod last_radix_cursor_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn last_scan_entries_clamp(scanned: u64, scan_budget: u64) -> u64 {
    if scanned < scan_budget {
        scanned
    } else {
        scan_budget
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn last_emitted_offset_clamp(candidate_off: u64, pinned_head: u64) -> u64 {
    if candidate_off < pinned_head {
        candidate_off
    } else {
        pinned_head
    }
}
#[cfg(clean_islands)]
pub use last_radix_cursor_island::{last_emitted_offset_clamp, last_scan_entries_clamp};

contract_fn! {
    /// Kernel-certified visibility check that `row_offset` was already committed at
    /// `pinned_head` (`row_offset < pinned_head`), linked via `clean-kernel-defeq`
    /// to `last_row_visible_at_pin_isl`.
    #[must_use]
    pub const fn last_row_visible_at_pin(row_offset: u64, pinned_head: u64) -> bool
    clauses [ensures result == (row_offset < pinned_head)]
    {
        row_offset < pinned_head
    }
}

/// Default maximum `BTreeMap` entries visited under a single lock acquisition (`4096`).
pub const DEFAULT_LAST_SCAN_BUDGET: u64 = 4_096;

/// Compute the literal non-wildcard prefix of a subject filter pattern (e.g. `"/a/s1/>"`
/// -> `"/a/s1/"`, `"/a/foo"` -> `"/a/foo"`, `">"` -> `""`) for narrowing `BTreeMap::range`.
#[must_use]
pub fn literal_subject_prefix(pattern: &str) -> &str {
    let mut cur = pattern.as_bytes();
    let mut i = 0usize;
    while let &[b, ref rest @ ..] = cur {
        if b == b'*' || b == b'>' {
            return match pattern.get(..i) {
                Some(s) => s,
                None => "",
            };
        }
        i = i.saturating_add(1);
        cur = rest;
    }
    pattern
}

/// Compute the smallest lexicographic string strictly greater than every string starting
/// with `prefix`, or `None` if `prefix` is empty or all `0xFF`.
#[must_use]
pub fn exclusive_prefix_upper_bound(prefix: &str) -> Option<String> {
    if prefix.is_empty() {
        return None;
    }
    let mut bytes = copy_bytes(prefix.as_bytes());
    while let Some(last) = bytes.pop() {
        if last < 0x7F {
            bytes.push(last.saturating_add(1));
            return match core::str::from_utf8(&bytes) {
                Ok(s) => Some(copy_str(s)),
                Err(_) => None,
            };
        }
    }
    None
}

fn copy_bytes(src: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(src);
    out
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

/// Result of one bounded `Last` scan round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LastScanPage {
    /// Matching `(subject, latest_offset)` rows visible at `pinned_head`.
    pub rows: Vec<(String, u64)>,
    /// Number of BTree entries inspected in this round (`<= scan_budget`).
    pub scanned_entries: u64,
    /// Clamped highest offset among emitted rows (`<= pinned_head`).
    pub emitted_max_offset: u64,
    /// Continuation key (`Some(last_visited_subject)`) if more entries remain, or `None` when complete.
    pub resume_after_subject: Option<String>,
    /// Pinned resume offset (`pinned_head`) for gapless tail handoff after the final page.
    pub tail_resume_offset: u64,
}

/// Stateful pinned-head `Last` snapshot cursor across bounded lock-release rounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LastSnapshotCursor {
    pattern: String,
    filter: Filter,
    prefix_lo: String,
    prefix_hi: Option<String>,
    after_subject: Option<String>,
    pinned_head: u64,
    scan_budget: u64,
    finished: bool,
}

impl LastSnapshotCursor {
    /// Create a pinned-head cursor over `pattern` anchored at `pinned_head`.
    pub fn new(pattern: &str, pinned_head: u64, scan_budget: u64) -> Result<Self, String> {
        let filter = match Filter::new(copy_str(pattern)) {
            Ok(f) => f,
            Err(e) => return Err(copy_str(e.as_str())),
        };
        let lit = literal_subject_prefix(pattern);
        let prefix_lo = copy_str(lit);
        let prefix_hi = exclusive_prefix_upper_bound(lit);
        let budget = if scan_budget == 0 { 1 } else { scan_budget };
        Ok(Self {
            pattern: copy_str(pattern),
            filter,
            prefix_lo,
            prefix_hi,
            after_subject: None,
            pinned_head,
            scan_budget: budget,
            finished: false,
        })
    }

    /// Original subject filter pattern string.
    #[must_use]
    pub fn pattern(&self) -> &str {
        &self.pattern
    }

    /// Pinned log head for this snapshot; callers attach their follow-up `Tail` at this offset.
    #[must_use]
    pub const fn pinned_head(&self) -> u64 {
        self.pinned_head
    }

    /// True once every matching subject in `[prefix_lo, prefix_hi)` has been visited.
    #[must_use]
    pub const fn is_finished(&self) -> bool {
        self.finished
    }

    /// Execute one bounded scan round against `last_map` (`subject -> latest_offset`).
    /// Subjects whose `latest_offset >= pinned_head` were superseded after the pin and are
    /// omitted here because the caller's `Tail` starting at `pinned_head` will deliver them!
    pub fn next_page(&mut self, last_map: &BTreeMap<String, u64>) -> LastScanPage {
        if self.finished {
            return LastScanPage {
                rows: Vec::new(),
                scanned_entries: 0,
                emitted_max_offset: 0,
                resume_after_subject: None,
                tail_resume_offset: self.pinned_head,
            };
        }

        let mut rows = Vec::new();
        let mut raw_scanned = 0u64;
        let mut raw_max_off = 0u64;
        let mut last_key: Option<String> = None;
        let mut hit_budget = false;

        let iter = match &self.after_subject {
            Some(prev) => {
                use std::ops::Bound::{Excluded, Unbounded};
                last_map.range::<String, _>((Excluded(prev.clone()), Unbounded))
            }
            None => {
                use std::ops::Bound::{Included, Unbounded};
                last_map.range::<String, _>((Included(self.prefix_lo.clone()), Unbounded))
            }
        };

        for (subj, &off) in iter {
            if let Some(ref hi) = self.prefix_hi {
                if subj.as_str() >= hi.as_str() {
                    break;
                }
            }
            if raw_scanned >= self.scan_budget {
                hit_budget = true;
                break;
            }
            raw_scanned = raw_scanned.saturating_add(1);
            last_key = Some(subj.clone());

            if self.filter.matches_str(subj) && last_row_visible_at_pin(off, self.pinned_head) {
                let clamped_off = last_emitted_offset_clamp(off, self.pinned_head);
                if clamped_off > raw_max_off {
                    raw_max_off = clamped_off;
                }
                rows.push((subj.clone(), clamped_off));
            }
        }

        let scanned_entries = last_scan_entries_clamp(raw_scanned, self.scan_budget);
        let emitted_max_offset = last_emitted_offset_clamp(raw_max_off, self.pinned_head);

        if hit_budget {
            self.after_subject = last_key.clone();
        } else {
            self.after_subject = None;
            self.finished = true;
        }

        LastScanPage {
            rows,
            scanned_entries,
            emitted_max_offset,
            resume_after_subject: self.after_subject.clone(),
            tail_resume_offset: self.pinned_head,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paginated_last_cursor_narrows_prefix_and_omits_post_pin_supersedes() {
        let mut map = BTreeMap::new();
        map.insert("/a/other/1".to_string(), 5);
        map.insert("/a/s1/a".to_string(), 10);
        map.insert("/a/s1/b".to_string(), 14);
        map.insert("/a/s1/c".to_string(), 25); // superseded at/after pinned_head=20!
        map.insert("/a/s1/d".to_string(), 19);
        map.insert("/a/s2/z".to_string(), 11);

        let mut cur = LastSnapshotCursor::new("/a/s1/*", 20, 2).unwrap();
        let p1 = cur.next_page(&map);
        assert_eq!(
            p1.rows,
            vec![("/a/s1/a".to_string(), 10), ("/a/s1/b".to_string(), 14)]
        );
        assert_eq!(p1.scanned_entries, 2);
        assert!(!cur.is_finished());

        let p2 = cur.next_page(&map);
        assert_eq!(p2.rows, vec![("/a/s1/d".to_string(), 19)]);
        assert!(cur.is_finished());
        assert_eq!(p2.tail_resume_offset, 20);
    }
}
