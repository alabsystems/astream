// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Prefix-narrowed `BTreeMap` `Last`-value index (`Astream.Broker.TlaLastPrefixScan`).
//!
//! Accelerates `Last` queries (`DESIGN-aterm-fabric.md` §13 Pareto axis) by extracting the
//! literal leading subject prefix before the first `*` or `>` wildcard in an
//! [`astream_wire::Filter`] and jumping directly to the `[lower..upper)` `BTreeMap` range
//! in `O(log S + K)` instead of scanning unrelated subject subtrees up to `LAST_SCAN_MAX`.

use std::collections::BTreeMap;
use std::ops::Bound;

use astream_wire::{Filter, Offset};

#[cfg(clean_islands)]
#[path = "last_index_island.rs"]
mod last_index_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn last_offset_advance(cur_off: u64, next_off: u64) -> u64 {
    if cur_off < next_off {
        next_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn last_scan_clamp(scanned: u64, scan_max: u64) -> u64 {
    if scanned < scan_max {
        scanned
    } else {
        scan_max
    }
}
#[cfg(clean_islands)]
pub use last_index_island::{last_offset_advance, last_scan_clamp};

/// Default maximum candidate entries inspected in a single bounded `Last` range query.
pub const DEFAULT_LAST_SCAN_MAX: usize = 65_536;

contract_fn! {
    /// Kernel-certified `Last` scan-budget check (`scanned <= scan_max`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `last_scan_within_cap_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn last_scan_within_cap(scanned: usize, scan_max: usize) -> bool
    clauses [ensures result == (scanned <= scan_max)]
    {
        scanned <= scan_max
    }
}

fn str_to_owned_string(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Extract the longest literal prefix of `filter_str` preceding any `*` or `>` wildcard
/// segment, together with its exclusive lexicographic upper bound (`next_lex_prefix`), so
/// `BTreeMap::range` skips all non-matching subtrees in `O(log S)`.
#[must_use]
pub fn filter_literal_bounds(filter_str: &str) -> (String, Option<String>) {
    let bytes = filter_str.as_bytes();
    let mut cut = bytes.len();
    let mut i = 0usize;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b == b'*' || b == b'>' {
            cut = i;
            break;
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    let prefix = match filter_str.get(..cut) {
        Some(p) => str_to_owned_string(p),
        None => String::new(),
    };
    let upper = next_lex_string(&prefix);
    (prefix, upper)
}

fn next_lex_string(prefix: &str) -> Option<String> {
    if prefix.is_empty() {
        return None;
    }
    let mut bytes = Vec::new();
    bytes.extend_from_slice(prefix.as_bytes());
    while let Some(last) = bytes.pop() {
        // Stay within valid single-byte ASCII (`<= 0x7F`) so `core::str::from_utf8` is guaranteed.
        if last < 0x7f {
            bytes.push(last.saturating_add(1));
            let Ok(s) = core::str::from_utf8(&bytes) else {
                return None;
            };
            return Some(str_to_owned_string(s));
        }
    }
    None
}

/// Outcome of a prefix-narrowed [`LastPrefixIndex::query_matching`] scan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LastPrefixScanResult {
    /// Matching `(subject, latest_offset)` rows sorted by subject.
    pub matches: Vec<(String, Offset)>,
    /// Clamped number of `BTreeMap` entries examined (`<= scan_max`).
    pub scanned_entries: usize,
    /// True if `scan_max` truncated the range scan before exhausting `[lower..upper)`.
    pub truncated: bool,
}

/// Prefix-range-accelerated `Last` table mapping `subject -> latest_offset`.
#[derive(Debug, Clone, Default)]
pub struct LastPrefixIndex {
    entries: BTreeMap<String, Offset>,
}

impl LastPrefixIndex {
    /// Construct an empty `LastPrefixIndex`.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    /// Number of live subjects currently indexed.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// True if no subjects are indexed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Record `offset` for `subject`, advancing monotonically via [`last_offset_advance`].
    pub fn upsert(&mut self, subject: &str, offset: Offset) -> Offset {
        if let Some(cur) = self.entries.get_mut(subject) {
            let next = Offset(last_offset_advance(cur.0, offset.0));
            *cur = next;
            return next;
        }
        self.entries.insert(str_to_owned_string(subject), offset);
        offset
    }

    /// Retire `subject` from the `Last` index (when `retire_subject` takes effect),
    /// returning its previous offset if present.
    pub fn remove(&mut self, subject: &str) -> Option<Offset> {
        self.entries.remove(subject)
    }

    /// Exact-subject `O(log S)` lookup.
    #[must_use]
    pub fn get(&self, subject: &str) -> Option<Offset> {
        self.entries.get(subject).copied()
    }

    /// Query all entries matching `filter` (`filter_str`) using `O(log S + K)` prefix-bounded
    /// `BTreeMap::range` iteration, examining at most `scan_max` entries.
    #[must_use]
    #[allow(clippy::vec_init_then_push)]
    pub fn query_matching(
        &self,
        filter_str: &str,
        filter: &Filter,
        scan_max: usize,
    ) -> LastPrefixScanResult {
        // Fast path: if `filter_str` has no wildcards at all, perform a single `O(log S)` lookup!
        if !filter_str.contains('*') && !filter_str.contains('>') {
            if !filter.matches_str(filter_str) {
                return LastPrefixScanResult {
                    matches: Vec::new(),
                    scanned_entries: 0,
                    truncated: false,
                };
            }
            return match self.entries.get(filter_str) {
                Some(&off) if scan_max >= 1 => {
                    let mut matches = Vec::new();
                    matches.push((str_to_owned_string(filter_str), off));
                    LastPrefixScanResult {
                        matches,
                        scanned_entries: 1,
                        truncated: false,
                    }
                }
                Some(_) => LastPrefixScanResult {
                    matches: Vec::new(),
                    scanned_entries: 0,
                    truncated: true,
                },
                None => LastPrefixScanResult {
                    matches: Vec::new(),
                    scanned_entries: 0,
                    truncated: false,
                },
            };
        }

        let (lo, hi_opt) = filter_literal_bounds(filter_str);
        let range = match hi_opt {
            Some(ref hi) => self
                .entries
                .range::<String, _>((Bound::Included(&lo), Bound::Excluded(hi))),
            None => self
                .entries
                .range::<String, _>((Bound::Included(&lo), Bound::Unbounded)),
        };

        let mut matches = Vec::new();
        let mut raw_scanned = 0usize;
        let mut truncated = false;

        for (subj, &off) in range {
            if !last_scan_within_cap(raw_scanned.saturating_add(1), scan_max) {
                truncated = true;
                break;
            }
            raw_scanned = raw_scanned.saturating_add(1);
            if filter.matches_str(subj) {
                matches.push((subj.clone(), off));
            }
        }

        let clamped = last_scan_clamp(raw_scanned as u64, scan_max as u64) as usize;
        LastPrefixScanResult {
            matches,
            scanned_entries: clamped,
            truncated,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_and_literal_bounds_hold() {
        assert_eq!(last_offset_advance(10, 42), 42);
        assert_eq!(last_offset_advance(42, 10), 42);
        assert_eq!(last_scan_clamp(50, 100), 50);
        assert_eq!(last_scan_clamp(500, 100), 100);
        assert!(last_scan_within_cap(10, 10));
        assert!(!last_scan_within_cap(11, 10));

        let (lo, hi) = filter_literal_bounds("/f/lab/presence/>");
        assert_eq!(lo, "/f/lab/presence/");
        assert_eq!(hi.as_deref(), Some("/f/lab/presence0"));

        let (tilde_lo, tilde_hi) = filter_literal_bounds("/f/~*");
        assert_eq!(tilde_lo, "/f/~");
        assert_eq!(tilde_hi.as_deref(), Some("/f/\x7f"));
    }

    #[test]
    fn prefix_range_skips_unrelated_subtrees_in_logarithmic_time() {
        let mut idx = LastPrefixIndex::new();
        // Populate 5,000 unrelated `/a/ev/...` subjects and `/z/metrics/...` subjects
        // flanking 3 target `/f/lab/presence/...` subjects!
        for i in 0..2500u64 {
            idx.upsert(&format!("/a/ev/s-{i}"), Offset(i));
            idx.upsert(&format!("/z/metrics/m-{i}"), Offset(5000 + i));
        }
        idx.upsert("/f/lab/presence/n-1/s-a", Offset(9001));
        idx.upsert("/f/lab/presence/n-1/s-b", Offset(9002));
        idx.upsert("/f/lab/presence/n-2/s-c", Offset(9003));
        // Out-of-order lower upsert stays monotone at 9003.
        assert_eq!(
            idx.upsert("/f/lab/presence/n-2/s-c", Offset(100)),
            Offset(9003)
        );

        let f_str = "/f/lab/presence/>";
        let f = Filter::new(f_str).unwrap();
        let res = idx.query_matching(f_str, &f, 16);
        assert!(!res.truncated);
        // Scanned ONLY the 3 `/f/lab/presence/...` entries instead of 2,500 `/a/ev/...` entries!
        assert_eq!(res.scanned_entries, 3);
        assert_eq!(res.matches.len(), 3);
        assert_eq!(
            res.matches[2],
            ("/f/lab/presence/n-2/s-c".to_string(), Offset(9003))
        );

        // Exact subject query touches at most 1 entry.
        let exact_str = "/f/lab/presence/n-1/s-b";
        let exact_f = Filter::new(exact_str).unwrap();
        let exact_res = idx.query_matching(exact_str, &exact_f, 1);
        assert_eq!(exact_res.scanned_entries, 1);
        assert_eq!(
            exact_res.matches,
            vec![(exact_str.to_string(), Offset(9002))]
        );
    }
}
