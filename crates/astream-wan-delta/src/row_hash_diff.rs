// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-row FNV-1a (`astream_wire::fnv1a_64`) dirty-row differ skipping unchanged terminal rows
//! over high-RTT WAN links (`Astream.WanDelta.TlaRowHashDiff`).

use astream_wire::fnv1a_64;

#[cfg(clean_islands)]
#[path = "row_hash_diff_island.rs"]
mod row_hash_diff_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn row_diff_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn row_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use row_hash_diff_island::{row_diff_clamp, row_gen_advance};

/// Maximum terminal rows tracked in the FNV-1a row-digest cache.
pub const MAX_TRACKED_ROWS: u64 = 256;

contract_fn! {
    /// Verified match check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `row_clean_match_isl`.
    #[must_use]
    pub const fn row_clean_match(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes changed row indices between consecutive frames.
#[derive(Debug, Clone)]
pub struct RowHashDiffer {
    frame_gen: u64,
    prev_hashes: Vec<u64>,
}

impl Default for RowHashDiffer {
    fn default() -> Self {
        Self::new()
    }
}

impl RowHashDiffer {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            frame_gen: 0,
            prev_hashes: Vec::new(),
        }
    }

    pub fn diff_rows(&mut self, rows: &[&[u8]]) -> Vec<usize> {
        let count = row_diff_clamp(rows.len() as u64, MAX_TRACKED_ROWS) as usize;
        let resized = !row_clean_match(self.prev_hashes.len() as u64, count as u64)
            || self.prev_hashes.len() != count;
        if resized {
            self.prev_hashes.clear();
            let mut i = 0usize;
            while i < count {
                self.prev_hashes.push(0);
                i = i.saturating_add(1);
            }
        }
        let mut dirty = Vec::new();
        let mut idx = 0usize;
        while idx < count {
            let Some(&r) = rows.get(idx) else {
                break;
            };
            let h = fnv1a_64(r);
            let same = match self.prev_hashes.get(idx) {
                Some(&prev) => !resized && prev == h,
                None => false,
            };
            if !same {
                if let Some(slot) = self.prev_hashes.get_mut(idx) {
                    *slot = h;
                }
                dirty.push(idx);
            }
            idx = idx.saturating_add(1);
        }
        self.frame_gen = row_gen_advance(self.frame_gen, self.frame_gen.saturating_add(1));
        dirty
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn row_differ_emits_only_mutated_row_indices_after_initial_frame() {
        let mut d = RowHashDiffer::new();
        assert_eq!(d.diff_rows(&[b"line0", b"line1", b"line2"]), vec![0, 1, 2]);
        assert_eq!(d.diff_rows(&[b"line0", b"EDIT!", b"line2"]), vec![1]);
        assert!(d.diff_rows(&[b"line0", b"EDIT!", b"line2"]).is_empty());
    }
}
