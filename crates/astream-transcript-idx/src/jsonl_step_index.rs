// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sparse monotone `(step_index -> byte_offset)` index over `transcript.jsonl` &
//! `transcript_full.jsonl` (`Astream.Transcript.TlaJsonlStepIndex`).
#![allow(clippy::question_mark, clippy::manual_map)]

#[cfg(clean_islands)]
#[path = "jsonl_step_index_island.rs"]
mod jsonl_step_index_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_sparse_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_step_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use jsonl_step_index_island::{tr_sparse_clamp, tr_step_advance};

/// Maximum sparse landmark entries retained in RAM.
pub const MAX_SPARSE_LANDMARKS: u64 = 8_192;

contract_fn! {
    /// Verified monotone byte-offset check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tr_offset_monotone_isl`.
    #[must_use]
    pub const fn tr_offset_monotone(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StepLandmark {
    pub step_index: u64,
    pub byte_offset: u64,
}

/// Maintains monotone sparse byte-offset landmarks for O(log N) seek into `.jsonl` transcripts.
#[derive(Debug, Clone, Default)]
pub struct SparseJsonlIndex {
    landmarks: Vec<StepLandmark>,
    last_step: u64,
    last_offset: u64,
}

impl SparseJsonlIndex {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            landmarks: Vec::new(),
            last_step: 0,
            last_offset: 0,
        }
    }

    pub fn record_line(&mut self, step_index: u64, byte_offset: u64) -> Result<(), &'static str> {
        if !self.landmarks.is_empty()
            && (!tr_offset_monotone(byte_offset, self.last_offset.saturating_add(1))
                || step_index <= self.last_step)
        {
            return Err("non-monotone step_index or byte_offset in transcript.jsonl");
        }
        let cap = tr_sparse_clamp(MAX_SPARSE_LANDMARKS, MAX_SPARSE_LANDMARKS) as usize;
        self.last_step = tr_step_advance(self.last_step, step_index);
        self.last_offset = byte_offset;
        if self.landmarks.len() < cap {
            self.landmarks.push(StepLandmark {
                step_index,
                byte_offset,
            });
        }
        Ok(())
    }

    /// Returns the nearest landmark `<= target_step` via binary search.
    #[must_use]
    pub fn seek_floor(&self, target_step: u64) -> Option<StepLandmark> {
        let mut lo = 0usize;
        let mut hi = self.landmarks.len();
        while lo < hi {
            let mid = lo.saturating_add(hi.saturating_sub(lo) >> 1);
            let Some(lm) = self.landmarks.get(mid) else {
                break;
            };
            if lm.step_index <= target_step {
                lo = mid.saturating_add(1);
            } else {
                hi = mid;
            }
        }
        let Some(idx) = lo.checked_sub(1) else {
            return None;
        };
        match self.landmarks.get(idx) {
            Some(&lm) => Some(lm),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_jsonl_index_finds_floor_landmark_and_rejects_backwards_offsets() {
        let mut idx = SparseJsonlIndex::new();
        idx.record_line(0, 0).unwrap();
        idx.record_line(10, 4096).unwrap();
        idx.record_line(20, 9200).unwrap();
        assert_eq!(
            idx.seek_floor(15),
            Some(StepLandmark {
                step_index: 10,
                byte_offset: 4096
            })
        );
        assert!(idx.record_line(25, 4000).is_err());
    }
}
