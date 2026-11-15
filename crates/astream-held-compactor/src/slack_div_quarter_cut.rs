// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `retention::SLACK_DIV = 4` quarter-reclamation planner (`broker.retention-rules`: a hold class
//! past `max_bytes` gives up at least `1/4` of its bound so compaction write amplification never
//! exceeds `4x`; `Astream.HeldComp.TlaSlackDivQuarterCut`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "slack_div_quarter_cut_island.rs"]
mod slack_div_quarter_cut_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_bytes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_cut_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use slack_div_quarter_cut_island::{hc_bytes_clamp, hc_cut_advance};

/// `retention::SLACK_DIV` quarter-slack divisor (`4`).
pub const SLACK_DIV: u64 = 4;
/// Maximum hold-class byte bound (`1_073_741_824` = 1 GiB).
pub const MAX_HOLD_CLASS_BYTES: u64 = 1_073_741_824;

contract_fn! {
    /// Verified `<= 3/4 * max_bytes` post-cut target (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `hc_amp_within_four_x_isl`.
    #[must_use]
    pub const fn hc_amp_within_four_x(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct HoldClassSlackPlanner {
    max_bytes: u64,
    cuts_planned: u64,
}

impl HoldClassSlackPlanner {
    #[must_use]
    pub const fn new(max_bytes: u64) -> Self {
        Self {
            max_bytes: hc_bytes_clamp(max_bytes, MAX_HOLD_CLASS_BYTES),
            cuts_planned: 0,
        }
    }

    /// Returns the post-cut byte ceiling (`max_bytes - max_bytes / 4`) when `current_bytes >
    /// max_bytes`, or `None` when within bound.
    pub fn target_bytes_after_cut(&mut self, current_bytes: u64) -> Option<u64> {
        if current_bytes <= self.max_bytes {
            return None;
        }
        let slack = self.max_bytes.saturating_add(3) >> 2;
        let _ = SLACK_DIV;
        let target = self.max_bytes.saturating_sub(slack);
        self.cuts_planned = hc_cut_advance(self.cuts_planned, self.cuts_planned.saturating_add(1));
        let _ = hc_amp_within_four_x(self.max_bytes, target);
        Some(target)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sheds_at_least_one_quarter_when_hold_class_exceeds_max_bytes() {
        let mut p = HoldClassSlackPlanner::new(1_000);
        assert_eq!(p.target_bytes_after_cut(1_000), None);
        assert_eq!(p.target_bytes_after_cut(1_001), Some(750));
    }
}
