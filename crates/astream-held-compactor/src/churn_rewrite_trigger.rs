// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `<log>.held` append-vs-rewrite churn controller (`broker.retention-rules`: appended between
//! compactions and rewritten once file bytes churn past `2x` live carried bytes;
//! `Astream.HeldComp.TlaChurnRewriteTrigger`).

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
#[path = "churn_rewrite_trigger_island.rs"]
mod churn_rewrite_trigger_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_churn_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_rw_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use churn_rewrite_trigger_island::{hc_churn_clamp, hc_rw_advance};

/// Maximum tracked `<log>.held` file size (`4_294_967_296` = 4 GiB).
pub const MAX_HELD_FILE_BYTES: u64 = 4_294_967_296;

contract_fn! {
    /// Verified `> 2x` churn rewrite trigger (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `hc_rewrite_needed_isl`.
    #[must_use]
    pub const fn hc_rewrite_needed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct HeldChurnTracker {
    rewrites: u64,
}

impl HeldChurnTracker {
    #[must_use]
    pub const fn new() -> Self {
        Self { rewrites: 0 }
    }

    pub fn should_rewrite_held(&mut self, file_bytes: u64, live_carried_bytes: u64) -> bool {
        let _ = hc_churn_clamp(file_bytes, MAX_HELD_FILE_BYTES);
        if file_bytes <= 4_096 || file_bytes <= live_carried_bytes {
            return false;
        }
        let Some(two_x) = live_carried_bytes.checked_mul(2) else {
            return false;
        };
        let Some(two_x_plus_one) = two_x.checked_add(1) else {
            return false;
        };
        if hc_rewrite_needed(file_bytes, two_x_plus_one) {
            self.rewrites = hc_rw_advance(self.rewrites, self.rewrites.saturating_add(1));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn appends_below_two_x_churn_and_rewrites_once_file_exceeds_twice_live_bytes() {
        let mut t = HeldChurnTracker::new();
        assert!(!t.should_rewrite_held(16_000, 10_000));
        assert!(t.should_rewrite_held(25_000, 10_000));
    }
}
