// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Live & durable will target retirement blocker (`is_retire_will()`): a retire is refused while
//! a live or durable will that can still append targets the subject
//! (`Astream.SubjRet.TlaActiveWillRetireGuard`).

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
#[path = "active_will_retire_guard_island.rs"]
mod active_will_retire_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_wills_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_chk_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use active_will_retire_guard_island::{srb_chk_advance, srb_wills_clamp};

/// Maximum active wills scanned (`4096`).
pub const MAX_PENDING_WILLS: u64 = 4096;

contract_fn! {
    /// Verified zero targeting wills (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `srb_no_live_will_isl`.
    #[must_use]
    pub const fn srb_no_live_will(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct WillRetireBlocker {
    will_targets: Vec<(u64, String)>,
    checks: u64,
}

impl WillRetireBlocker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            will_targets: Vec::new(),
            checks: 0,
        }
    }

    pub fn register_will(&mut self, conn_id: u64, subject: &str) -> bool {
        if subject.is_empty() {
            return false;
        }
        let mut idx = 0usize;
        while idx < self.will_targets.len() {
            if let Some(entry) = self.will_targets.get_mut(idx) {
                if entry.0 == conn_id {
                    entry.1.clear();
                    entry.1.push_str(subject);
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        let next = srb_wills_clamp(
            (self.will_targets.len() as u64).saturating_add(1),
            MAX_PENDING_WILLS,
        );
        if next as usize <= self.will_targets.len() {
            return false;
        }
        let mut owned = String::new();
        owned.push_str(subject);
        self.will_targets.push((conn_id, owned));
        true
    }

    pub fn clear_will(&mut self, conn_id: u64) {
        let mut kept = Vec::new();
        for entry in core::mem::take(&mut self.will_targets) {
            if entry.0 != conn_id {
                kept.push(entry);
            }
        }
        self.will_targets = kept;
    }

    pub fn can_retire(&mut self, subject: &str) -> bool {
        self.checks = srb_chk_advance(self.checks, self.checks.saturating_add(1));
        if subject.is_empty() {
            return false;
        }
        let mut blocking = 0u64;
        let mut idx = 0usize;
        while idx < self.will_targets.len() {
            if let Some((_, s)) = self.will_targets.get(idx) {
                if s == subject {
                    blocking = blocking.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        srb_no_live_will(0, blocking)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_subject_retire_until_pending_will_clears() {
        let mut b = WillRetireBlocker::new();
        assert!(b.register_will(9, "/f/a/pub/n1/s1/presence"));
        assert!(!b.can_retire("/f/a/pub/n1/s1/presence"));
        b.clear_will(9);
        assert!(b.can_retire("/f/a/pub/n1/s1/presence"));
    }
}
