// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `PendingRetire` `visible_head` visibility gate: `PendingRetire` overlays `last_matching` and
//! moot retries so retirement takes effect only once the visible head passes the retire offset
//! (`Astream.SubjRet.TlaPendingRetireOverlay`).

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
#[path = "pending_retire_overlay_island.rs"]
mod pending_retire_overlay_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_pend_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_head_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pending_retire_overlay_island::{srb_head_advance, srb_pend_clamp};

/// Maximum concurrent in-flight `PendingRetire` entries (`1024`).
pub const MAX_PENDING_RETIRES: u64 = 1024;

contract_fn! {
    /// Verified `visible_head > retire_offset` commit visibility (`threshold <= observed`), linked
    /// via `clean-kernel-defeq` to `srb_head_past_retire_isl`.
    #[must_use]
    pub const fn srb_head_past_retire(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct PendingRetireOverlay {
    pending: Vec<(String, u64)>,
    visible_head: u64,
}

impl PendingRetireOverlay {
    #[must_use]
    pub const fn new(visible_head: u64) -> Self {
        Self {
            pending: Vec::new(),
            visible_head,
        }
    }

    pub fn stage_retire(&mut self, subject: &str, retire_offset: u64) -> bool {
        if subject.is_empty() {
            return false;
        }
        let mut idx = 0usize;
        while idx < self.pending.len() {
            if let Some(entry) = self.pending.get_mut(idx) {
                if entry.0 == subject {
                    entry.1 = srb_head_advance(entry.1, retire_offset);
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        let next = srb_pend_clamp(
            (self.pending.len() as u64).saturating_add(1),
            MAX_PENDING_RETIRES,
        );
        if next as usize <= self.pending.len() {
            return false;
        }
        let mut owned = String::new();
        owned.push_str(subject);
        self.pending.push((owned, retire_offset));
        true
    }

    pub fn advance_visible_head(&mut self, head: u64) {
        self.visible_head = srb_head_advance(self.visible_head, head);
    }

    #[must_use]
    pub fn is_retired_in_last(&self, subject: &str) -> bool {
        let vh = self.visible_head;
        let mut idx = 0usize;
        while idx < self.pending.len() {
            if let Some((s, off)) = self.pending.get(idx) {
                if s == subject {
                    if let Some(min_vh) = off.checked_add(1) {
                        if srb_head_past_retire(vh, min_vh) {
                            return true;
                        }
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hides_last_entry_only_after_visible_head_passes_retire_offset() {
        let mut o = PendingRetireOverlay::new(50);
        assert!(o.stage_retire("/f/a/s", 55));
        assert!(!o.is_retired_in_last("/f/a/s"));
        o.advance_visible_head(55);
        assert!(!o.is_retired_in_last("/f/a/s"));
        o.advance_visible_head(56);
        assert!(o.is_retired_in_last("/f/a/s"));
    }
}
