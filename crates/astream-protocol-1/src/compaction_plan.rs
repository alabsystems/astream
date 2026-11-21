// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `/a/bind` & `/a/will` Control-Record Compaction Planner (`Astream.Broker.TlaBindWillCompaction`).
//!
//! Resolves the long-running `aterm` fleet log-compaction blocker:
//! - In `BrokerLog`, `/a/bind/<sid>` and `/a/will/<sid>` records tie session ownership and
//!   disconnect last-wills to log offsets.
//! - Once a session disconnects cleanly (releasing its `/a/bind` and either clearing or firing
//!   its `/a/will`), its historical control records no longer need to block `retain_before`
//!   compaction!
//! - Meanwhile, **live** session bindings and **unfired** pending wills below `requested_before`
//!   can either:
//!   1. Pin `effective_cut = min(requested_before, min_live_pinned_offset)` in conservative mode, or
//!   2. Be re-anchored into a bounded checkpoint snapshot (`Vec<PinnedControlRecord>`, capped at
//!      [`MAX_CHECKPOINT_CONTROLS`]) written at the head of the compacted segment so `retain_before`
//!      advances all the way to `min(requested_before, log_hw)` with **zero** loss of live bindings
//!      or unfired wills!

#[cfg(clean_islands)]
#[path = "compaction_plan_island.rs"]
mod compaction_plan_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn compact_base_advance(prev_base: u64, cand_base: u64) -> u64 {
    if prev_base < cand_base {
        cand_base
    } else {
        prev_base
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn compact_floor_clamp(requested_before: u64, safe_ceiling: u64) -> u64 {
    if requested_before < safe_ceiling {
        requested_before
    } else {
        safe_ceiling
    }
}
#[cfg(clean_islands)]
pub use compaction_plan_island::{compact_base_advance, compact_floor_clamp};

/// Maximum live `/a/bind` + `/a/will` entries re-anchored in one compaction checkpoint (`16_384`).
pub const MAX_CHECKPOINT_CONTROLS: usize = 16_384;

contract_fn! {
    /// Verified check whether a control entry is still active and lies strictly below `cut`
    /// (`active && offset < cut`), linked via `clean-kernel-defeq` to `compact_entry_is_pinned_isl`.
    #[must_use]
    pub const fn compact_entry_is_pinned(active: bool, offset: u64, cut: u64) -> bool
    clauses [ensures result == (active && (offset < cut))]
    {
        active && (offset < cut)
    }
}

/// Kind of broker control record tracked across compaction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlKind {
    /// `/a/bind` exclusive session/name lease.
    Bind,
    /// `/a/will` disconnect testament record.
    Will,
}

/// Lifecycle state of one `/a/bind` or `/a/will` control record in the broker log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrackedControlEntry {
    pub kind: ControlKind,
    pub key: String,
    pub offset: u64,
    /// `true` if the binding is still held or the pending will has not yet fired/cleared.
    pub active: bool,
}

/// Computed compaction plan for `retain_before(requested_before)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactionPlan {
    /// Previous `base` offset before compaction.
    pub prev_base: u64,
    /// Monotone next `base` offset (`prev_base <= next_base <= safe_ceiling`).
    pub next_base: u64,
    /// Active `/a/bind` and `/a/will` entries below `next_base` that must be re-anchored into
    /// the compacted checkpoint prefix (empty in conservative pin-floor mode).
    pub reanchored_controls: Vec<TrackedControlEntry>,
    /// Retired control entries below `next_base` safely dropped by this compaction pass.
    pub reclaimed_dead_controls: usize,
}

/// Plan a conservative compaction cut that never rewrites active `/a/bind` or `/a/will` offsets,
/// advancing `base` past all dead/released bindings and fired/cleared wills up to the earliest
/// still-active control offset (`<= log_hw`).
#[must_use]
pub fn plan_conservative_compaction(
    current_base: u64,
    log_hw: u64,
    requested_before: u64,
    entries: &[TrackedControlEntry],
) -> CompactionPlan {
    let mut safe_ceiling = log_hw;
    let mut idx = 0usize;
    while idx < entries.len() {
        if let Some(entry) = entries.get(idx) {
            if entry.active && entry.offset < safe_ceiling {
                safe_ceiling = entry.offset;
            }
        }
        idx = idx.saturating_add(1);
    }
    let clamped_cut = compact_floor_clamp(requested_before, safe_ceiling);
    let next_base = compact_base_advance(current_base, clamped_cut);

    let mut reclaimed = 0usize;
    let mut scan = 0usize;
    while scan < entries.len() {
        if let Some(entry) = entries.get(scan) {
            if !entry.active && entry.offset >= current_base && entry.offset < next_base {
                reclaimed = reclaimed.saturating_add(1);
            }
        }
        scan = scan.saturating_add(1);
    }

    CompactionPlan {
        prev_base: current_base,
        next_base,
        reanchored_controls: Vec::new(),
        reclaimed_dead_controls: reclaimed,
    }
}

/// Plan a checkpointing compaction cut that advances `base` to `min(requested_before, log_hw)`
/// while collecting every active `/a/bind` and `/a/will` record in `current_base..next_base`
/// into `reanchored_controls` (falling back to conservative pinning if active controls exceed
/// [`MAX_CHECKPOINT_CONTROLS`]).
#[must_use]
pub fn plan_checkpoint_compaction(
    current_base: u64,
    log_hw: u64,
    requested_before: u64,
    entries: &[TrackedControlEntry],
) -> CompactionPlan {
    let clamped_cut = compact_floor_clamp(requested_before, log_hw);
    let target_base = compact_base_advance(current_base, clamped_cut);

    let cap = if entries.len() < 64 {
        entries.len()
    } else {
        64
    };
    let mut reanchored = {
        let _ = cap;
        Vec::new()
    };
    let mut reclaimed = 0usize;
    let mut idx = 0usize;
    while idx < entries.len() {
        if let Some(entry) = entries.get(idx) {
            if compact_entry_is_pinned(entry.active, entry.offset, target_base) {
                if reanchored.len() >= MAX_CHECKPOINT_CONTROLS {
                    return plan_conservative_compaction(
                        current_base,
                        log_hw,
                        requested_before,
                        entries,
                    );
                }
                reanchored.push(entry.clone());
            } else if !entry.active && entry.offset >= current_base && entry.offset < target_base {
                reclaimed = reclaimed.saturating_add(1);
            }
        }
        idx = idx.saturating_add(1);
    }

    CompactionPlan {
        prev_base: current_base,
        next_base: target_base,
        reanchored_controls: reanchored,
        reclaimed_dead_controls: reclaimed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(compact_base_advance(10, 25), 25);
        assert_eq!(compact_base_advance(25, 10), 25);
        assert_eq!(compact_floor_clamp(80, 100), 80);
        assert_eq!(compact_floor_clamp(120, 100), 100);
        assert!(compact_entry_is_pinned(true, 5, 10));
        assert!(!compact_entry_is_pinned(false, 5, 10));
        assert!(!compact_entry_is_pinned(true, 10, 10));
    }

    #[test]
    fn conservative_reclaims_retired_controls_and_pins_at_earliest_live_control() {
        let entries = vec![
            TrackedControlEntry {
                kind: ControlKind::Bind,
                key: "s-dead1".to_string(),
                offset: 5,
                active: false,
            },
            TrackedControlEntry {
                kind: ControlKind::Will,
                key: "s-dead1".to_string(),
                offset: 8,
                active: false,
            },
            TrackedControlEntry {
                kind: ControlKind::Bind,
                key: "s-live2".to_string(),
                offset: 42,
                active: true,
            },
        ];

        let plan = plan_conservative_compaction(0, 100, 80, &entries);
        assert_eq!(plan.next_base, 42);
        assert_eq!(plan.reclaimed_dead_controls, 2);
        assert!(plan.reanchored_controls.is_empty());
    }

    #[test]
    fn checkpoint_compaction_advances_past_live_controls_by_reanchoring_them() {
        let entries = vec![
            TrackedControlEntry {
                kind: ControlKind::Bind,
                key: "s-dead1".to_string(),
                offset: 5,
                active: false,
            },
            TrackedControlEntry {
                kind: ControlKind::Bind,
                key: "s-live2".to_string(),
                offset: 42,
                active: true,
            },
            TrackedControlEntry {
                kind: ControlKind::Will,
                key: "s-live2".to_string(),
                offset: 43,
                active: true,
            },
        ];

        let plan = plan_checkpoint_compaction(0, 100, 80, &entries);
        assert_eq!(plan.next_base, 80);
        assert_eq!(plan.reclaimed_dead_controls, 1);
        assert_eq!(plan.reanchored_controls.len(), 2);
        assert_eq!(plan.reanchored_controls[0].key, "s-live2");
    }
}
