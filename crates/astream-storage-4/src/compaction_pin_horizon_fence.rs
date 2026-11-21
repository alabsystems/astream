// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Incremental `/a/bind` & `/a/will` live-pin horizon tracker for `BrokerLog::retain_before`
//! (`Astream.Broker.TlaCompactionPinHorizonFence`).
//!
//! Resolves the compaction pin bottleneck: tracks live connection/name
//! pins on the stack (`MAX_COMPACTION_PINS = 16`) and computes the exact safe prefix-truncation
//! ceiling `min(requested_retain_before, oldest_live_pin_offset)` without scanning the full log.

#[cfg(clean_islands)]
#[path = "compaction_pin_horizon_fence_island.rs"]
mod compaction_pin_horizon_fence_island;
#[cfg(clean_islands)]
pub use compaction_pin_horizon_fence_island::{
    compaction_base_advance, compaction_safe_retain_clamp,
};

#[cfg(not(clean_islands))]
/// Clamp a requested `retain_before` offset so it never truncates past `pin_ceiling`.
#[must_use]
pub const fn compaction_safe_retain_clamp(requested_offset: u64, pin_ceiling: u64) -> u64 {
    if requested_offset < pin_ceiling {
        requested_offset
    } else {
        pin_ceiling
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `BrokerLog` `base_offset` after safe prefix compaction.
#[must_use]
pub const fn compaction_base_advance(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}

contract_fn! {
    /// True iff `cand_base` strictly advances `cur_base` without exceeding `pin_ceiling`.
    #[must_use]
    pub const fn compaction_can_truncate(cur_base: u64, cand_base: u64, pin_ceiling: u64) -> bool
    clauses [ensures result == (cur_base < cand_base && cand_base <= pin_ceiling)]
    {
        cur_base < cand_base && cand_base <= pin_ceiling
    }
}

/// Maximum live `/a/bind` or `/a/will` pin slots tracked per shard horizon fence.
pub const MAX_COMPACTION_PINS: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PinEntry {
    active: bool,
    owner_key: u64,
    pinned_offset: u64,
}

impl PinEntry {
    const EMPTY: Self = Self {
        active: false,
        owner_key: 0,
        pinned_offset: 0,
    };
}

///Incremental `/a/bind` + `/a/will` compaction horizon fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactionPinHorizonFence {
    pins: [PinEntry; MAX_COMPACTION_PINS],
    active_pins: usize,
    base_offset: u64,
}

impl CompactionPinHorizonFence {
    #[must_use]
    pub const fn new(initial_base: u64) -> Self {
        Self {
            pins: [PinEntry::EMPTY; MAX_COMPACTION_PINS],
            active_pins: 0,
            base_offset: initial_base,
        }
    }

    #[must_use]
    pub const fn base_offset(&self) -> u64 {
        self.base_offset
    }

    #[must_use]
    pub const fn active_pins(&self) -> usize {
        self.active_pins
    }

    /// Upsert a live `/a/bind` or `/a/will` pin at `pinned_offset` (superseding any older pin for `owner_key`).
    pub fn upsert_pin(&mut self, owner_key: u64, pinned_offset: u64) -> bool {
        let mut idx = 0usize;
        let mut free_idx: Option<usize> = None;
        while let Some(pin) = self.pins.get_mut(idx) {
            if pin.active {
                if pin.owner_key == owner_key {
                    pin.pinned_offset = pinned_offset;
                    return true;
                }
            } else if free_idx.is_none() {
                free_idx = Some(idx);
            }
            idx = idx.saturating_add(1);
        }
        if let Some(slot) = free_idx {
            if let Some(pin) = self.pins.get_mut(slot) {
                *pin = PinEntry {
                    active: true,
                    owner_key,
                    pinned_offset,
                };
                self.active_pins = self.active_pins.saturating_add(1);
                return true;
            }
        }
        false
    }

    /// Release a pin when a connection disconnects (will fired/cleared) or a binding is tombstoned.
    pub fn release_pin(&mut self, owner_key: u64) -> bool {
        let mut idx = 0usize;
        while let Some(pin) = self.pins.get_mut(idx) {
            if pin.active && pin.owner_key == owner_key {
                *pin = PinEntry::EMPTY;
                self.active_pins = self.active_pins.saturating_sub(1);
                return true;
            }
            idx = idx.saturating_add(1);
        }
        false
    }

    /// Compute the lowest live pinned offset, or `hw_offset` if no live pins exist.
    #[must_use]
    pub fn effective_pin_ceiling(&self, hw_offset: u64) -> u64 {
        let mut ceiling = hw_offset;
        let mut rest: &[PinEntry] = &self.pins;
        while let [p, tail @ ..] = rest {
            if p.active && p.pinned_offset < ceiling {
                ceiling = p.pinned_offset;
            }
            rest = tail;
        }
        ceiling
    }

    /// Compute and commit the safe new `base_offset` for `retain_before(requested_offset)`.
    pub fn plan_retain_before(&mut self, requested_offset: u64, hw_offset: u64) -> u64 {
        let ceiling = self.effective_pin_ceiling(hw_offset);
        let safe_target = compaction_safe_retain_clamp(requested_offset, ceiling);
        if compaction_can_truncate(self.base_offset, safe_target, ceiling) {
            self.base_offset = compaction_base_advance(self.base_offset, safe_target);
        }
        self.base_offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clamps_compaction_at_oldest_live_will_or_bind_pin_until_released() {
        let mut fence = CompactionPinHorizonFence::new(0);
        assert!(fence.upsert_pin(101, 40));
        assert!(fence.upsert_pin(202, 85));
        // Requesting retain_before(100) with hw=120 stops at pin 101's offset 40:
        assert_eq!(fence.plan_retain_before(100, 120), 40);
        // Releasing pin 101 unblocks compaction up to pin 202's offset 85:
        assert!(fence.release_pin(101));
        assert_eq!(fence.plan_retain_before(100, 120), 85);
        // Superseding pin 202 to offset 110 unblocks compaction to requested 100:
        assert!(fence.upsert_pin(202, 110));
        assert_eq!(fence.plan_retain_before(100, 120), 100);
    }
}
