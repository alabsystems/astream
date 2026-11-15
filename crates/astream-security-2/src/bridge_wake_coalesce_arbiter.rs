// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-recipient bridge wake budget and priority coalescing arbiter
//! (`docs/DESIGN-aterm-fabric.md` §5.6, §15; `Astream.Pump.TlaBridgeWakeCoalesceArbiter`).
//!
//! Enforces `serve --wake-budget` coalescing per recipient session with the §5.6 priority lattice:
//! `Control > Ask > Task > Answer > Report > Ack > Note`.
//! Multiple inbox deliveries arriving while a recipient's per-window wake budget is exhausted or
//! coalescing coalesce into a single pending wake carrying the highest seen priority, the message
//! count, and a monotonically advancing `high_water_offset`.

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
#[path = "bridge_wake_coalesce_arbiter_island.rs"]
mod bridge_wake_coalesce_arbiter_island;
#[cfg(clean_islands)]
pub use bridge_wake_coalesce_arbiter_island::{
    wake_budget_used_clamp_b124, wake_offset_advance_b124, wake_priority_max_b124,
};

#[cfg(not(clean_islands))]
/// Clamp wakes emitted in the current budget window to `max_budget`.
#[must_use]
pub const fn wake_budget_used_clamp_b124(cand_used: u64, max_budget: u64) -> u64 {
    if cand_used < max_budget {
        cand_used
    } else {
        max_budget
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the recipient's wake `high_water_offset`.
#[must_use]
pub const fn wake_offset_advance_b124(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
/// Coalesce two wake priority ranks by selecting the higher priority (`max`).
#[must_use]
pub const fn wake_priority_max_b124(cur_rank: u64, cand_rank: u64) -> u64 {
    if cur_rank < cand_rank {
        cand_rank
    } else {
        cur_rank
    }
}

contract_fn! {
    /// True iff `wakes_used < max_budget` (at least one wake token remains in this window).
    #[must_use]
    pub const fn wake_budget_has_room_b124(wakes_used: u64, max_budget: u64) -> bool
    clauses [ensures result == (wakes_used < max_budget)]
    {
        wakes_used < max_budget
    }
}

/// Fabric `in/` message kind ordered by §5.6 wake priority (`Control > Ask > Task > … > Note`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeMailKind {
    Note,
    Ack,
    Report,
    Answer,
    Task,
    Ask,
    Control,
}

impl WakeMailKind {
    #[must_use]
    pub const fn rank(self) -> u64 {
        match self {
            Self::Note => 1,
            Self::Ack => 2,
            Self::Report => 3,
            Self::Answer => 4,
            Self::Task => 5,
            Self::Ask => 6,
            Self::Control => 7,
        }
    }

    #[must_use]
    pub const fn from_rank(rank: u64) -> Option<Self> {
        match rank {
            1 => Some(Self::Note),
            2 => Some(Self::Ack),
            3 => Some(Self::Report),
            4 => Some(Self::Answer),
            5 => Some(Self::Task),
            6 => Some(Self::Ask),
            7 => Some(Self::Control),
            _ => None,
        }
    }
}

/// Outcome of enqueuing or flushing a recipient wake.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeArbiterAction {
    /// Emitted a wake immediately or upon window refill.
    EmitWake {
        dominant_kind: WakeMailKind,
        coalesced_count: u64,
        high_water_offset: u64,
        wakes_used: u64,
    },
    /// Coalesced behind the current window budget limit (`wakes_used == max_budget`).
    CoalescedPending {
        dominant_kind: WakeMailKind,
        coalesced_count: u64,
        high_water_offset: u64,
    },
    /// Offset already covered by `flushed_high_water` (duplicate delivery suppressed).
    DuplicateOffsetIgnored { flushed_high_water: u64 },
    /// Nothing pending to flush.
    Idle,
}

/// Per-recipient wake budget & coalescing arbiter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BridgeWakeCoalesceArbiter {
    max_budget: u64,
    wakes_used: u64,
    flushed_high_water: u64,
    pending_rank: u64,
    pending_count: u64,
    pending_high_water: u64,
}

impl BridgeWakeCoalesceArbiter {
    #[must_use]
    pub const fn new(max_budget: u64) -> Self {
        Self {
            max_budget,
            wakes_used: 0,
            flushed_high_water: 0,
            pending_rank: 0,
            pending_count: 0,
            pending_high_water: 0,
        }
    }

    #[must_use]
    pub const fn flushed_high_water(&self) -> u64 {
        self.flushed_high_water
    }

    #[must_use]
    pub const fn wakes_used(&self) -> u64 {
        self.wakes_used
    }

    /// Record an inbound message at 1-based `record_offset` (`>= 1`) with `kind`.
    #[allow(clippy::manual_unwrap_or)]
    pub fn on_inbox_delivery(
        &mut self,
        record_offset: u64,
        kind: WakeMailKind,
    ) -> WakeArbiterAction {
        let seen_floor = wake_offset_advance_b124(self.flushed_high_water, self.pending_high_water);
        if record_offset == 0 || record_offset <= seen_floor {
            return WakeArbiterAction::DuplicateOffsetIgnored {
                flushed_high_water: seen_floor,
            };
        }
        self.pending_rank = wake_priority_max_b124(self.pending_rank, kind.rank());
        self.pending_count = self.pending_count.saturating_add(1);
        self.pending_high_water = wake_offset_advance_b124(self.pending_high_water, record_offset);

        let dominant = match WakeMailKind::from_rank(self.pending_rank) {
            Some(k) => k,
            None => kind,
        };
        if wake_budget_has_room_b124(self.wakes_used, self.max_budget) {
            self.wakes_used =
                wake_budget_used_clamp_b124(self.wakes_used.saturating_add(1), self.max_budget);
            let count = self.pending_count;
            let hw = self.pending_high_water;
            self.flushed_high_water = wake_offset_advance_b124(self.flushed_high_water, hw);
            self.pending_rank = 0;
            self.pending_count = 0;
            WakeArbiterAction::EmitWake {
                dominant_kind: dominant,
                coalesced_count: count,
                high_water_offset: self.flushed_high_water,
                wakes_used: self.wakes_used,
            }
        } else {
            WakeArbiterAction::CoalescedPending {
                dominant_kind: dominant,
                coalesced_count: self.pending_count,
                high_water_offset: self.pending_high_water,
            }
        }
    }

    /// Refill the recipient's wake budget at the next window boundary and emit any coalesced wake.
    #[allow(clippy::manual_unwrap_or)]
    pub fn on_window_refill(&mut self) -> WakeArbiterAction {
        self.wakes_used = 0;
        if self.pending_count == 0 {
            return WakeArbiterAction::Idle;
        }
        if !wake_budget_has_room_b124(self.wakes_used, self.max_budget) {
            let dominant = match WakeMailKind::from_rank(self.pending_rank) {
                Some(k) => k,
                None => WakeMailKind::Note,
            };
            return WakeArbiterAction::CoalescedPending {
                dominant_kind: dominant,
                coalesced_count: self.pending_count,
                high_water_offset: self.pending_high_water,
            };
        }
        self.wakes_used = wake_budget_used_clamp_b124(1, self.max_budget);
        let dominant = match WakeMailKind::from_rank(self.pending_rank) {
            Some(k) => k,
            None => WakeMailKind::Note,
        };
        let count = self.pending_count;
        self.flushed_high_water =
            wake_offset_advance_b124(self.flushed_high_water, self.pending_high_water);
        self.pending_rank = 0;
        self.pending_count = 0;
        WakeArbiterAction::EmitWake {
            dominant_kind: dominant,
            coalesced_count: count,
            high_water_offset: self.flushed_high_water,
            wakes_used: self.wakes_used,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_wake_budget_and_coalesces_note_task_ask_control_in_priority_order() {
        let mut arb = BridgeWakeCoalesceArbiter::new(1);

        // First wake consumes the 1-wake budget immediately.
        assert_eq!(
            arb.on_inbox_delivery(10, WakeMailKind::Note),
            WakeArbiterAction::EmitWake {
                dominant_kind: WakeMailKind::Note,
                coalesced_count: 1,
                high_water_offset: 10,
                wakes_used: 1,
            }
        );
        // Duplicate offset <= 10 is ignored.
        assert_eq!(
            arb.on_inbox_delivery(10, WakeMailKind::Control),
            WakeArbiterAction::DuplicateOffsetIgnored {
                flushed_high_water: 10
            }
        );

        // Next three messages arrive in the same window -> coalesce and promote priority:
        // Note -> Task -> Control -> Ask keeps Control as dominant!
        assert_eq!(
            arb.on_inbox_delivery(11, WakeMailKind::Note),
            WakeArbiterAction::CoalescedPending {
                dominant_kind: WakeMailKind::Note,
                coalesced_count: 1,
                high_water_offset: 11,
            }
        );
        assert_eq!(
            arb.on_inbox_delivery(12, WakeMailKind::Task),
            WakeArbiterAction::CoalescedPending {
                dominant_kind: WakeMailKind::Task,
                coalesced_count: 2,
                high_water_offset: 12,
            }
        );
        assert_eq!(
            arb.on_inbox_delivery(15, WakeMailKind::Control),
            WakeArbiterAction::CoalescedPending {
                dominant_kind: WakeMailKind::Control,
                coalesced_count: 3,
                high_water_offset: 15,
            }
        );
        assert_eq!(
            arb.on_inbox_delivery(18, WakeMailKind::Ask),
            WakeArbiterAction::CoalescedPending {
                dominant_kind: WakeMailKind::Control,
                coalesced_count: 4,
                high_water_offset: 18,
            }
        );

        // Window refill emits ONE coalesced wake carrying Control and count=4 up to offset 18.
        assert_eq!(
            arb.on_window_refill(),
            WakeArbiterAction::EmitWake {
                dominant_kind: WakeMailKind::Control,
                coalesced_count: 4,
                high_water_offset: 18,
                wakes_used: 1,
            }
        );
        assert_eq!(arb.on_window_refill(), WakeArbiterAction::Idle);
    }
}
