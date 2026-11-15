// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Retention-gap `reset_escape` torn-VT/OSC clearing & stderr-before-stdout wake barrier
//! (`evidence/manifest.toml` `pump.wake-on-boundaries`, `pump.cli.wake-lines`;
//! `Astream.Pump.TlaRetentionGapEscapeResetGuard`).
//!
//! Enforces `Pump`/`aspump` R4 addendum A9 gap recovery:
//! - On a retention gap `[gap_from, gap_to)`, torn pre-gap OSC-133 carry, DEC `?2026` sync-update
//!   budgets, and unfinished CSI/OSC/DCS parser state MUST be cleared (`reset_escape`) while
//!   preserving painted cells so torn pre-gap bytes neither forge phantom `CommandEnd` wakes nor
//!   swallow post-gap prompts!
//! - No post-gap wake line may be emitted on stdout until the pending `GAP from=<F> to=<T>` notice
//!   has been drained (`take_gap` / stderr emit)!

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
#[path = "retention_gap_escape_reset_guard_island.rs"]
mod retention_gap_escape_reset_guard_island;
#[cfg(clean_islands)]
pub use retention_gap_escape_reset_guard_island::{
    gap_resume_offset_advance_b143, post_gap_carry_clamp_b143,
};

/// Maximum mid-record OSC-133 carry buffer (`1_024` bytes).
pub const MAX_ESCAPE_CARRY_BYTES: u64 = 1_024;

#[cfg(not(clean_islands))]
/// Monotonically advance the pump cursor across a retention gap `to` offset.
#[must_use]
pub const fn gap_resume_offset_advance_b143(cur_off: u64, gap_to_off: u64) -> u64 {
    if cur_off < gap_to_off {
        gap_to_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
/// Clamp mid-record escape carry length to `carry_cap`.
#[must_use]
pub const fn post_gap_carry_clamp_b143(cand_carry: u64, carry_cap: u64) -> u64 {
    if cand_carry < carry_cap {
        cand_carry
    } else {
        carry_cap
    }
}

contract_fn! {
    /// Post-gap stdout wake emission is admissible ONLY once the pending gap notice has been
    /// surfaced and torn pre-gap escape carry has been reset.
    #[must_use]
    pub const fn post_gap_wake_admissible_b143(
        gap_notice_pending: bool,
        escape_carry_cleared: bool,
    ) -> bool
    clauses [ensures result == (!gap_notice_pending && escape_carry_cleared)]
    {
        !gap_notice_pending && escape_carry_cleared
    }
}

/// Gate verdict for pump wake emission across retention gaps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PumpGapBarrierDecision {
    SurfaceGapNoticeFirst { gap_from: u64, gap_to: u64 },
    AdmitWakeLine { cursor_offset: u64 },
}

/// Pump retention-gap escape-reset & notice-ordering state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PumpGapEscapeBarrier {
    cursor_offset: u64,
    escape_carry_bytes: u64,
    sync_mode_latched: bool,
    pending_gap: Option<(u64, u64)>,
    escape_carry_cleared: bool,
}

impl PumpGapEscapeBarrier {
    #[must_use]
    pub const fn new(initial_offset: u64) -> Self {
        Self {
            cursor_offset: initial_offset,
            escape_carry_bytes: 0,
            sync_mode_latched: false,
            pending_gap: None,
            escape_carry_cleared: true,
        }
    }

    pub fn record_partial_escape(&mut self, raw_carry_bytes: u64, in_sync_mode: bool) {
        self.escape_carry_bytes =
            post_gap_carry_clamp_b143(raw_carry_bytes, MAX_ESCAPE_CARRY_BYTES);
        self.sync_mode_latched = in_sync_mode;
    }

    /// Observe an inbound `Gap { from, to }`: advances cursor and immediately resets torn escape
    /// carry + DEC `?2026` sync latch while staging the gap notice!
    pub fn on_retention_gap(&mut self, gap_from: u64, gap_to: u64) {
        self.cursor_offset = gap_resume_offset_advance_b143(self.cursor_offset, gap_to);
        self.escape_carry_bytes = 0;
        self.sync_mode_latched = false;
        self.escape_carry_cleared = true;
        self.pending_gap = Some((gap_from, self.cursor_offset));
    }

    pub fn take_gap_notice(&mut self) -> Option<(u64, u64)> {
        core::mem::take(&mut self.pending_gap)
    }

    #[must_use]
    pub const fn check_wake_emission(&self) -> PumpGapBarrierDecision {
        if let Some((gap_from, gap_to)) = self.pending_gap {
            return PumpGapBarrierDecision::SurfaceGapNoticeFirst { gap_from, gap_to };
        }
        if post_gap_wake_admissible_b143(false, self.escape_carry_cleared) {
            PumpGapBarrierDecision::AdmitWakeLine {
                cursor_offset: self.cursor_offset,
            }
        } else {
            PumpGapBarrierDecision::SurfaceGapNoticeFirst {
                gap_from: self.cursor_offset,
                gap_to: self.cursor_offset,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retention_gap_resets_torn_escape_and_orders_stderr_notice_before_wake() {
        let mut b = PumpGapEscapeBarrier::new(10);
        b.record_partial_escape(48, true);
        b.on_retention_gap(10, 250);
        assert_eq!(b.escape_carry_bytes, 0);
        assert!(!b.sync_mode_latched);
        // Wake blocked until `take_gap_notice()` drains the gap notice to stderr:
        assert_eq!(
            b.check_wake_emission(),
            PumpGapBarrierDecision::SurfaceGapNoticeFirst {
                gap_from: 10,
                gap_to: 250
            }
        );
        assert_eq!(b.take_gap_notice(), Some((10, 250)));
        assert_eq!(
            b.check_wake_emission(),
            PumpGapBarrierDecision::AdmitWakeLine { cursor_offset: 250 }
        );
    }
}
