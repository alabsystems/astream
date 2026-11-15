// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Single-subject `pub/<node>/node/ack` fleet-halt roster completion & watermark fence
//! (`docs/DESIGN-aterm-fabric.md` §5.3 lines 1345–1390, aterm `7c2985c01`, `ce2cf6a59`, `7f8d6c38a`;
//! `Astream.Broker.TlaFleetHaltRosterAckFence`).
//!
//! Protects node subject budget (1 retained `pub/<node>/node/ack` subject for node lifetime) and
//! prevents premature halt acks during seamless updates:
//! - Observer bridges hold nothing and ack nothing,
//! - A bridge whose verb lane died (`verb_lane_alive == false`) acks nothing so its successor's
//!   `Last` snapshot answers once applied (`7f8d6c38a`),
//! - `ERR busy` on any roster session leaves the halt owed (`busy_sessions > 0`) for the `2s`
//!   roster backstop (`ce2cf6a59`), while `ERR no such session` counts as reached,
//! - Counter interpretation: a node row naming `re > target_halt_off` is `UnknownSupersededByLater`,
//!   never `Missing`!

#[cfg(clean_islands)]
#[path = "fleet_halt_roster_ack_fence_island.rs"]
mod fleet_halt_roster_ack_fence_island;
#[cfg(clean_islands)]
pub use fleet_halt_roster_ack_fence_island::{
    halt_ack_pending_clamp_b133, halt_ack_watermark_advance_b133,
};

/// Maximum tracked sessions per node roster sweep (`512`).
pub const MAX_ROSTER_SESSIONS: u64 = 512;

#[cfg(not(clean_islands))]
/// Clamp remaining `ERR busy` session count to `roster_cap`.
#[must_use]
pub const fn halt_ack_pending_clamp_b133(cand_pending: u64, roster_cap: u64) -> u64 {
    if cand_pending < roster_cap {
        cand_pending
    } else {
        roster_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance durable halt-ack offset watermark (`offset + 1`).
#[must_use]
pub const fn halt_ack_watermark_advance_b133(cur_acked: u64, cand_acked: u64) -> u64 {
    if cur_acked < cand_acked {
        cand_acked
    } else {
        cur_acked
    }
}

contract_fn! {
    /// True iff `verb_lane_alive && busy_count == 0 && acked_watermark < halt_off_plus_one`.
    #[must_use]
    pub const fn halt_ack_ready_to_publish_b133(
        verb_lane_alive: bool,
        busy_count: u64,
        halt_off_plus_one: u64,
        acked_watermark: u64,
    ) -> bool
    clauses [ensures result == (verb_lane_alive && busy_count == 0 && acked_watermark < halt_off_plus_one)]
    {
        verb_lane_alive && busy_count == 0 && acked_watermark < halt_off_plus_one
    }
}

/// Issuer-side reading of a node's single retained `pub/<node>/node/ack` row against `target_halt_off`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeHaltAckReading {
    /// `re == target_halt_off`: authoritative answer for this halt!
    AckedTarget,
    /// `re < target_halt_off`: node has not yet acked `target_halt_off`.
    PendingBehindTarget,
    /// `re > target_halt_off`: node already acked a NEWER halt -> status for `target_halt_off` is unknown, NOT missing!
    UnknownSupersededByLater,
}

/// Interpret a node's single retained `re=<ack_re_off>` row against `target_halt_off` (§5.3 lines 1357–1361).
#[must_use]
pub const fn read_node_halt_ack_row(ack_re_off: u64, target_halt_off: u64) -> NodeHaltAckReading {
    if ack_re_off == target_halt_off {
        NodeHaltAckReading::AckedTarget
    } else if ack_re_off < target_halt_off {
        NodeHaltAckReading::PendingBehindTarget
    } else {
        NodeHaltAckReading::UnknownSupersededByLater
    }
}

/// Bridge-side fleet-halt roster completion and watermark gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FleetHaltRosterAckFence {
    observer_mode: bool,
    acked_watermark: u64, // halt_offset + 1
    owed_halt_plus_one: u64,
    busy_sessions: u64,
}

impl FleetHaltRosterAckFence {
    #[must_use]
    pub const fn new(observer_mode: bool, persisted_acked_watermark: u64) -> Self {
        Self {
            observer_mode,
            acked_watermark: persisted_acked_watermark,
            owed_halt_plus_one: 0,
            busy_sessions: 0,
        }
    }

    #[must_use]
    pub const fn acked_watermark(&self) -> u64 {
        self.acked_watermark
    }

    /// Attempt to apply a standing (`Last`) or tail halt at `halt_offset` across the local roster.
    /// `no_such_session_count` is ignored as reached; `busy_count` blocks the ack until a 2s retry pass lands!
    pub fn evaluate_roster_pass(
        &mut self,
        halt_offset: u64,
        verb_lane_alive: bool,
        roster_readable: bool,
        busy_count: u64,
        _no_such_session_count: u64,
    ) -> bool {
        if self.observer_mode {
            return false;
        }
        let target_plus_one = halt_offset.saturating_add(1);
        if target_plus_one > self.owed_halt_plus_one {
            self.owed_halt_plus_one = target_plus_one;
        }
        let effective_busy = if roster_readable {
            halt_ack_pending_clamp_b133(busy_count, MAX_ROSTER_SESSIONS)
        } else {
            1
        };
        self.busy_sessions = effective_busy;
        if halt_ack_ready_to_publish_b133(
            verb_lane_alive,
            effective_busy,
            self.owed_halt_plus_one,
            self.acked_watermark,
        ) {
            self.acked_watermark =
                halt_ack_watermark_advance_b133(self.acked_watermark, self.owed_halt_plus_one);
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
    fn withholds_ack_on_busy_or_dead_verb_lane_and_marks_superseded_re_unknown() {
        let mut f = FleetHaltRosterAckFence::new(false, 0);
        // Busy session during seamless update withholds ack!
        assert!(!f.evaluate_roster_pass(10, true, true, 1, 2));
        assert_eq!(f.acked_watermark(), 0);
        // Dead verb lane ALSO withholds ack (`7f8d6c38a`)!
        assert!(!f.evaluate_roster_pass(10, false, true, 0, 0));
        // Clean roster pass (`no_such_session` = 3 is fine!) publishes ack once and advances watermark!
        assert!(f.evaluate_roster_pass(10, true, true, 0, 3));
        assert_eq!(f.acked_watermark(), 11);
        // Reconnect snapshot re-reading halt 10 does NOT re-ack!
        assert!(!f.evaluate_roster_pass(10, true, true, 0, 0));

        assert_eq!(
            read_node_halt_ack_row(25, 10),
            NodeHaltAckReading::UnknownSupersededByLater
        );
    }
}
