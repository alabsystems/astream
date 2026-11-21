// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Three-phase zero-drop region-gateway drain controller (`Serving -> Draining -> Closed`)
//! (`Astream.Mesh.TlaGatewayDrain`).

#[cfg(clean_islands)]
#[path = "gateway_drain_island.rs"]
mod gateway_drain_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn drain_inflight_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn drain_phase_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use gateway_drain_island::{drain_inflight_clamp, drain_phase_advance};

/// Maximum concurrent streams accepted on a regional gateway before drain.
pub const MAX_DRAINING_STREAMS: u64 = 1024;
/// Phase `0`: accepting new streams.
pub const DRAIN_PHASE_SERVING: u64 = 0;
/// Phase `1`: refusing new streams while draining existing ones.
pub const DRAIN_PHASE_DRAINING: u64 = 1;
/// Phase `2`: fully quiesced or deadline-closed.
pub const DRAIN_PHASE_CLOSED: u64 = 2;

contract_fn! {
    /// Verified quiescence check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `drain_quiesced_isl`.
    #[must_use]
    pub const fn drain_quiesced(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Monotone 3-phase graceful gateway drain barrier.
#[derive(Debug, Clone)]
pub struct GatewayDrainController {
    max_streams: u64,
    phase: u64,
    active_streams: u64,
    deadline_ms: u64,
}

impl Default for GatewayDrainController {
    fn default() -> Self {
        Self::new()
    }
}

impl GatewayDrainController {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_streams: MAX_DRAINING_STREAMS,
            phase: DRAIN_PHASE_SERVING,
            active_streams: 0,
            deadline_ms: u64::MAX,
        }
    }

    #[must_use]
    pub const fn phase(&self) -> u64 {
        self.phase
    }

    #[must_use]
    pub const fn active_streams(&self) -> u64 {
        self.active_streams
    }

    pub fn try_open_stream(&mut self) -> bool {
        if self.phase != DRAIN_PHASE_SERVING || self.active_streams >= self.max_streams {
            return false;
        }
        let next = self.active_streams.saturating_add(1);
        self.active_streams = drain_inflight_clamp(next, self.max_streams);
        true
    }

    pub fn close_stream(&mut self) -> bool {
        if self.active_streams == 0 {
            return self.phase == DRAIN_PHASE_CLOSED;
        }
        self.active_streams = self.active_streams.saturating_sub(1);
        if self.phase == DRAIN_PHASE_DRAINING && self.active_streams == 0 {
            self.phase = drain_phase_advance(self.phase, DRAIN_PHASE_CLOSED);
        }
        self.phase == DRAIN_PHASE_CLOSED
    }

    pub fn begin_drain(&mut self, deadline_ms: u64) -> u64 {
        if self.phase == DRAIN_PHASE_SERVING || deadline_ms < self.deadline_ms {
            self.deadline_ms = deadline_ms;
        }
        let target = if self.active_streams == 0 {
            DRAIN_PHASE_CLOSED
        } else {
            DRAIN_PHASE_DRAINING
        };
        self.phase = drain_phase_advance(self.phase, target);
        self.phase
    }

    pub fn poll_deadline(&mut self, now_ms: u64) -> bool {
        if self.phase == DRAIN_PHASE_DRAINING && drain_quiesced(now_ms, self.deadline_ms) {
            self.phase = drain_phase_advance(self.phase, DRAIN_PHASE_CLOSED);
        }
        self.phase == DRAIN_PHASE_CLOSED
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gateway_drain_refuses_new_streams_and_closes_when_inflight_hits_zero() {
        let mut gw = GatewayDrainController::new();
        assert!(gw.try_open_stream());
        assert!(gw.try_open_stream());
        assert_eq!(gw.begin_drain(5_000), DRAIN_PHASE_DRAINING);
        assert!(!gw.try_open_stream());
        assert!(!gw.close_stream());
        assert!(gw.close_stream());
        assert_eq!(gw.phase(), DRAIN_PHASE_CLOSED);
    }
}
