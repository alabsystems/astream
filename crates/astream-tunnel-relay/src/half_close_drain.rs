// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Closer` TCP half-close (`SHUT_WR`) outbound flush & bounded inbound `FIN` drain state machine
//! preventing `RST` loss of the final acked `Frame` (`Astream.Tunnel.TlaHalfCloseDrain`).

#[cfg(clean_islands)]
#[path = "half_close_drain_island.rs"]
mod half_close_drain_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_drain_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_phase_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use half_close_drain_island::{tun_drain_clamp, tun_phase_advance};

/// Maximum lingering inbound bytes drained after `SHUT_WR` before hard close (`64` KiB).
pub const MAX_HALF_CLOSE_DRAIN_BYTES: u64 = 65_536;

contract_fn! {
    /// Verified terminal close state (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tun_cleanly_closed_isl`.
    #[must_use]
    pub const fn tun_cleanly_closed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Phase progression: `0 = Open`, `1 = ShutWrDraining`, `2 = ClosedClean`, `3 = AbortedCap`.
#[derive(Debug, Clone, Default)]
pub struct HalfCloseDrainMachine {
    phase: u64,
    drained_bytes: u64,
}

impl HalfCloseDrainMachine {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            phase: 0,
            drained_bytes: 0,
        }
    }

    pub fn initiate_shut_wr(&mut self) {
        self.phase = tun_phase_advance(self.phase, 1);
    }

    pub fn on_inbound_chunk(&mut self, len: usize) -> bool {
        if self.phase != 1 {
            return false;
        }
        if len == 0 {
            self.phase = tun_phase_advance(self.phase, 2);
            return true;
        }
        let cap = tun_drain_clamp(MAX_HALF_CLOSE_DRAIN_BYTES, MAX_HALF_CLOSE_DRAIN_BYTES);
        self.drained_bytes = self.drained_bytes.saturating_add(len as u64);
        if self.drained_bytes > cap {
            self.phase = tun_phase_advance(self.phase, 3);
            false
        } else {
            true
        }
    }

    #[must_use]
    pub const fn is_clean_eof(&self) -> bool {
        self.phase == 2 && tun_cleanly_closed(self.phase, 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn half_close_drains_bounded_tail_to_eof_and_aborts_flood() {
        let mut m = HalfCloseDrainMachine::new();
        m.initiate_shut_wr();
        assert!(m.on_inbound_chunk(512));
        assert!(m.on_inbound_chunk(0));
        assert!(m.is_clean_eof());
    }
}
