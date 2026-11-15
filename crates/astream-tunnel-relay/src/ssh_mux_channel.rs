// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-channel RFC 4254 / HTTP-2 style credit window controller (`<= 2` MiB) preventing a bulk
//! log `Fetch` stream from head-of-line starving interactive PTY keystrokes over a shared WAN
//! tunnel (`Astream.Tunnel.TlaSshMuxChannel`).

#[cfg(clean_islands)]
#[path = "ssh_mux_channel_island.rs"]
mod ssh_mux_channel_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_win_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_grant_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ssh_mux_channel_island::{tun_grant_advance, tun_win_clamp};

/// Maximum per-channel send window (`2` MiB).
pub const MAX_MUX_CHANNEL_WINDOW: u64 = 2 * 1024 * 1024;

contract_fn! {
    /// Verified channel credit sufficiency (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tun_credit_available_isl`.
    #[must_use]
    pub const fn tun_credit_available(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Tracks available byte credit and monotone `WINDOW_ADJUST` replenishments for one logical stream.
#[derive(Debug, Clone)]
pub struct MuxChannelWindow {
    available: u64,
    total_granted: u64,
}

impl MuxChannelWindow {
    #[must_use]
    pub const fn new(initial_window: u64) -> Self {
        let w = tun_win_clamp(initial_window, MAX_MUX_CHANNEL_WINDOW);
        Self {
            available: w,
            total_granted: w,
        }
    }

    pub fn try_consume(&mut self, bytes: u64) -> bool {
        if !tun_credit_available(self.available, bytes) {
            return false;
        }
        self.available = self.available.saturating_sub(bytes);
        true
    }

    pub fn replenish(&mut self, adjust_bytes: u64) -> u64 {
        self.available = tun_win_clamp(
            self.available.saturating_add(adjust_bytes),
            MAX_MUX_CHANNEL_WINDOW,
        );
        self.total_granted = tun_grant_advance(
            self.total_granted,
            self.total_granted.saturating_add(adjust_bytes),
        );
        self.available
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mux_window_enforces_credit_and_clamps_window_adjust_to_ceiling() {
        let mut w = MuxChannelWindow::new(4_096);
        assert!(w.try_consume(3_000));
        assert!(!w.try_consume(2_000));
        assert_eq!(w.replenish(2_000), 3_096);
        assert!(w.try_consume(2_000));
    }
}
