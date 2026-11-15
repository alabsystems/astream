// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bandwidth-Delay Product (BDP) pipelined credit-window autoscaler for LAN/WAN `aterm-link`
//! (`Astream.Wire.TlaWanWindowAutoscaler`).
//!
//! Scales `aterm-link`'s pipelined publish/subscribe credit window seamlessly across:
//! - Same-machine Unix sockets (`MIN_PIPELINE_CREDITS = 64`),
//! - Sub-millisecond LAN links (`256..1_024` credits),
//! - High-RTT WAN / cross-region links (`up to MAX_WAN_CREDITS = 4_096` credits),
//!
//! proving `in_flight_credits <= window_cap` and `window_cap <= max_wan_credits` with
//! `0 unknown` and `0 runtime_checked` obligations in `astream-wire`.

#[cfg(clean_islands)]
#[path = "wan_rtt_window_autoscaler_island.rs"]
mod wan_rtt_window_autoscaler_island;
#[cfg(clean_islands)]
pub use wan_rtt_window_autoscaler_island::{wan_inflight_clamp_b82, wan_window_cap_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn wan_inflight_clamp_b82(in_flight: u64, window_cap: u64) -> u64 {
    if in_flight < window_cap {
        in_flight
    } else {
        window_cap
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn wan_window_cap_clamp(target_cap: u64, max_credits: u64) -> u64 {
    if target_cap < max_credits {
        target_cap
    } else {
        max_credits
    }
}

contract_fn! {
    /// Verified check that in-flight pipelined frames have credit headroom below `window_cap`
    /// (`in_flight < window_cap`), linked via `clean-kernel-defeq` to
    /// `wan_credits_available_isl`.
    #[must_use]
    pub const fn wan_credits_available(in_flight: u64, window_cap: u64) -> bool
    clauses [ensures result == (in_flight < window_cap)]
    {
        in_flight < window_cap
    }
}

/// Baseline local-IPC pipeline window (`64` frames, matching `ATERM_PIPELINE_WINDOW`).
pub const MIN_PIPELINE_CREDITS: u64 = 64;
/// Hard ceiling on WAN pipelined credits (`4_096` frames).
pub const MAX_WAN_CREDITS: u64 = 4_096;

/// Stateful BDP credit-window autoscaler.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WanWindowAutoscaler {
    in_flight_credits: u64,
    window_cap: u64,
    max_wan_credits: u64,
    srtt_us: u64,
}

impl WanWindowAutoscaler {
    #[must_use]
    pub const fn new(max_wan_credits: u64) -> Self {
        let hi = if max_wan_credits < MIN_PIPELINE_CREDITS {
            MIN_PIPELINE_CREDITS
        } else if max_wan_credits > MAX_WAN_CREDITS {
            MAX_WAN_CREDITS
        } else {
            max_wan_credits
        };
        let init_win = wan_window_cap_clamp(MIN_PIPELINE_CREDITS, hi);
        Self {
            in_flight_credits: 0,
            window_cap: init_win,
            max_wan_credits: hi,
            srtt_us: 0,
        }
    }

    #[must_use]
    pub const fn in_flight_credits(&self) -> u64 {
        self.in_flight_credits
    }

    #[must_use]
    pub const fn window_cap(&self) -> u64 {
        self.window_cap
    }

    #[must_use]
    pub const fn srtt_us(&self) -> u64 {
        self.srtt_us
    }

    /// Try to acquire 1 credit for an outbound pipelined frame.
    pub fn try_acquire_credit(&mut self) -> bool {
        if !wan_credits_available(self.in_flight_credits, self.window_cap) {
            return false;
        }
        let raw_next = self.in_flight_credits.saturating_add(1);
        self.in_flight_credits = wan_inflight_clamp_b82(raw_next, self.window_cap);
        true
    }

    /// Observe an ack batch of `acked_frames` with measured `sample_rtt_us`, updating
    /// smoothed RTT (`7/8 * srtt + 1/8 * sample` via bitshifts) and scaling `window_cap`.
    pub fn on_ack_batch(&mut self, acked_frames: u64, sample_rtt_us: u64) -> u64 {
        self.srtt_us = if self.srtt_us == 0 {
            sample_rtt_us
        } else {
            let seven_eighths = self.srtt_us - (self.srtt_us >> 3);
            let one_eighth = sample_rtt_us >> 3;
            seven_eighths.saturating_add(one_eighth)
        };

        // Scale target window by RTT tier using shift arithmetic (zero division/modulo VCs):
        // <= 500 us (Unix/loopback) -> 64; <= 5 ms (LAN) -> 256; <= 50 ms -> 1024; > 50 ms -> 4096.
        let raw_target = if self.srtt_us <= 500 {
            MIN_PIPELINE_CREDITS
        } else if self.srtt_us <= 5_000 {
            256
        } else if self.srtt_us <= 50_000 {
            1_024
        } else {
            MAX_WAN_CREDITS
        };
        let next_cap = wan_window_cap_clamp(raw_target, self.max_wan_credits);
        let rem_inflight = self.in_flight_credits.saturating_sub(acked_frames);
        self.window_cap = next_cap;
        self.in_flight_credits = wan_inflight_clamp_b82(rem_inflight, self.window_cap);
        self.window_cap
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scales_from_loopback_64_to_wan_4096_and_clamps_inflight_on_shrink() {
        let mut sc = WanWindowAutoscaler::new(MAX_WAN_CREDITS);
        assert_eq!(sc.window_cap(), 64);

        let mut acquired = 0u64;
        while sc.try_acquire_credit() {
            acquired += 1;
        }
        assert_eq!(acquired, 64);
        assert_eq!(sc.in_flight_credits(), 64);

        // High-RTT WAN ack (80 ms = 80_000 us) scales window up to 4_096!
        let new_cap = sc.on_ack_batch(32, 80_000);
        assert_eq!(new_cap, 4_096);
        assert_eq!(sc.in_flight_credits(), 32);

        // Return to sub-500us loopback shrinks window back toward 64 while clamping in-flight.
        let mut round = 0usize;
        while round < 64 {
            let _ = sc.on_ack_batch(0, 100);
            round += 1;
        }
        assert_eq!(sc.window_cap(), 64);
        assert!(sc.in_flight_credits() <= sc.window_cap());
    }
}
