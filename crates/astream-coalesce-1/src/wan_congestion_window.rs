// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WAN/Internet AIMD frame congestion-window controller & `"ACW1"` telemetry codec.
//!
//! Bounds in-flight unacknowledged frame bytes over high-RTT WAN/Internet links
//! (`min_cwnd..=max_cwnd`), transitioning smoothly from exponential slow start
//! (`cwnd < ssthresh`) to linear congestion avoidance (`cwnd >= ssthresh`) and
//! halving `cwnd` (`ssthresh = max(cwnd / 2, min_cwnd)`) on timeout / NACK loss.
//! Uses pure slice-pattern destructuring (`0` `runtime_checked`) and zero closures
//! (`0 mandated`), backed by Clean TLA+ island `Astream.Wire.TlaAimdCongestionWindow`.

#![allow(
    clippy::manual_checked_ops,
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
#[path = "wan_congestion_window_island.rs"]
mod wan_congestion_window_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn wan_cwnd_clamp(proposed_cwnd: u64, max_cwnd: u64) -> u64 {
    if proposed_cwnd < max_cwnd {
        proposed_cwnd
    } else {
        max_cwnd
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn wan_inflight_clamp(proposed_inflight: u64, cwnd: u64) -> u64 {
    if proposed_inflight < cwnd {
        proposed_inflight
    } else {
        cwnd
    }
}
#[cfg(clean_islands)]
pub use wan_congestion_window_island::{wan_cwnd_clamp, wan_inflight_clamp};

contract_fn! {
    /// Kernel-certified admission check that `proposed_inflight` fits within `cwnd`
    /// (`proposed_inflight <= cwnd`), linked via `clean-kernel-defeq` to
    /// `wan_can_send_isl`.
    #[must_use]
    pub const fn wan_can_send(proposed_inflight: u64, cwnd: u64) -> bool
    clauses [ensures result == (proposed_inflight <= cwnd)]
    {
        proposed_inflight <= cwnd
    }
}

/// Wire magic (`"ACW1"`) for 28-byte congestion-window telemetry frames.
pub const WAN_CWND_MAGIC: [u8; 4] = *b"ACW1";
/// Exact byte length of an `"ACW1"` snapshot (`magic(4) + in_flight(8) + cwnd(8) + ssthresh(8)`).
pub const WAN_CWND_WIRE_LEN: usize = 28;
/// Default minimum congestion window (`16 KiB`).
pub const DEFAULT_MIN_CWND_BYTES: u64 = 16 * 1024;
/// Default maximum congestion window (`16 MiB`).
pub const DEFAULT_MAX_CWND_BYTES: u64 = 16 * 1024 * 1024;

/// Decoded `"ACW1"` congestion-window snapshot.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WanCwndSnapshot {
    /// Unacknowledged bytes currently in flight (`<= cwnd`).
    pub in_flight: u64,
    /// Current congestion window ceiling in bytes (`<= max_cwnd`).
    pub cwnd: u64,
    /// Slow-start threshold in bytes.
    pub ssthresh: u64,
}

impl WanCwndSnapshot {
    /// Encode this snapshot into a 28-byte `"ACW1"` frame without slice indexing.
    #[must_use]
    pub const fn encode(&self) -> [u8; WAN_CWND_WIRE_LEN] {
        let [m0, m1, m2, m3] = WAN_CWND_MAGIC;
        let f = self.in_flight;
        let c = self.cwnd;
        let s = self.ssthresh;
        [
            m0,
            m1,
            m2,
            m3,
            f as u8,
            (f >> 8) as u8,
            (f >> 16) as u8,
            (f >> 24) as u8,
            (f >> 32) as u8,
            (f >> 40) as u8,
            (f >> 48) as u8,
            (f >> 56) as u8,
            c as u8,
            (c >> 8) as u8,
            (c >> 16) as u8,
            (c >> 24) as u8,
            (c >> 32) as u8,
            (c >> 40) as u8,
            (c >> 48) as u8,
            (c >> 56) as u8,
            s as u8,
            (s >> 8) as u8,
            (s >> 16) as u8,
            (s >> 24) as u8,
            (s >> 32) as u8,
            (s >> 40) as u8,
            (s >> 48) as u8,
            (s >> 56) as u8,
        ]
    }

    /// Decode a 28-byte `"ACW1"` frame via exact slice-pattern destructuring (`0` bounds checks).
    #[must_use]
    pub const fn decode(raw: &[u8]) -> Option<Self> {
        let &[m0, m1, m2, m3, f0, f1, f2, f3, f4, f5, f6, f7, c0, c1, c2, c3, c4, c5, c6, c7, s0, s1, s2, s3, s4, s5, s6, s7] =
            raw
        else {
            return None;
        };
        let [magic0, magic1, magic2, magic3] = WAN_CWND_MAGIC;
        if m0 != magic0 || m1 != magic1 || m2 != magic2 || m3 != magic3 {
            return None;
        }
        let in_flight = (f0 as u64)
            | ((f1 as u64) << 8)
            | ((f2 as u64) << 16)
            | ((f3 as u64) << 24)
            | ((f4 as u64) << 32)
            | ((f5 as u64) << 40)
            | ((f6 as u64) << 48)
            | ((f7 as u64) << 56);
        let cwnd = (c0 as u64)
            | ((c1 as u64) << 8)
            | ((c2 as u64) << 16)
            | ((c3 as u64) << 24)
            | ((c4 as u64) << 32)
            | ((c5 as u64) << 40)
            | ((c6 as u64) << 48)
            | ((c7 as u64) << 56);
        let ssthresh = (s0 as u64)
            | ((s1 as u64) << 8)
            | ((s2 as u64) << 16)
            | ((s3 as u64) << 24)
            | ((s4 as u64) << 32)
            | ((s5 as u64) << 40)
            | ((s6 as u64) << 48)
            | ((s7 as u64) << 56);
        if !wan_can_send(in_flight, cwnd) {
            return None;
        }
        Some(Self {
            in_flight,
            cwnd,
            ssthresh,
        })
    }
}

/// AIMD congestion-window controller for WAN/Internet frame pipelines.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WanFlightWindow {
    in_flight: u64,
    cwnd: u64,
    ssthresh: u64,
    min_cwnd: u64,
    max_cwnd: u64,
}

impl WanFlightWindow {
    /// Construct a [`WanFlightWindow`] with `(init_cwnd, min_cwnd, max_cwnd)` in bytes.
    #[must_use]
    pub const fn new(init_cwnd: u64, min_cwnd: u64, max_cwnd: u64) -> Self {
        let cap = if max_cwnd == 0 { 1 } else { max_cwnd };
        let floor = if min_cwnd == 0 {
            1
        } else if min_cwnd < cap {
            min_cwnd
        } else {
            cap
        };
        let raised_init = if init_cwnd < floor { floor } else { init_cwnd };
        let cwnd = wan_cwnd_clamp(raised_init, cap);
        Self {
            in_flight: 0,
            cwnd,
            ssthresh: cap,
            min_cwnd: floor,
            max_cwnd: cap,
        }
    }

    /// Current unacknowledged bytes in flight (`<= cwnd`).
    #[must_use]
    pub const fn in_flight(&self) -> u64 {
        self.in_flight
    }

    /// Current congestion window ceiling in bytes (`<= max_cwnd`).
    #[must_use]
    pub const fn cwnd(&self) -> u64 {
        self.cwnd
    }

    /// Slow-start threshold in bytes.
    #[must_use]
    pub const fn ssthresh(&self) -> u64 {
        self.ssthresh
    }

    /// Remaining send credit in bytes (`cwnd - in_flight`).
    #[must_use]
    pub const fn available_bytes(&self) -> u64 {
        self.cwnd.saturating_sub(self.in_flight)
    }

    /// Export a wire-serializable [`WanCwndSnapshot`].
    #[must_use]
    pub const fn snapshot(&self) -> WanCwndSnapshot {
        WanCwndSnapshot {
            in_flight: self.in_flight,
            cwnd: self.cwnd,
            ssthresh: self.ssthresh,
        }
    }

    /// Attempt to admit `frame_bytes` into flight, returning `true` on admission.
    pub fn try_send(&mut self, frame_bytes: u64) -> bool {
        let Some(proposed) = self.in_flight.checked_add(frame_bytes) else {
            return false;
        };
        if !wan_can_send(proposed, self.cwnd) {
            return false;
        }
        self.in_flight = wan_inflight_clamp(proposed, self.cwnd);
        true
    }

    /// Record acknowledgment of `acked_bytes`, growing `cwnd` via slow-start (`< ssthresh`)
    /// or additive congestion avoidance (`>= ssthresh`).
    pub fn on_ack(&mut self, acked_bytes: u64) {
        let rem = self.in_flight.saturating_sub(acked_bytes);
        let growth = if self.cwnd < self.ssthresh {
            acked_bytes
        } else {
            let num = acked_bytes.saturating_mul(self.min_cwnd);
            let denom = if self.cwnd > 1 { self.cwnd } else { 1 };
            let step = match num.checked_div(denom) {
                Some(v) => v,
                None => 0,
            };
            if step == 0 && acked_bytes > 0 {
                1
            } else {
                step
            }
        };
        let next_cwnd = wan_cwnd_clamp(self.cwnd.saturating_add(growth), self.max_cwnd);
        self.cwnd = next_cwnd;
        self.in_flight = wan_inflight_clamp(rem, self.cwnd);
    }

    /// Record a loss / RTO timeout event: halve `cwnd` down to at least `min_cwnd` and
    /// release `lost_bytes` from `in_flight`.
    pub fn on_loss(&mut self, lost_bytes: u64) {
        let half = self.cwnd >> 1;
        let halved = if half > self.min_cwnd {
            half
        } else {
            self.min_cwnd
        };
        let next_cwnd = wan_cwnd_clamp(halved, self.max_cwnd);
        self.ssthresh = next_cwnd;
        self.cwnd = next_cwnd;
        let rem = self.in_flight.saturating_sub(lost_bytes);
        self.in_flight = wan_inflight_clamp(rem, self.cwnd);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aimd_slow_start_loss_backoff_and_wire_snapshot_roundtrip() {
        let mut win = WanFlightWindow::new(4096, 2048, 32_768);
        assert!(win.try_send(3000));
        assert!(!win.try_send(2000), "exceeds 4096 initial cwnd");

        // Slow-start ACK grows cwnd by +3000 -> 7096!
        win.on_ack(3000);
        assert_eq!(win.in_flight(), 0);
        assert_eq!(win.cwnd(), 7096);

        // Loss halves cwnd -> 3548 (`ssthresh = 3548`).
        assert!(win.try_send(2000));
        win.on_loss(2000);
        assert_eq!(win.cwnd(), 3548);
        assert_eq!(win.ssthresh(), 3548);
        assert_eq!(win.in_flight(), 0);

        let snap = win.snapshot();
        assert_eq!(WanCwndSnapshot::decode(&snap.encode()), Some(snap));
    }
}
