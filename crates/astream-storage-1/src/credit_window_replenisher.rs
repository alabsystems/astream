// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack half-window `GrantCredit` batch replenisher
//! (`Astream.Wire.TlaCreditWindowReplenisher`).
//!
//! Avoids per-frame credit-ACK chatter over WAN `Subscription` links: accumulates
//! consumed credits locally and emits a batched replenishment grant only once
//! consumed credits reach `(window_max + 1) / 2`, keeping `in_flight <= window_max`
//! with **zero heap allocations**.

#![allow(clippy::result_unit_err)]

#[cfg(clean_islands)]
#[path = "credit_window_replenisher_island.rs"]
mod credit_window_replenisher_island;
#[cfg(clean_islands)]
pub use credit_window_replenisher_island::{credit_granted_advance, credit_inflight_clamp};

/// Default subscription credit window (`256` records).
pub const DEFAULT_CREDIT_WINDOW_MAX: u64 = 256;

#[cfg(not(clean_islands))]
/// Monotonically advance cumulative credits granted to the sender.
#[must_use]
pub const fn credit_granted_advance(cur_granted: u64, cand_granted: u64) -> u64 {
    if cur_granted < cand_granted {
        cand_granted
    } else {
        cur_granted
    }
}

#[cfg(not(clean_islands))]
/// Clamp outstanding sender credit balance to `window_max`.
#[must_use]
pub const fn credit_inflight_clamp(cand_inflight: u64, window_max: u64) -> u64 {
    if cand_inflight < window_max {
        cand_inflight
    } else {
        window_max
    }
}

contract_fn! {
    /// True iff `consumed_since_grant >= low_threshold`.
    #[must_use]
    pub const fn credit_replenish_due(low_threshold: u64, consumed_since_grant: u64) -> bool
    clauses [ensures result == (low_threshold <= consumed_since_grant)]
    {
        low_threshold <= consumed_since_grant
    }
}

/// Pure stack receiver flow-control credit tracker.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CreditWindowReplenisher {
    window_max: u64,
    in_flight: u64,
    consumed_unreplenished: u64,
    total_granted: u64,
}

impl Default for CreditWindowReplenisher {
    fn default() -> Self {
        Self::new(DEFAULT_CREDIT_WINDOW_MAX)
    }
}

impl CreditWindowReplenisher {
    #[must_use]
    pub const fn new(window_max: u64) -> Self {
        let cap = if window_max < 2 { 2 } else { window_max };
        Self {
            window_max: cap,
            in_flight: cap,
            consumed_unreplenished: 0,
            total_granted: cap,
        }
    }

    #[must_use]
    pub const fn in_flight(&self) -> u64 {
        self.in_flight
    }

    #[must_use]
    pub const fn total_granted(&self) -> u64 {
        self.total_granted
    }

    /// Account for `n` delivered records; returns `Some(grant_delta)` when half-window replenishment is due,
    /// or `Err(())` if the peer violated flow control (`n > in_flight`).
    pub fn on_delivered(&mut self, n: u64) -> Result<Option<u64>, ()> {
        if n > self.in_flight {
            return Err(());
        }
        self.in_flight = self.in_flight.saturating_sub(n);
        self.consumed_unreplenished = self.consumed_unreplenished.saturating_add(n);

        let threshold = self.window_max.saturating_add(1) >> 1;
        if credit_replenish_due(threshold, self.consumed_unreplenished) {
            let grant = self.consumed_unreplenished;
            self.consumed_unreplenished = 0;
            let cand_inf = self.in_flight.saturating_add(grant);
            self.in_flight = credit_inflight_clamp(cand_inf, self.window_max);
            let cand_gr = self.total_granted.saturating_add(grant);
            self.total_granted = credit_granted_advance(self.total_granted, cand_gr);
            Ok(Some(grant))
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batches_credit_grants_at_half_window_and_rejects_overrun() {
        let mut rw = CreditWindowReplenisher::new(10);
        assert_eq!(rw.in_flight(), 10);
        // Delivering 4 (< 5) holds off sending GrantCredit
        assert_eq!(rw.on_delivered(4), Ok(None));
        assert_eq!(rw.in_flight(), 6);

        // Delivering 1 more reaches 5 (>= 10/2) -> grants 5 back to full window 10!
        assert_eq!(rw.on_delivered(1), Ok(Some(5)));
        assert_eq!(rw.in_flight(), 10);
        assert_eq!(rw.total_granted(), 15);

        // Peer overrun (> 10) is rejected!
        assert_eq!(rw.on_delivered(11), Err(()));
    }
}
