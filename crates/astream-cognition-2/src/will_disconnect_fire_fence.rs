// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! At-most-once `/a/will` disconnect firing & graceful-clear fence
//! (`Astream.Broker.TlaWillDisconnectFireFence`).
//!
//! Ensures `astream-broker` fires a connection's registered `/a/will` record at most once upon
//! abrupt disconnect, suppresses firing when explicitly cleared before close, and bounds live
//! registered wills per connection.

#[cfg(clean_islands)]
#[path = "will_disconnect_fire_fence_island.rs"]
mod will_disconnect_fire_fence_island;
#[cfg(clean_islands)]
pub use will_disconnect_fire_fence_island::{
    will_fire_epoch_advance_b111, will_pending_clamp_b111,
};

#[cfg(not(clean_islands))]
/// Clamp active pending wills for a connection to `max_wills`.
#[must_use]
pub const fn will_pending_clamp_b111(cand_pending: u64, max_wills: u64) -> u64 {
    if cand_pending < max_wills {
        cand_pending
    } else {
        max_wills
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the will registration / firing epoch.
#[must_use]
pub const fn will_fire_epoch_advance_b111(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `pending_wills` has room to register another will below `max_wills`.
    #[must_use]
    pub const fn will_can_register_b111(pending_wills: u64, max_wills: u64) -> bool
    clauses [ensures result == (pending_wills < max_wills)]
    {
        pending_wills < max_wills
    }
}

/// Outcome when a connection closes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WillDisconnectAction {
    FireWills { count: u64, fire_epoch: u64 },
    SuppressedGracefulOrEmpty { fire_epoch: u64 },
    AlreadyFiredAtMostOnce { fire_epoch: u64 },
}

/// Per-connection `/a/will` lifecycle fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WillDisconnectFireFence {
    max_wills: u64,
    pending_wills: u64,
    fired: bool,
    fire_epoch: u64,
}

impl WillDisconnectFireFence {
    #[must_use]
    pub const fn new(max_wills: u64) -> Self {
        let cap = if max_wills == 0 { 4 } else { max_wills };
        Self {
            max_wills: cap,
            pending_wills: 0,
            fired: false,
            fire_epoch: 0,
        }
    }

    #[must_use]
    pub const fn pending_wills(&self) -> u64 {
        self.pending_wills
    }

    /// Register a new `/a/will` payload on an active connection.
    pub fn register_will(&mut self) -> bool {
        if self.fired || !will_can_register_b111(self.pending_wills, self.max_wills) {
            return false;
        }
        let cand = self.pending_wills.saturating_add(1);
        self.pending_wills = will_pending_clamp_b111(cand, self.max_wills);
        let next_ep = self.fire_epoch.saturating_add(1);
        self.fire_epoch = will_fire_epoch_advance_b111(self.fire_epoch, next_ep);
        true
    }

    /// Explicitly disarm pending wills before a clean shutdown.
    pub fn clear_wills(&mut self) {
        self.pending_wills = 0;
        let next_ep = self.fire_epoch.saturating_add(1);
        self.fire_epoch = will_fire_epoch_advance_b111(self.fire_epoch, next_ep);
    }

    /// Handle connection close (`graceful == true` suppresses firing).
    pub fn on_disconnect(&mut self, graceful: bool) -> WillDisconnectAction {
        if self.fired {
            return WillDisconnectAction::AlreadyFiredAtMostOnce {
                fire_epoch: self.fire_epoch,
            };
        }
        let next_ep = self.fire_epoch.saturating_add(1);
        self.fire_epoch = will_fire_epoch_advance_b111(self.fire_epoch, next_ep);
        if graceful || self.pending_wills == 0 {
            self.pending_wills = 0;
            WillDisconnectAction::SuppressedGracefulOrEmpty {
                fire_epoch: self.fire_epoch,
            }
        } else {
            let count = self.pending_wills;
            self.pending_wills = 0;
            self.fired = true;
            WillDisconnectAction::FireWills {
                count,
                fire_epoch: self.fire_epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fires_at_most_once_on_abrupt_drop_and_never_twice() {
        let mut f = WillDisconnectFireFence::new(2);
        assert!(f.register_will());
        assert_eq!(
            f.on_disconnect(false),
            WillDisconnectAction::FireWills {
                count: 1,
                fire_epoch: 2,
            }
        );
        assert_eq!(
            f.on_disconnect(false),
            WillDisconnectAction::AlreadyFiredAtMostOnce { fire_epoch: 2 }
        );
    }
}
