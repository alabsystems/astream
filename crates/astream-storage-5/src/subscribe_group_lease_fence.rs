// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `SubscribeGroup` consumer lease fencing & in-flight dispatch window guard
//! (`Astream.Broker.TlaSubscribeGroupLeaseFence`).
//!
//! Prevents split-brain dual delivery across `SubscribeGroup` consumer churn: fences stale
//! consumer acks with a monotonically increasing `fencing_epoch`, enforces lease expiry before
//! takeover (`now_ms >= lease_expiry_ms`), and bounds unacknowledged dispatches to `max_inflight`.

#[cfg(clean_islands)]
#[path = "subscribe_group_lease_fence_island.rs"]
mod subscribe_group_lease_fence_island;
#[cfg(clean_islands)]
pub use subscribe_group_lease_fence_island::{group_inflight_clamp, group_lease_epoch_advance};

#[cfg(not(clean_islands))]
/// Clamp consumer-group unacknowledged in-flight count to `max_inflight`.
#[must_use]
pub const fn group_inflight_clamp(cand_inflight: u64, max_inflight: u64) -> u64 {
    if cand_inflight < max_inflight {
        cand_inflight
    } else {
        max_inflight
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the consumer-group lease fencing epoch.
#[must_use]
pub const fn group_lease_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff the group still has in-flight dispatch capacity below `max_inflight`.
    #[must_use]
    pub const fn group_can_dispatch(inflight: u64, max_inflight: u64) -> bool
    clauses [ensures result == (inflight < max_inflight)]
    {
        inflight < max_inflight
    }
}

/// Result of attempting a `SubscribeGroup` lease takeover or renewal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupLeaseOutcome {
    Granted { owner_id: u64, fencing_epoch: u64 },
    HeldByActiveOwner { owner_id: u64, lease_expiry_ms: u64 },
}

/// Stateful lease and in-flight fence for a `SubscribeGroup` queue cursor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubscribeGroupLeaseFence {
    owner_id: Option<u64>,
    fencing_epoch: u64,
    lease_expiry_ms: u64,
    lease_ttl_ms: u64,
    inflight: u64,
    max_inflight: u64,
    acked_offset: u64,
}

impl SubscribeGroupLeaseFence {
    #[must_use]
    pub const fn new(lease_ttl_ms: u64, max_inflight: u64) -> Self {
        let ttl = if lease_ttl_ms == 0 {
            5_000
        } else {
            lease_ttl_ms
        };
        let cap = if max_inflight == 0 { 64 } else { max_inflight };
        Self {
            owner_id: None,
            fencing_epoch: 0,
            lease_expiry_ms: 0,
            lease_ttl_ms: ttl,
            inflight: 0,
            max_inflight: cap,
            acked_offset: 0,
        }
    }

    #[must_use]
    pub const fn fencing_epoch(&self) -> u64 {
        self.fencing_epoch
    }

    #[must_use]
    pub const fn inflight(&self) -> u64 {
        self.inflight
    }

    #[must_use]
    pub const fn acked_offset(&self) -> u64 {
        self.acked_offset
    }

    /// Acquire or renew the group lease at `now_ms`. Takeover by a new member requires expiry.
    pub fn acquire_or_renew(&mut self, member_id: u64, now_ms: u64) -> GroupLeaseOutcome {
        match self.owner_id {
            Some(cur_owner) if cur_owner == member_id => {
                self.lease_expiry_ms = now_ms.saturating_add(self.lease_ttl_ms);
                GroupLeaseOutcome::Granted {
                    owner_id: cur_owner,
                    fencing_epoch: self.fencing_epoch,
                }
            }
            Some(cur_owner) if now_ms < self.lease_expiry_ms => {
                GroupLeaseOutcome::HeldByActiveOwner {
                    owner_id: cur_owner,
                    lease_expiry_ms: self.lease_expiry_ms,
                }
            }
            _ => {
                let next_ep = self.fencing_epoch.saturating_add(1);
                self.fencing_epoch = group_lease_epoch_advance(self.fencing_epoch, next_ep);
                self.owner_id = Some(member_id);
                self.lease_expiry_ms = now_ms.saturating_add(self.lease_ttl_ms);
                // Reclaim unacked in-flight window from the expired owner for redelivery from acked_offset:
                self.inflight = 0;
                GroupLeaseOutcome::Granted {
                    owner_id: member_id,
                    fencing_epoch: self.fencing_epoch,
                }
            }
        }
    }

    /// Reserve one in-flight dispatch slot for `(member_id, epoch)`.
    pub fn try_dispatch(&mut self, member_id: u64, epoch: u64) -> bool {
        if self.owner_id != Some(member_id) || epoch != self.fencing_epoch {
            return false;
        }
        if !group_can_dispatch(self.inflight, self.max_inflight) {
            return false;
        }
        let next = self.inflight.saturating_add(1);
        self.inflight = group_inflight_clamp(next, self.max_inflight);
        true
    }

    /// Commit an acknowledgment from the active lease holder (`epoch` must match `fencing_epoch`).
    pub fn ack(&mut self, member_id: u64, epoch: u64, offset: u64) -> bool {
        if self.owner_id != Some(member_id) || epoch != self.fencing_epoch {
            return false;
        }
        self.inflight = self.inflight.saturating_sub(1);
        if offset > self.acked_offset {
            self.acked_offset = offset;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fences_stale_owner_acks_after_lease_expiry_takeover() {
        let mut fence = SubscribeGroupLeaseFence::new(100, 2);
        assert_eq!(
            fence.acquire_or_renew(1, 1_000),
            GroupLeaseOutcome::Granted {
                owner_id: 1,
                fencing_epoch: 1,
            }
        );
        assert!(fence.try_dispatch(1, 1));
        // Before 1_100ms, member 2 cannot steal the lease:
        assert_eq!(
            fence.acquire_or_renew(2, 1_050),
            GroupLeaseOutcome::HeldByActiveOwner {
                owner_id: 1,
                lease_expiry_ms: 1_100,
            }
        );
        // At 1_100ms, member 2 takes over at epoch 2 and resets stale in-flight:
        assert_eq!(
            fence.acquire_or_renew(2, 1_100),
            GroupLeaseOutcome::Granted {
                owner_id: 2,
                fencing_epoch: 2,
            }
        );
        // Zombie ack from member 1 @ epoch 1 is fenced off:
        assert!(!fence.ack(1, 1, 50));
        assert!(fence.try_dispatch(2, 2));
        assert!(fence.ack(2, 2, 50));
        assert_eq!(fence.acked_offset(), 50);
    }
}
