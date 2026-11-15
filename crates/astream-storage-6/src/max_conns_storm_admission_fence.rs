// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Reserved-slot `MAX_CONNS` reconnect-storm admission fence
//! (`Astream.Broker.TlaMaxConnsStormAdmissionFence`).
//!
//! Protects `astream-broker` (`MAX_CONNS`) during WAN/LAN reconnect storms: reserves
//! `reserved_priority_slots` exclusively for authenticated replication/control peers so
//! unauthenticated socket floods can never starve quorum replication or operator `ctl` access.

#[cfg(clean_islands)]
#[path = "max_conns_storm_admission_fence_island.rs"]
mod max_conns_storm_admission_fence_island;
#[cfg(clean_islands)]
pub use max_conns_storm_admission_fence_island::{
    admission_epoch_advance_b108, conns_active_clamp_b108,
};

#[cfg(not(clean_islands))]
/// Clamp active broker connection count to `max_conns`.
#[must_use]
pub const fn conns_active_clamp_b108(cand_active: u64, max_conns: u64) -> u64 {
    if cand_active < max_conns {
        cand_active
    } else {
        max_conns
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the connection admission epoch.
#[must_use]
pub const fn admission_epoch_advance_b108(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `active_conns` is strictly below `tier_ceiling`.
    #[must_use]
    pub const fn conn_tier_has_room_b108(active_conns: u64, tier_ceiling: u64) -> bool
    clauses [ensures result == (active_conns < tier_ceiling)]
    {
        active_conns < tier_ceiling
    }
}

/// Connection admission priority class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnAdmissionClass {
    GeneralClient,
    PriorityReplicaOrControl,
}

/// Admission verdict for an incoming TCP/UDS accept.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StormAdmissionVerdict {
    Admitted {
        active_conns: u64,
        admission_epoch: u64,
    },
    RejectedGeneralPoolFull {
        active_conns: u64,
        general_ceiling: u64,
    },
    RejectedMaxConnsFull {
        max_conns: u64,
    },
}

/// Two-tier `MAX_CONNS` admission controller with priority reservation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaxConnsStormAdmissionFence {
    max_conns: u64,
    reserved_priority_slots: u64,
    active_conns: u64,
    admission_epoch: u64,
}

impl MaxConnsStormAdmissionFence {
    #[must_use]
    pub const fn new(max_conns: u64, reserved_priority_slots: u64) -> Self {
        let total = if max_conns < 4 { 64 } else { max_conns };
        let res = if reserved_priority_slots >= total {
            total / 4
        } else {
            reserved_priority_slots
        };
        Self {
            max_conns: total,
            reserved_priority_slots: res,
            active_conns: 0,
            admission_epoch: 0,
        }
    }

    #[must_use]
    pub const fn active_conns(&self) -> u64 {
        self.active_conns
    }

    #[must_use]
    pub const fn general_ceiling(&self) -> u64 {
        self.max_conns.saturating_sub(self.reserved_priority_slots)
    }

    /// Attempt to admit a newly accepted connection in `class`.
    pub fn try_admit(&mut self, class: ConnAdmissionClass) -> StormAdmissionVerdict {
        let next_ep = self.admission_epoch.saturating_add(1);
        self.admission_epoch = admission_epoch_advance_b108(self.admission_epoch, next_ep);
        match class {
            ConnAdmissionClass::GeneralClient => {
                let ceiling = self.general_ceiling();
                if !conn_tier_has_room_b108(self.active_conns, ceiling) {
                    return StormAdmissionVerdict::RejectedGeneralPoolFull {
                        active_conns: self.active_conns,
                        general_ceiling: ceiling,
                    };
                }
            }
            ConnAdmissionClass::PriorityReplicaOrControl => {
                if !conn_tier_has_room_b108(self.active_conns, self.max_conns) {
                    return StormAdmissionVerdict::RejectedMaxConnsFull {
                        max_conns: self.max_conns,
                    };
                }
            }
        }
        let next_act = self.active_conns.saturating_add(1);
        self.active_conns = conns_active_clamp_b108(next_act, self.max_conns);
        StormAdmissionVerdict::Admitted {
            active_conns: self.active_conns,
            admission_epoch: self.admission_epoch,
        }
    }

    /// Release one slot on connection close.
    pub fn on_close(&mut self) {
        self.active_conns = self.active_conns.saturating_sub(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reserves_priority_slots_during_general_reconnect_storm() {
        let mut fence = MaxConnsStormAdmissionFence::new(4, 1);
        for _ in 0..3 {
            assert!(matches!(
                fence.try_admit(ConnAdmissionClass::GeneralClient),
                StormAdmissionVerdict::Admitted { .. }
            ));
        }
        // 4th general client is shed to protect the reserved slot:
        assert_eq!(
            fence.try_admit(ConnAdmissionClass::GeneralClient),
            StormAdmissionVerdict::RejectedGeneralPoolFull {
                active_conns: 3,
                general_ceiling: 3,
            }
        );
        // Priority replica/control connection still succeeds!
        assert!(matches!(
            fence.try_admit(ConnAdmissionClass::PriorityReplicaOrControl),
            StormAdmissionVerdict::Admitted {
                active_conns: 4,
                ..
            }
        ));
    }
}
