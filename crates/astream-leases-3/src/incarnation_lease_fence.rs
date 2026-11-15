// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Boot-scoped endpoint incarnation lease tracker (`Astream.Broker.TlaIncarnationLease`,
//! `aterm-link` boot-session incarnation fencing).
//!
//! Coordinates `(boot_id, incarnation_slot)` leases per endpoint principal so a restarted
//! `aterm-link` daemon within the same OS boot monotonically advances its [`INC_MAX`]-bounded
//! incarnation slot (fencing stale lower-slot sockets from the crashed process), while an OS
//! reboot (`boot_id != active_boot`) cleanly resets the per-boot slot counter to `0` after
//! fencing any lingering pre-reboot lease.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

/// Highest 31-bit incarnation index (`(1 << 31) - 1`).
pub const INC_MAX: u64 = (1u64 << 31) - 1;

#[inline]
const fn incarnation_base(inc: u64) -> Option<u64> {
    if inc <= INC_MAX {
        Some(inc << 32)
    } else {
        None
    }
}
use std::collections::HashMap;

#[cfg(clean_islands)]
#[path = "incarnation_lease_fence_island.rs"]
mod incarnation_lease_fence_island;
#[cfg(clean_islands)]
pub use incarnation_lease_fence_island::{incarnation_slot_advance, incarnation_slot_clamp};

/// Mirror of Clean's `incarnation_slot_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn incarnation_slot_advance(cur_slot: u64, next_slot: u64) -> u64 {
    if cur_slot < next_slot {
        next_slot
    } else {
        cur_slot
    }
}

/// Mirror of Clean's `incarnation_slot_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn incarnation_slot_clamp(cand_slot: u64, inc_max: u64) -> u64 {
    if cand_slot < inc_max {
        cand_slot
    } else {
        inc_max
    }
}

contract_fn! {
    /// Kernel-certified check that `slot` lies within `[0, inc_max]` (`slot <= inc_max`),
    /// linked via `clean-kernel-defeq` to `incarnation_within_cap_isl`.
    #[must_use]
    pub const fn incarnation_within_cap(slot: u64, inc_max: u64) -> bool
    clauses [ensures result == (slot <= inc_max)]
    {
        slot <= inc_max
    }
}

/// Maximum distinct endpoint principals tracked in one [`IncarnationLeaseTracker`].
pub const MAX_INCARNATION_PRINCIPALS: usize = 4096;

/// Active boot-scoped lease record for one endpoint principal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EndpointIncarnationLease {
    /// 16-byte kernel boot session UUID (`astream_sys::boot_session`).
    pub boot_id: [u8; 16],
    /// Monotone incarnation slot within `boot_id` (`0..=INC_MAX`).
    pub slot: u64,
    /// Derived `producer_seq` base (`incarnation_base(slot)`) for this incarnation.
    pub seq_base: u64,
}

/// Outcome of claiming or validating an `(endpoint, boot_id, slot)` lease.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncarnationVerdict {
    /// Lease acquired or renewed; returns the active [`EndpointIncarnationLease`].
    Admitted(EndpointIncarnationLease),
    /// Refused: `slot` is strictly lower than the active slot within the same `boot_id`.
    FencedStaleSlot { active_slot: u64, offered_slot: u64 },
    /// Refused: `slot > INC_MAX` would overflow the producer sequence incarnation space.
    SlotExhausted { offered_slot: u64, max_slot: u64 },
    /// Refused: tracker table reached [`MAX_INCARNATION_PRINCIPALS`].
    CapacityReached,
}

/// Bounded per-principal `(boot_id, slot)` lease table.
#[derive(Debug, Clone, Default)]
pub struct IncarnationLeaseTracker {
    leases: HashMap<String, EndpointIncarnationLease>,
}

impl IncarnationLeaseTracker {
    /// Construct an empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            leases: HashMap::new(),
        }
    }

    /// Number of tracked endpoint principals.
    #[must_use]
    pub fn len(&self) -> usize {
        self.leases.len()
    }

    /// Whether zero principals are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.leases.is_empty()
    }

    /// Look up the current lease for `principal`.
    #[must_use]
    #[allow(clippy::manual_map)]
    pub fn get(&self, principal: &str) -> Option<EndpointIncarnationLease> {
        match self.leases.get(principal) {
            Some(&v) => Some(v),
            None => None,
        }
    }

    /// Claim or advance `(boot_id, offered_slot)` for `principal`.
    ///
    /// - Within the same `boot_id`, `offered_slot < active.slot` is fenced via
    ///   [`IncarnationVerdict::FencedStaleSlot`], while `offered_slot >= active.slot`
    ///   advances monotonically via [`incarnation_slot_advance`].
    /// - Across a new `boot_id != active.boot_id`, the new boot replaces the old boot's
    ///   lease starting at `clamped_slot`.
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn claim(
        &mut self,
        principal: &str,
        boot_id: [u8; 16],
        offered_slot: u64,
    ) -> IncarnationVerdict {
        if !incarnation_within_cap(offered_slot, INC_MAX) {
            return IncarnationVerdict::SlotExhausted {
                offered_slot,
                max_slot: INC_MAX,
            };
        }
        if let Some(existing) = self.leases.get_mut(principal) {
            if existing.boot_id == boot_id {
                if offered_slot < existing.slot {
                    return IncarnationVerdict::FencedStaleSlot {
                        active_slot: existing.slot,
                        offered_slot,
                    };
                }
                let next_slot = incarnation_slot_clamp(
                    incarnation_slot_advance(existing.slot, offered_slot),
                    INC_MAX,
                );
                let seq_base = match incarnation_base(next_slot) {
                    Some(v) => v,
                    None => existing.seq_base,
                };
                existing.slot = next_slot;
                existing.seq_base = seq_base;
                return IncarnationVerdict::Admitted(*existing);
            }
            let reset_slot = incarnation_slot_clamp(offered_slot, INC_MAX);
            let seq_base = match incarnation_base(reset_slot) {
                Some(v) => v,
                None => 0,
            };
            *existing = EndpointIncarnationLease {
                boot_id,
                slot: reset_slot,
                seq_base,
            };
            return IncarnationVerdict::Admitted(*existing);
        }

        if self.leases.len() >= MAX_INCARNATION_PRINCIPALS {
            return IncarnationVerdict::CapacityReached;
        }
        let slot = incarnation_slot_clamp(offered_slot, INC_MAX);
        let seq_base = match incarnation_base(slot) {
            Some(v) => v,
            None => 0,
        };
        let lease = EndpointIncarnationLease {
            boot_id,
            slot,
            seq_base,
        };
        let mut owned_principal = String::new();
        owned_principal.push_str(principal);
        self.leases.insert(owned_principal, lease);
        IncarnationVerdict::Admitted(lease)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fences_stale_slot_in_same_boot_and_resets_across_os_reboot() {
        let mut tracker = IncarnationLeaseTracker::new();
        let boot_a = [0x11; 16];
        let boot_b = [0x22; 16];

        let IncarnationVerdict::Admitted(l1) = tracker.claim("n-alpha", boot_a, 2) else {
            panic!("expected admit");
        };
        assert_eq!(l1.slot, 2);

        assert_eq!(
            tracker.claim("n-alpha", boot_a, 1),
            IncarnationVerdict::FencedStaleSlot {
                active_slot: 2,
                offered_slot: 1,
            }
        );

        let IncarnationVerdict::Admitted(l2) = tracker.claim("n-alpha", boot_a, 3) else {
            panic!("expected advance");
        };
        assert_eq!(l2.slot, 3);
        assert!(l2.seq_base > l1.seq_base);

        // Reboot into boot_b resets slot cleanly to 0.
        let IncarnationVerdict::Admitted(l3) = tracker.claim("n-alpha", boot_b, 0) else {
            panic!("expected reboot reset");
        };
        assert_eq!(l3.boot_id, boot_b);
        assert_eq!(l3.slot, 0);
    }
}
