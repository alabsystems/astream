// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Nine-kind fabric wake priority lattice, sender/relay demotion, & control-exemption guard
//! (`evidence/manifest.toml` `wire.wake-and-control-acks`;
//! `Astream.Wire.TlaWakePriorityRelayedDemotionGuard`).
//!
//! Enforces `aterm`'s 9-kind wake algebra (`0 = note .. 8 = control`):
//! - Relayed (`has_via`), stray-reply, or unlisted `task`/`control` messages demote immediately
//!   to silent `note` (`rank = 0`),
//! - Within a pending delivery batch, `batch_max_rank` coalesces monotonically via `max` so at
//!   most ONE wake fires per batch,
//! - Accepted `control` directives (`rank == 8`) bypass the sliding-window wake budget, while
//!   `1..=7` wakes require `window_used < window_budget`!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "wake_priority_relayed_demotion_guard_island.rs"]
mod wake_priority_relayed_demotion_guard_island;
#[cfg(clean_islands)]
pub use wake_priority_relayed_demotion_guard_island::{
    wake_batch_rank_advance_b156, wake_rank_cap_clamp_b156,
};

/// Silent `note` rank (`0`).
pub const WAKE_RANK_NOTE: u64 = 0;
/// Highest `control` directive rank (`8`), exempt from sliding-window throttling.
pub const WAKE_RANK_CONTROL: u64 = 8;

#[cfg(not(clean_islands))]
/// Clamp wake rank to `WAKE_RANK_CONTROL` (`8`).
#[must_use]
pub const fn wake_rank_cap_clamp_b156(cand_rank: u64, max_rank: u64) -> u64 {
    if cand_rank < max_rank {
        cand_rank
    } else {
        max_rank
    }
}

#[cfg(not(clean_islands))]
/// Coalesce highest pending wake rank within a batch monotonically (`max`).
#[must_use]
pub const fn wake_batch_rank_advance_b156(cur_rank: u64, cand_rank: u64) -> u64 {
    if cur_rank < cand_rank {
        cand_rank
    } else {
        cur_rank
    }
}

contract_fn! {
    /// True iff `batch_rank > 0` AND either `batch_rank == 8` (`control` exemption) or `used < budget`.
    #[must_use]
    pub const fn coalesced_wake_fires_b156(
        batch_rank: u64,
        control_rank: u64,
        window_used: u64,
        window_budget: u64,
    ) -> bool
    clauses [ensures result == (batch_rank > 0 && (batch_rank == control_rank || window_used < window_budget))]
    {
        batch_rank > 0 && (batch_rank == control_rank || window_used < window_budget)
    }
}

/// Decision when observing deliveries and flushing a coalesced batch wake.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WakeDemotionDecision {
    DemotedToSilentNote {
        batch_max_rank: u64,
    },
    CoalescedIntoBatch {
        effective_rank: u64,
        batch_max_rank: u64,
    },
    FiredExemptControlWake,
    FiredBudgetedWake {
        fired_rank: u64,
        new_window_used: u64,
    },
    SuppressedSilentNoteBatch,
    ThrottledByWindowBudget {
        deferred_rank: u64,
    },
}

/// Zero-allocation per-recipient batch wake coalescer with demotion & control exemption.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WakeCoalesceGuard {
    batch_max_rank: u64,
    window_used: u64,
    window_budget: u64,
}

impl WakeCoalesceGuard {
    #[must_use]
    pub const fn new(window_budget: u64) -> Self {
        Self {
            batch_max_rank: 0,
            window_used: 0,
            window_budget,
        }
    }

    /// Observe one delivery (`raw_rank` in `0..=8`) and apply sender/relay demotion rules.
    pub fn observe_delivery(
        &mut self,
        raw_rank: u64,
        has_via_header: bool,
        is_stray_reply: bool,
        unlisted_directive_sender: bool,
    ) -> WakeDemotionDecision {
        let clamped = wake_rank_cap_clamp_b156(raw_rank, WAKE_RANK_CONTROL);
        let must_demote =
            has_via_header || is_stray_reply || (unlisted_directive_sender && clamped >= 6);
        if must_demote {
            return WakeDemotionDecision::DemotedToSilentNote {
                batch_max_rank: self.batch_max_rank,
            };
        }
        self.batch_max_rank = wake_batch_rank_advance_b156(self.batch_max_rank, clamped);
        WakeDemotionDecision::CoalescedIntoBatch {
            effective_rank: clamped,
            batch_max_rank: self.batch_max_rank,
        }
    }

    /// Emit at most one coalesced wake for the pending batch and reset `batch_max_rank`.
    pub fn flush_batch_wake(&mut self) -> WakeDemotionDecision {
        let rank = self.batch_max_rank;
        self.batch_max_rank = WAKE_RANK_NOTE;
        if rank == WAKE_RANK_NOTE {
            return WakeDemotionDecision::SuppressedSilentNoteBatch;
        }
        if coalesced_wake_fires_b156(
            rank,
            WAKE_RANK_CONTROL,
            self.window_used,
            self.window_budget,
        ) {
            if rank == WAKE_RANK_CONTROL {
                WakeDemotionDecision::FiredExemptControlWake
            } else {
                self.window_used = self.window_used.saturating_add(1);
                WakeDemotionDecision::FiredBudgetedWake {
                    fired_rank: rank,
                    new_window_used: self.window_used,
                }
            }
        } else {
            WakeDemotionDecision::ThrottledByWindowBudget {
                deferred_rank: rank,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demotes_relayed_and_unlisted_directives_and_exempts_accepted_control_from_budget() {
        let mut g = WakeCoalesceGuard::new(1);
        // Relayed `control` (`via=`) demotes to `note`!
        assert_eq!(
            g.observe_delivery(WAKE_RANK_CONTROL, true, false, false),
            WakeDemotionDecision::DemotedToSilentNote { batch_max_rank: 0 }
        );
        assert_eq!(
            g.flush_batch_wake(),
            WakeDemotionDecision::SuppressedSilentNoteBatch
        );
        // Spend the 1-wake budget on an `ask` (`rank = 7`):
        g.observe_delivery(7, false, false, false);
        assert_eq!(
            g.flush_batch_wake(),
            WakeDemotionDecision::FiredBudgetedWake {
                fired_rank: 7,
                new_window_used: 1,
            }
        );
        // Accepted `control` (`rank = 8`) STILL fires despite spent window budget!
        g.observe_delivery(WAKE_RANK_CONTROL, false, false, false);
        assert_eq!(
            g.flush_batch_wake(),
            WakeDemotionDecision::FiredExemptControlWake
        );
    }
}
