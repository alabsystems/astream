// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Power-loss barrier epoch prefix law (`P1`–`P8`) & lost-acked-record generation move guard
//! (`evidence/manifest.toml` `broker.crash-sim.prefix-law`;
//! `Astream.Broker.TlaCrashSimBarrierEpochPrefixLawGuard`).
//!
//! Enforces the `broker.crash-sim.prefix-law` invariants (`P2`, `P3`, `P3e`, `P4`, `P5`):
//! - Every `full_flush` promotes `durable_head` monotonically, and NO power-loss recovery may
//!   drop any record `< durable_head` (`P3`) or any acked escalated record (`P3e`),
//! - Every `Strict` or `Ordered` recovery cuts strictly at a batch boundary (`P2`,
//!   `recovered_head <= pre_crash_written_head`),
//! - Whenever a power-loss recovery loses an acked record (`recovered_head < pre_crash_acked_head`),
//!   the log MUST move its generation (`generation_moved == true`, `P4`); after a `close_clean`,
//!   nothing is lost or moved (`P5`)!

#[cfg(clean_islands)]
#[path = "crash_sim_barrier_epoch_prefix_law_guard_island.rs"]
mod crash_sim_barrier_epoch_prefix_law_guard_island;
#[cfg(clean_islands)]
pub use crash_sim_barrier_epoch_prefix_law_guard_island::{
    durable_floor_advance_b156, recovered_prefix_clamp_b156,
};

#[cfg(not(clean_islands))]
/// Clamp `recovered_head` to `pre_crash_written_head` (`P2`: prefix of what was written).
#[must_use]
pub const fn recovered_prefix_clamp_b156(cand_recovered: u64, written_head: u64) -> u64 {
    if cand_recovered < written_head {
        cand_recovered
    } else {
        written_head
    }
}

#[cfg(not(clean_islands))]
/// Advance `durable_floor` monotonically across full flushes (`P3`).
#[must_use]
pub const fn durable_floor_advance_b156(cur_durable: u64, cand_durable: u64) -> u64 {
    if cur_durable < cand_durable {
        cand_durable
    } else {
        cur_durable
    }
}

contract_fn! {
    /// True iff `P3` (`durable_floor <= recovered`), `P2` (`recovered <= written`), and `P4`
    /// (`recovered < acked => generation_moved`) all hold!
    #[must_use]
    pub const fn crash_recovery_satisfies_p2_p3_p4_b156(
        durable_floor: u64,
        recovered_head: u64,
        acked_head: u64,
        written_head: u64,
        generation_moved: bool,
    ) -> bool
    clauses [ensures result == (durable_floor <= recovered_head && recovered_head <= written_head && (acked_head <= recovered_head || generation_moved))]
    {
        durable_floor <= recovered_head
            && recovered_head <= written_head
            && (acked_head <= recovered_head || generation_moved)
    }
}

/// Verdict of checking a power-loss recovery against `P2`, `P3`, `P3e`, `P4`, and `P5`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrefixLawAuditDecision {
    VerifiedPrefixLaw {
        recovered_head: u64,
        lost_acked_records: bool,
        generation_moved: bool,
    },
    ViolatedP3LostDurableOrEscalatedRecord {
        durable_floor: u64,
        recovered_head: u64,
    },
    ViolatedP2NotBatchBoundaryOrPastWritten,
    ViolatedP4LostAckedWithoutGenerationMove {
        acked_head: u64,
        recovered_head: u64,
    },
    ViolatedP5MovedOrLostAfterCleanClose,
}

/// Oracle checking `P2`–`P5` across simulated power-loss recoveries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrefixLawAuditOracle {
    durable_floor: u64,
    acked_head: u64,
    written_head: u64,
    closed_clean: bool,
}

impl PrefixLawAuditOracle {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            durable_floor: 0,
            acked_head: 0,
            written_head: 0,
            closed_clean: false,
        }
    }

    pub fn record_barrier_batch(&mut self, written: u64, acked_now: u64, escalated_acked: u64) {
        if written > self.written_head {
            self.written_head = written;
        }
        if acked_now > self.acked_head {
            self.acked_head = acked_now;
        }
        self.durable_floor = durable_floor_advance_b156(self.durable_floor, escalated_acked);
    }

    pub fn record_full_flush(&mut self) {
        self.durable_floor = durable_floor_advance_b156(self.durable_floor, self.written_head);
        self.acked_head = self.written_head;
    }

    pub fn record_clean_close(&mut self) {
        self.record_full_flush();
        self.closed_clean = true;
    }

    /// Audit a recovered open (`recovered_head`, `at_batch_boundary`, `generation_moved`).
    #[must_use]
    pub const fn audit_recovery(
        &self,
        recovered_head: u64,
        at_batch_boundary: bool,
        generation_moved: bool,
    ) -> PrefixLawAuditDecision {
        if !at_batch_boundary || recovered_head > self.written_head {
            return PrefixLawAuditDecision::ViolatedP2NotBatchBoundaryOrPastWritten;
        }
        if recovered_head < self.durable_floor {
            return PrefixLawAuditDecision::ViolatedP3LostDurableOrEscalatedRecord {
                durable_floor: self.durable_floor,
                recovered_head,
            };
        }
        if self.closed_clean && (recovered_head != self.written_head || generation_moved) {
            return PrefixLawAuditDecision::ViolatedP5MovedOrLostAfterCleanClose;
        }
        let clamped_rec = recovered_prefix_clamp_b156(recovered_head, self.written_head);
        if !crash_recovery_satisfies_p2_p3_p4_b156(
            self.durable_floor,
            clamped_rec,
            self.acked_head,
            self.written_head,
            generation_moved,
        ) {
            return PrefixLawAuditDecision::ViolatedP4LostAckedWithoutGenerationMove {
                acked_head: self.acked_head,
                recovered_head: clamped_rec,
            };
        }
        PrefixLawAuditDecision::VerifiedPrefixLaw {
            recovered_head: clamped_rec,
            lost_acked_records: clamped_rec < self.acked_head,
            generation_moved,
        }
    }
}

impl Default for PrefixLawAuditOracle {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_p2_batch_prefix_p3_durable_floor_and_p4_generation_move_on_ordered_loss() {
        let mut o = PrefixLawAuditOracle::new();
        o.record_barrier_batch(3, 3, 0);
        o.record_full_flush();
        o.record_barrier_batch(6, 6, 0);

        // Losing durable record (< 3) violates P3!
        assert_eq!(
            o.audit_recovery(2, true, true),
            PrefixLawAuditDecision::ViolatedP3LostDurableOrEscalatedRecord {
                durable_floor: 3,
                recovered_head: 2,
            }
        );
        // Losing Ordered barrier-acked batch [3..6) WITHOUT moving generation violates P4!
        assert_eq!(
            o.audit_recovery(3, true, false),
            PrefixLawAuditDecision::ViolatedP4LostAckedWithoutGenerationMove {
                acked_head: 6,
                recovered_head: 3,
            }
        );
        // Losing Ordered batch [3..6) WITH generation move + lineage at 3 satisfies P2/P3/P4!
        assert_eq!(
            o.audit_recovery(3, true, true),
            PrefixLawAuditDecision::VerifiedPrefixLaw {
                recovered_head: 3,
                lost_acked_records: true,
                generation_moved: true,
            }
        );
    }
}
