// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotonic anti-rollback witness counter verifier (`Astream.Broker.TlaAntiRollbackCounterFence`).
//!
//! Protects `astream-broker` (`anti-rollback`) against VM snapshot revert, disk-image rollback,
//! and stale segment substitution by checking persisted `(log_id_tag, disk_counter)` against
//! an external monotonic witness counter.

#[cfg(clean_islands)]
#[path = "anti_rollback_counter_fence_island.rs"]
mod anti_rollback_counter_fence_island;
#[cfg(clean_islands)]
pub use anti_rollback_counter_fence_island::{
    rollback_violation_clamp_b112, witness_counter_advance_b112,
};

#[cfg(not(clean_islands))]
/// Clamp recorded rollback-attempt violation count to `max_violations`.
#[must_use]
pub const fn rollback_violation_clamp_b112(cand_violations: u64, max_violations: u64) -> u64 {
    if cand_violations < max_violations {
        cand_violations
    } else {
        max_violations
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the trusted anti-rollback witness counter.
#[must_use]
pub const fn witness_counter_advance_b112(cur_witness: u64, cand_witness: u64) -> u64 {
    if cur_witness < cand_witness {
        cand_witness
    } else {
        cur_witness
    }
}

contract_fn! {
    /// True iff `disk_counter` is at or ahead of `witness_counter` (no rollback).
    #[must_use]
    pub const fn disk_counter_fresh_b112(disk_counter: u64, witness_counter: u64) -> bool
    clauses [ensures result == (witness_counter <= disk_counter)]
    {
        witness_counter <= disk_counter
    }
}

/// Verdict when opening or sealing a log header against the anti-rollback witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AntiRollbackVerdict {
    VerifiedFresh {
        committed_witness: u64,
    },
    RollbackDetected {
        disk_counter: u64,
        witness_counter: u64,
        violations: u64,
    },
    LogIdMismatch {
        expected_log_tag: u64,
        found_log_tag: u64,
    },
}

/// Monotonic anti-rollback witness fence for a durable broker shard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AntiRollbackCounterFence {
    expected_log_tag: u64,
    witness_counter: u64,
    violations: u64,
    max_violations: u64,
}

impl AntiRollbackCounterFence {
    #[must_use]
    pub const fn new(expected_log_tag: u64, initial_witness: u64, max_violations: u64) -> Self {
        let cap = if max_violations == 0 {
            64
        } else {
            max_violations
        };
        Self {
            expected_log_tag,
            witness_counter: initial_witness,
            violations: 0,
            max_violations: cap,
        }
    }

    #[must_use]
    pub const fn witness_counter(&self) -> u64 {
        self.witness_counter
    }

    /// Verify a disk header `(log_tag, disk_counter)` and ratify `disk_counter` into the witness.
    pub fn verify_and_ratchet(&mut self, log_tag: u64, disk_counter: u64) -> AntiRollbackVerdict {
        if log_tag != self.expected_log_tag {
            return AntiRollbackVerdict::LogIdMismatch {
                expected_log_tag: self.expected_log_tag,
                found_log_tag: log_tag,
            };
        }
        if !disk_counter_fresh_b112(disk_counter, self.witness_counter) {
            let cand = self.violations.saturating_add(1);
            self.violations = rollback_violation_clamp_b112(cand, self.max_violations);
            return AntiRollbackVerdict::RollbackDetected {
                disk_counter,
                witness_counter: self.witness_counter,
                violations: self.violations,
            };
        }
        self.witness_counter = witness_counter_advance_b112(self.witness_counter, disk_counter);
        AntiRollbackVerdict::VerifiedFresh {
            committed_witness: self.witness_counter,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratchets_witness_and_catches_snapshot_rollback() {
        let mut f = AntiRollbackCounterFence::new(0xABCD, 10, 8);
        assert_eq!(
            f.verify_and_ratchet(0xABCD, 15),
            AntiRollbackVerdict::VerifiedFresh {
                committed_witness: 15
            }
        );
        assert_eq!(
            f.verify_and_ratchet(0xABCD, 12),
            AntiRollbackVerdict::RollbackDetected {
                disk_counter: 12,
                witness_counter: 15,
                violations: 1,
            }
        );
    }
}
