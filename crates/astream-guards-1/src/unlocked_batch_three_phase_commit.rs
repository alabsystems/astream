// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Three-phase unlocked batch write (`begin -> unlocked write+flush -> end`) & mutation fence
//! (`evidence/manifest.toml` `broker.unlocked-batch-write`;
//! `Astream.Broker.TlaUnlockedBatchThreePhaseCommit`).
//!
//! Models the writer's lock-free I/O window in `astream-broker`:
//! - **Locked `begin`**: stages records, snapshots `captured_flush_fault` & `captured_truncate_fault`
//!   from the seam, and sets `batch_in_flight = true` WITHOUT advancing `visible_head` (so concurrent
//!   `Fetch`, `Last`, and `Subscribe` catch-up read uninterrupted while seeing only committed records!),
//! - **In-window mutation fence**: while `batch_in_flight`, direct `BrokerLog` mutations return
//!   `RefusedBatchInFlightOutsideLock`, whereas `Broker::retain_before` increments `retention_waits`
//!   to serialize behind the writer's batch lock,
//! - **Locked `end`**: promotes `visible_head` iff the unlocked flush (evaluated against the seam
//!   snapshot captured at `begin`!) succeeded; otherwise rolls back using the captured truncate seam!

#[cfg(clean_islands)]
#[path = "unlocked_batch_three_phase_commit_island.rs"]
mod unlocked_batch_three_phase_commit_island;
#[cfg(clean_islands)]
pub use unlocked_batch_three_phase_commit_island::{
    retention_wait_count_advance_b145, visible_head_promote_advance_b145,
};

#[cfg(not(clean_islands))]
/// Monotonically promote the reader-visible committed log head.
#[must_use]
pub const fn visible_head_promote_advance_b145(cur_head: u64, cand_head: u64) -> u64 {
    if cur_head < cand_head {
        cand_head
    } else {
        cur_head
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `BrokerStats::retention_waits`.
#[must_use]
pub const fn retention_wait_count_advance_b145(cur_waits: u64, cand_waits: u64) -> u64 {
    if cur_waits < cand_waits {
        cand_waits
    } else {
        cur_waits
    }
}

contract_fn! {
    /// Direct `BrokerLog` mutation (append, second begin, close, raw retain) is admissible ONLY
    /// when no unlocked batch write is in flight and the log is unpoisoned.
    #[must_use]
    pub const fn direct_log_mutation_admissible_b145(
        batch_in_flight: bool,
        log_poisoned: bool,
    ) -> bool
    clauses [ensures result == (!batch_in_flight && !log_poisoned)]
    {
        !batch_in_flight && !log_poisoned
    }
}

/// Snapshot of fault-injection flags captured at `locked_begin` that travels with the batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapturedBatchSeam {
    pub staged_target_head: u64,
    pub flush_fault: bool,
    pub truncate_fault: bool,
}

/// Outcome of the three-phase unlocked batch state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnlockedBatchOutcome {
    BeganInFlight { seam: CapturedBatchSeam },
    PromotedAtEnd { visible_head: u64 },
    RolledBackCleanly { visible_head: u64 },
    RollbackTruncatePoisonedLog,
    RefusedBatchInFlightOutsideLock,
    RefusedLogPoisoned,
}

/// Coordinator for `BrokerLog`'s unlocked write window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnlockedBatchCoordinator {
    visible_head: u64,
    batch_in_flight: bool,
    log_poisoned: bool,
    retention_waits: u64,
}

impl UnlockedBatchCoordinator {
    #[must_use]
    pub const fn new(initial_head: u64) -> Self {
        Self {
            visible_head: initial_head,
            batch_in_flight: false,
            log_poisoned: false,
            retention_waits: 0,
        }
    }

    #[must_use]
    pub const fn visible_head(&self) -> u64 {
        self.visible_head
    }

    #[must_use]
    pub const fn retention_waits(&self) -> u64 {
        self.retention_waits
    }

    pub fn locked_begin(
        &mut self,
        batch_records: u64,
        live_flush_fault: bool,
        live_truncate_fault: bool,
    ) -> UnlockedBatchOutcome {
        if self.log_poisoned {
            return UnlockedBatchOutcome::RefusedLogPoisoned;
        }
        if !direct_log_mutation_admissible_b145(self.batch_in_flight, self.log_poisoned) {
            return UnlockedBatchOutcome::RefusedBatchInFlightOutsideLock;
        }
        self.batch_in_flight = true;
        UnlockedBatchOutcome::BeganInFlight {
            seam: CapturedBatchSeam {
                staged_target_head: self.visible_head.saturating_add(batch_records),
                flush_fault: live_flush_fault,
                truncate_fault: live_truncate_fault,
            },
        }
    }

    #[must_use]
    pub const fn check_concurrent_direct_mutation(&self) -> Option<UnlockedBatchOutcome> {
        if self.log_poisoned {
            Some(UnlockedBatchOutcome::RefusedLogPoisoned)
        } else if !direct_log_mutation_admissible_b145(self.batch_in_flight, false) {
            Some(UnlockedBatchOutcome::RefusedBatchInFlightOutsideLock)
        } else {
            None
        }
    }

    pub fn note_broker_retain_wait_if_in_flight(&mut self) -> u64 {
        if self.batch_in_flight {
            let next = self.retention_waits.saturating_add(1);
            self.retention_waits = retention_wait_count_advance_b145(self.retention_waits, next);
        }
        self.retention_waits
    }

    pub fn locked_end(
        &mut self,
        seam: CapturedBatchSeam,
        io_write_ok: bool,
    ) -> UnlockedBatchOutcome {
        self.batch_in_flight = false;
        if io_write_ok && !seam.flush_fault {
            self.visible_head =
                visible_head_promote_advance_b145(self.visible_head, seam.staged_target_head);
            UnlockedBatchOutcome::PromotedAtEnd {
                visible_head: self.visible_head,
            }
        } else if seam.truncate_fault {
            self.log_poisoned = true;
            UnlockedBatchOutcome::RollbackTruncatePoisonedLog
        } else {
            UnlockedBatchOutcome::RolledBackCleanly {
                visible_head: self.visible_head,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn readers_see_old_head_in_window_mutations_refuse_and_seam_travels_with_batch() {
        let mut c = UnlockedBatchCoordinator::new(3);
        let UnlockedBatchOutcome::BeganInFlight { seam } = c.locked_begin(1, true, false) else {
            panic!("expected begin");
        };
        // Readers still see head 3 while unlocked write is in flight:
        assert_eq!(c.visible_head(), 3);
        // Direct mutation in window is refused; Broker::retain_before counts a wait:
        assert_eq!(
            c.check_concurrent_direct_mutation(),
            Some(UnlockedBatchOutcome::RefusedBatchInFlightOutsideLock)
        );
        assert_eq!(c.note_broker_retain_wait_if_in_flight(), 1);
        // Even if live fault cleared mid-window, batch's captured `flush_fault=true` rolls back cleanly:
        assert_eq!(
            c.locked_end(seam, true),
            UnlockedBatchOutcome::RolledBackCleanly { visible_head: 3 }
        );
    }
}
