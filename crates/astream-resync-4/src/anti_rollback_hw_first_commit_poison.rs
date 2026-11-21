// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Anti-rollback `.hw` first-commit pre-binding & watermark-failure log poisoning
//! (`Astream.Broker.TlaAntiRollbackHwFirstCommitPoison`).
//!
//! Models both anti-rollback durability invariants:
//! 1. On the first commit of a verified log, the initial `.hw` sidecar MUST be bound and synced
//!    BEFORE appending records so a crash mid-first-commit never leaves non-empty log records
//!    without a `.hw` sidecar (which `open_encrypted_verified` would permanently refuse),
//! 2. Any failed `.hw` watermark write irreversibly poisons the `BrokerLog` (`LogPoisonedHwFailure`),
//!    guaranteeing `acked_head <= persisted_hw` at all times and preventing a retry from either
//!    duplicating a partially committed record or acking a record not covered by `.hw`.

#[cfg(clean_islands)]
#[path = "anti_rollback_hw_first_commit_poison_island.rs"]
mod anti_rollback_hw_first_commit_poison_island;
#[cfg(clean_islands)]
pub use anti_rollback_hw_first_commit_poison_island::{
    acked_within_hw_clamp_b140, hw_persisted_advance_b140,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the persisted `.hw` anti-rollback watermark.
#[must_use]
pub const fn hw_persisted_advance_b140(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

#[cfg(not(clean_islands))]
/// Clamp the client-acknowledged head offset to `persisted_hw` (`acked_head <= persisted_hw`).
#[must_use]
pub const fn acked_within_hw_clamp_b140(cand_acked: u64, persisted_hw: u64) -> u64 {
    if cand_acked < persisted_hw {
        cand_acked
    } else {
        persisted_hw
    }
}

contract_fn! {
    /// True iff the log is unpoisoned, the initial `.hw` sidecar was bound prior to the first
    /// record append, and the batch's `.hw` watermark update succeeded.
    #[must_use]
    pub const fn hw_commit_ack_admissible_b140(
        log_poisoned: bool,
        initial_hw_bound: bool,
        hw_write_succeeded: bool,
    ) -> bool
    clauses [ensures result == (!log_poisoned && initial_hw_bound && hw_write_succeeded)]
    {
        !log_poisoned && initial_hw_bound && hw_write_succeeded
    }
}

/// Commit outcome under verified `.hw` anti-rollback protection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HwVerifiedCommitOutcome {
    CommittedAndCovered { acked_head: u64, persisted_hw: u64 },
    RefusedRollbackDetected { disk_head: u64, required_hw: u64 },
    LogPoisonedHwFailure,
}

/// Stateful `.hw` anti-rollback guard enforcing first-commit pre-bind and failure poisoning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AntiRollbackHwGuard {
    initial_hw_bound: bool,
    log_poisoned: bool,
    persisted_hw: u64,
    acked_head: u64,
}

impl AntiRollbackHwGuard {
    /// Verify open of a log at `disk_head` against an optional existing `.hw` sidecar.
    pub const fn open_verified(
        disk_head: u64,
        existing_hw_sidecar: Option<u64>,
    ) -> Result<Self, HwVerifiedCommitOutcome> {
        match existing_hw_sidecar {
            Some(hw) => {
                if disk_head < hw {
                    Err(HwVerifiedCommitOutcome::RefusedRollbackDetected {
                        disk_head,
                        required_hw: hw,
                    })
                } else {
                    Ok(Self {
                        initial_hw_bound: true,
                        log_poisoned: false,
                        persisted_hw: disk_head,
                        acked_head: acked_within_hw_clamp_b140(disk_head, disk_head),
                    })
                }
            }
            None => {
                if disk_head > 0 {
                    // Non-empty log missing `.hw`: rollback or unverified tamper!
                    Err(HwVerifiedCommitOutcome::RefusedRollbackDetected {
                        disk_head,
                        required_hw: disk_head,
                    })
                } else {
                    Ok(Self {
                        initial_hw_bound: false,
                        log_poisoned: false,
                        persisted_hw: 0,
                        acked_head: 0,
                    })
                }
            }
        }
    }

    #[must_use]
    pub const fn is_poisoned(&self) -> bool {
        self.log_poisoned
    }

    /// Execute a verified batch commit to `target_head`:
    /// 1. If `!initial_hw_bound`, pre-bind `.hw = 0` (`pre_bind_ok`) BEFORE writing log bytes!
    /// 2. After syncing log bytes, advance `.hw = target_head` (`hw_advance_ok`); on failure,
    ///    poison the log so neither retries nor un-watermarked acks can proceed!
    pub fn commit_batch(
        &mut self,
        target_head: u64,
        pre_bind_ok: bool,
        hw_advance_ok: bool,
    ) -> HwVerifiedCommitOutcome {
        if self.log_poisoned {
            return HwVerifiedCommitOutcome::LogPoisonedHwFailure;
        }
        if !self.initial_hw_bound {
            if !pre_bind_ok {
                self.log_poisoned = true;
                return HwVerifiedCommitOutcome::LogPoisonedHwFailure;
            }
            self.initial_hw_bound = true;
        }
        if !hw_commit_ack_admissible_b140(self.log_poisoned, self.initial_hw_bound, hw_advance_ok) {
            self.log_poisoned = true;
            return HwVerifiedCommitOutcome::LogPoisonedHwFailure;
        }
        self.persisted_hw = hw_persisted_advance_b140(self.persisted_hw, target_head);
        self.acked_head = acked_within_hw_clamp_b140(target_head, self.persisted_hw);
        HwVerifiedCommitOutcome::CommittedAndCovered {
            acked_head: self.acked_head,
            persisted_hw: self.persisted_hw,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_initial_hw_first_detects_rollback_and_poisons_on_hw_write_failure() {
        // Non-empty log without `.hw` is refused on `open_verified`:
        assert_eq!(
            AntiRollbackHwGuard::open_verified(5, None),
            Err(HwVerifiedCommitOutcome::RefusedRollbackDetected {
                disk_head: 5,
                required_hw: 5
            })
        );
        // Disk head rolled back below `.hw` (`3 < 10`) is refused:
        assert_eq!(
            AntiRollbackHwGuard::open_verified(3, Some(10)),
            Err(HwVerifiedCommitOutcome::RefusedRollbackDetected {
                disk_head: 3,
                required_hw: 10
            })
        );

        let mut g = AntiRollbackHwGuard::open_verified(0, None).unwrap();
        assert_eq!(
            g.commit_batch(4, true, true),
            HwVerifiedCommitOutcome::CommittedAndCovered {
                acked_head: 4,
                persisted_hw: 4
            }
        );
        // Failed `.hw` write on batch `4..8` poisons the log permanently:
        assert_eq!(
            g.commit_batch(8, true, false),
            HwVerifiedCommitOutcome::LogPoisonedHwFailure
        );
        assert!(g.is_poisoned());
        assert_eq!(
            g.commit_batch(8, true, true),
            HwVerifiedCommitOutcome::LogPoisonedHwFailure
        );
    }
}
