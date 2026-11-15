// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-worker task lease & work-stealing epoch fence (`Astream.Agent.TlaWorkStealingEpoch`).
//!
//! Coordinates `aterm ctl @self spawn` worker pools (`claude`, `codex-alab`, `agy`):
//! when a worker stalls (`sys jobs`), a sibling worker can steal the task only by
//! acquiring a strictly higher `claim_epoch`, fencing any late completion from the
//! stalled worker and bounding total steal attempts (`<= max_attempts`).

#[cfg(clean_islands)]
#[path = "work_stealing_epoch_island.rs"]
mod work_stealing_epoch_island;
#[cfg(clean_islands)]
pub use work_stealing_epoch_island::{steal_attempt_clamp, steal_epoch_advance};

/// Default maximum times a single task may be stolen before escalating to `NeedsPerson`.
pub const DEFAULT_MAX_STEAL_ATTEMPTS: u64 = 4;

#[cfg(not(clean_islands))]
/// Monotonically advance the authoritative claim epoch for a task.
#[must_use]
pub const fn steal_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp cumulative steal attempts to `max_attempts`.
#[must_use]
pub const fn steal_attempt_clamp(cand_attempts: u64, max_attempts: u64) -> u64 {
    if cand_attempts < max_attempts {
        cand_attempts
    } else {
        max_attempts
    }
}

contract_fn! {
    /// True iff `claim_epoch` strictly fences `prior_epoch`.
    #[must_use]
    pub const fn steal_claim_fences_prior(prior_epoch: u64, claim_epoch: u64) -> bool
    clauses [ensures result == (prior_epoch < claim_epoch)]
    {
        prior_epoch < claim_epoch
    }
}

/// Lifecycle state of astealable worker task slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskClaimPhase {
    Unclaimed,
    Claimed {
        worker_sid: u64,
        lease_deadline_ms: u64,
    },
    Completed {
        worker_sid: u64,
    },
    EscalatedNeedsPerson,
}

/// Refusal reasons when claiming, stealing, or completing a task slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkStealError {
    AlreadyCompleted,
    LeaseStillActive {
        holder_sid: u64,
        deadline_ms: u64,
    },
    MaxStealsExhausted {
        attempts: u64,
    },
    StaleWorkerEpoch {
        expected_epoch: u64,
        worker_epoch: u64,
    },
    WorkerSidMismatch {
        expected_sid: u64,
        actual_sid: u64,
    },
}

/// Single task lease & work-stealing fence tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkStealingSlot {
    task_offset: u64,
    epoch: u64,
    attempts: u64,
    max_attempts: u64,
    phase: TaskClaimPhase,
}

impl WorkStealingSlot {
    #[must_use]
    pub const fn new(task_offset: u64, max_attempts: u64) -> Self {
        let cap = if max_attempts == 0 {
            DEFAULT_MAX_STEAL_ATTEMPTS
        } else {
            max_attempts
        };
        Self {
            task_offset,
            epoch: 0,
            attempts: 0,
            max_attempts: cap,
            phase: TaskClaimPhase::Unclaimed,
        }
    }

    #[must_use]
    pub const fn task_offset(&self) -> u64 {
        self.task_offset
    }

    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    #[must_use]
    pub const fn attempts(&self) -> u64 {
        self.attempts
    }

    #[must_use]
    pub const fn phase(&self) -> TaskClaimPhase {
        self.phase
    }

    /// Initial claim or expired-lease work-steal by `new_worker_sid`.
    pub fn claim_or_steal(
        &mut self,
        new_worker_sid: u64,
        now_ms: u64,
        lease_duration_ms: u64,
    ) -> Result<u64, WorkStealError> {
        match self.phase {
            TaskClaimPhase::Completed { .. } => return Err(WorkStealError::AlreadyCompleted),
            TaskClaimPhase::EscalatedNeedsPerson => {
                return Err(WorkStealError::MaxStealsExhausted {
                    attempts: self.attempts,
                });
            }
            TaskClaimPhase::Claimed {
                worker_sid,
                lease_deadline_ms,
            } => {
                if now_ms < lease_deadline_ms {
                    return Err(WorkStealError::LeaseStillActive {
                        holder_sid: worker_sid,
                        deadline_ms: lease_deadline_ms,
                    });
                }
                if self.attempts >= self.max_attempts {
                    self.phase = TaskClaimPhase::EscalatedNeedsPerson;
                    return Err(WorkStealError::MaxStealsExhausted {
                        attempts: self.attempts,
                    });
                }
                let cand_att = self.attempts.saturating_add(1);
                self.attempts = steal_attempt_clamp(cand_att, self.max_attempts);
            }
            TaskClaimPhase::Unclaimed => {}
        }

        let cand_ep = self.epoch.saturating_add(1);
        let next_ep = steal_epoch_advance(self.epoch, cand_ep);
        if !steal_claim_fences_prior(self.epoch, next_ep) {
            return Err(WorkStealError::StaleWorkerEpoch {
                expected_epoch: self.epoch,
                worker_epoch: next_ep,
            });
        }
        self.epoch = next_ep;
        self.phase = TaskClaimPhase::Claimed {
            worker_sid: new_worker_sid,
            lease_deadline_ms: now_ms.saturating_add(lease_duration_ms),
        };
        Ok(self.epoch)
    }

    /// Commit completion only if `(worker_sid, worker_epoch)` matches the active fenced lease.
    pub fn complete(&mut self, worker_sid: u64, worker_epoch: u64) -> Result<(), WorkStealError> {
        if worker_epoch != self.epoch {
            return Err(WorkStealError::StaleWorkerEpoch {
                expected_epoch: self.epoch,
                worker_epoch,
            });
        }
        match self.phase {
            TaskClaimPhase::Completed { .. } => Err(WorkStealError::AlreadyCompleted),
            TaskClaimPhase::Claimed {
                worker_sid: holder, ..
            } => {
                if holder != worker_sid {
                    return Err(WorkStealError::WorkerSidMismatch {
                        expected_sid: holder,
                        actual_sid: worker_sid,
                    });
                }
                self.phase = TaskClaimPhase::Completed { worker_sid };
                Ok(())
            }
            TaskClaimPhase::Unclaimed | TaskClaimPhase::EscalatedNeedsPerson => {
                Err(WorkStealError::StaleWorkerEpoch {
                    expected_epoch: self.epoch,
                    worker_epoch,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stealing_fences_stalled_worker_and_caps_attempts() {
        let mut slot = WorkStealingSlot::new(42, 2);
        let ep1 = slot.claim_or_steal(101, 1_000, 5_000).unwrap();
        assert_eq!(ep1, 1);

        // Cannot steal while lease active
        assert_eq!(
            slot.claim_or_steal(102, 4_000, 5_000),
            Err(WorkStealError::LeaseStillActive {
                holder_sid: 101,
                deadline_ms: 6_000,
            })
        );

        // Lease expires at 6_000; worker 102 steals at epoch 2 (attempt 1/2)
        let ep2 = slot.claim_or_steal(102, 6_000, 5_000).unwrap();
        assert_eq!(ep2, 2);
        assert_eq!(slot.attempts(), 1);

        // Stalled worker 101 wakes up late and tries to complete at epoch 1 -> fenced!
        assert_eq!(
            slot.complete(101, ep1),
            Err(WorkStealError::StaleWorkerEpoch {
                expected_epoch: 2,
                worker_epoch: 1,
            })
        );

        // Worker 102 also stalls; worker 103 steals at epoch 3 (attempt 2/2)
        let ep3 = slot.claim_or_steal(103, 12_000, 5_000).unwrap();
        assert_eq!(ep3, 3);
        assert_eq!(slot.attempts(), 2);

        // Worker 103 stalls; max steals (2) exhausted -> escalates to NeedsPerson!
        assert_eq!(
            slot.claim_or_steal(104, 18_000, 5_000),
            Err(WorkStealError::MaxStealsExhausted { attempts: 2 })
        );
        assert_eq!(slot.phase(), TaskClaimPhase::EscalatedNeedsPerson);
    }
}
