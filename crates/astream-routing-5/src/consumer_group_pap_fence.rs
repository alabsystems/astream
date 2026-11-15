// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Consumer-group `ProcessAndProduce` zombie-worker generation fence
//! (`Astream.Broker.TlaConsumerGroupPapFence`).
//!
//! Ensures atomic read-process-write (`process_and_produce`) exactly-once
//! semantics across consumer-group rebalances: a delayed worker holding an old
//! `member_gen` or stale `expected_committed_offset` is deterministically fenced
//! before its output batch and offset commit can append to the log.

#[cfg(clean_islands)]
#[path = "consumer_group_pap_fence_island.rs"]
mod consumer_group_pap_fence_island;
#[cfg(clean_islands)]
pub use consumer_group_pap_fence_island::{pap_gen_advance, pap_outputs_clamp};

/// Default maximum output records permitted in one atomic `ProcessAndProduce` batch.
pub const DEFAULT_MAX_PAP_OUTPUTS: u64 = 128;

#[cfg(not(clean_islands))]
/// Monotonically advance the consumer group's rebalance generation.
#[must_use]
pub const fn pap_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Clamp output count in a single `ProcessAndProduce` transaction to `max_outputs`.
#[must_use]
pub const fn pap_outputs_clamp(cand_outputs: u64, max_outputs: u64) -> u64 {
    if cand_outputs < max_outputs {
        cand_outputs
    } else {
        max_outputs
    }
}

contract_fn! {
    /// True iff `member_gen == active_gen`.
    #[must_use]
    pub const fn pap_gen_matches(active_gen: u64, member_gen: u64) -> bool
    clauses [ensures result == (active_gen == member_gen)]
    {
        active_gen == member_gen
    }
}

/// Refusal reasons when validating an atomic `ProcessAndProduce` commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PapFenceError {
    ZombieMemberGeneration {
        active_gen: u64,
        member_gen: u64,
    },
    CommittedOffsetCASMismatch {
        actual: Option<u64>,
        expected: Option<u64>,
    },
    NonMonotonicCommit {
        current: u64,
        proposed: u64,
    },
    TooManyOutputs {
        requested: u64,
        max_outputs: u64,
    },
}

/// Stateful per-consumer-group `ProcessAndProduce` CAS + generation fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConsumerGroupPapFence {
    group_gen: u64,
    committed_offset: Option<u64>,
    last_tx_outputs: u64,
    max_outputs: u64,
}

impl Default for ConsumerGroupPapFence {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_PAP_OUTPUTS)
    }
}

impl ConsumerGroupPapFence {
    #[must_use]
    pub const fn new(max_outputs: u64) -> Self {
        let cap = if max_outputs == 0 {
            DEFAULT_MAX_PAP_OUTPUTS
        } else {
            max_outputs
        };
        Self {
            group_gen: 1,
            committed_offset: None,
            last_tx_outputs: 0,
            max_outputs: cap,
        }
    }

    #[must_use]
    pub const fn group_gen(&self) -> u64 {
        self.group_gen
    }

    #[must_use]
    pub const fn committed_offset(&self) -> Option<u64> {
        self.committed_offset
    }

    #[must_use]
    pub const fn last_tx_outputs(&self) -> u64 {
        self.last_tx_outputs
    }

    /// Rebalance the group onto a strictly newer generation, fencing prior members.
    pub fn rebalance(&mut self) -> u64 {
        let cand = self.group_gen.saturating_add(1);
        self.group_gen = pap_gen_advance(self.group_gen, cand);
        self.group_gen
    }

    /// Validate and commit an atomic `(expected_prev, new_committed_offset, output_count)` transaction.
    pub fn validate_and_commit(
        &mut self,
        member_gen: u64,
        expected_prev: Option<u64>,
        new_committed_offset: u64,
        output_count: u64,
    ) -> Result<u64, PapFenceError> {
        if !pap_gen_matches(self.group_gen, member_gen) {
            return Err(PapFenceError::ZombieMemberGeneration {
                active_gen: self.group_gen,
                member_gen,
            });
        }
        if self.committed_offset != expected_prev {
            return Err(PapFenceError::CommittedOffsetCASMismatch {
                actual: self.committed_offset,
                expected: expected_prev,
            });
        }
        if let Some(cur) = self.committed_offset {
            if new_committed_offset <= cur {
                return Err(PapFenceError::NonMonotonicCommit {
                    current: cur,
                    proposed: new_committed_offset,
                });
            }
        }
        if output_count > self.max_outputs {
            return Err(PapFenceError::TooManyOutputs {
                requested: output_count,
                max_outputs: self.max_outputs,
            });
        }

        self.committed_offset = Some(new_committed_offset);
        self.last_tx_outputs = pap_outputs_clamp(output_count, self.max_outputs);
        Ok(new_committed_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fences_zombie_generation_and_duplicate_cas_commits() {
        let mut fence = ConsumerGroupPapFence::new(64);
        assert_eq!(fence.validate_and_commit(1, None, 10, 3), Ok(10));
        // Duplicate retry at expected_prev = None is rejected by CAS!
        assert_eq!(
            fence.validate_and_commit(1, None, 10, 3),
            Err(PapFenceError::CommittedOffsetCASMismatch {
                actual: Some(10),
                expected: None,
            })
        );

        let gen2 = fence.rebalance();
        assert_eq!(gen2, 2);
        // Zombie worker from gen 1 is fenced even with matching expected_prev!
        assert_eq!(
            fence.validate_and_commit(1, Some(10), 11, 1),
            Err(PapFenceError::ZombieMemberGeneration {
                active_gen: 2,
                member_gen: 1,
            })
        );
        // Active worker in gen 2 commits cleanly
        assert_eq!(fence.validate_and_commit(2, Some(10), 11, 2), Ok(11));
    }
}
