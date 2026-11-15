// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Consumer-group `/a/commit` monotone watermark & in-flight lease planner
//! (`Astream.Broker.TlaConsumerGroupLease`).
//!
//! Coordinates `SubscribeGroup`, `drain`, `commit`, and `ProcessAndProduce` (`ack`) cursors:
//! - Rejects `commit`/`ack` operands at or past `visible_head` via [`group_commit_operand_valid`].
//! - Advances `committed_offset` monotonically (`committed_offset <= head_offset`) while
//!   bounding outstanding leased items (`leased_count <= max_in_flight`).

#[cfg(clean_islands)]
#[path = "subscribe_group_fair_lease_island.rs"]
mod subscribe_group_fair_lease_island;
#[cfg(clean_islands)]
pub use subscribe_group_fair_lease_island::{group_commit_clamp, group_lease_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn group_commit_clamp(candidate: u64, head: u64) -> u64 {
    if candidate < head {
        candidate
    } else {
        head
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn group_lease_clamp(leased: u64, max_in_flight: u64) -> u64 {
    if leased < max_in_flight {
        leased
    } else {
        max_in_flight
    }
}

contract_fn! {
    /// Verified check that a `CommitGroup` / `ack` inclusive `upto_offset` lies strictly
    /// below `visible_head` (`upto_offset < visible_head`), linked via `clean-kernel-defeq`
    /// to `group_commit_operand_valid_isl`.
    #[must_use]
    pub const fn group_commit_operand_valid(upto_offset: u64, visible_head: u64) -> bool
    clauses [ensures result == (upto_offset < visible_head)]
    {
        upto_offset < visible_head
    }
}

/// Outcome of validating and applying a consumer-group `commit` / `ack` operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupCommitVerdict {
    /// Advanced the group's exclusive resume cursor to `next_resume_offset` (`<= visible_head`).
    Advanced {
        /// New exclusive resume cursor (`upto_offset + 1`).
        next_resume_offset: u64,
    },
    /// Idempotent no-op because `upto_offset + 1 <= committed_offset`.
    AlreadyCommitted {
        /// Existing exclusive resume cursor.
        current_resume_offset: u64,
    },
    /// Refused because `upto_offset >= visible_head`.
    OutOfRange {
        /// Invalid requested inclusive offset.
        upto_offset: u64,
        /// Current visible head of the log.
        visible_head: u64,
    },
}

/// Stateful consumer-group watermark & bounded lease tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsumerGroupLeaseTracker {
    group_name: String,
    committed_offset: u64,
    head_offset: u64,
    leased_count: u64,
    max_in_flight: u64,
}

impl ConsumerGroupLeaseTracker {
    /// Create a tracker for `group_name` with bounded `max_in_flight` (`>= 1`).
    #[must_use]
    pub fn new(group_name: impl Into<String>, max_in_flight: u64) -> Self {
        let cap = if max_in_flight < 1 { 1 } else { max_in_flight };
        Self {
            group_name: group_name.into(),
            committed_offset: 0,
            head_offset: 0,
            leased_count: 0,
            max_in_flight: cap,
        }
    }

    /// Group name.
    #[must_use]
    pub fn group_name(&self) -> &str {
        &self.group_name
    }

    /// Exclusive resume cursor (`upto + 1`, `<= head_offset`).
    #[must_use]
    pub const fn committed_offset(&self) -> u64 {
        self.committed_offset
    }

    /// Latest observed `visible_head`.
    #[must_use]
    pub const fn head_offset(&self) -> u64 {
        self.head_offset
    }

    /// Clamped count of currently leased unacknowledged items (`<= max_in_flight`).
    #[must_use]
    pub const fn leased_count(&self) -> u64 {
        self.leased_count
    }

    /// Lease up to `available_matches` newly visible items below `visible_head`, returning the
    /// number of items newly leased under `max_in_flight`.
    pub fn lease_batch(&mut self, visible_head: u64, available_matches: u64) -> u64 {
        if visible_head > self.head_offset {
            self.head_offset = visible_head;
        }
        self.committed_offset = group_commit_clamp(self.committed_offset, self.head_offset);
        let budget = self.max_in_flight.saturating_sub(self.leased_count);
        let granted = if available_matches < budget {
            available_matches
        } else {
            budget
        };
        let raw_leased = self.leased_count.saturating_add(granted);
        self.leased_count = group_lease_clamp(raw_leased, self.max_in_flight);
        granted
    }

    /// Validate and apply an inclusive `upto_offset` group commit against `visible_head`,
    /// releasing `acked_leases` from `leased_count`.
    pub fn commit_upto(
        &mut self,
        upto_offset: u64,
        visible_head: u64,
        acked_leases: u64,
    ) -> GroupCommitVerdict {
        if visible_head > self.head_offset {
            self.head_offset = visible_head;
        }
        if !group_commit_operand_valid(upto_offset, self.head_offset) {
            return GroupCommitVerdict::OutOfRange {
                upto_offset,
                visible_head: self.head_offset,
            };
        }
        let next_resume = upto_offset.saturating_add(1);
        let rem_leased = self.leased_count.saturating_sub(acked_leases);
        self.leased_count = group_lease_clamp(rem_leased, self.max_in_flight);
        if next_resume <= self.committed_offset {
            self.committed_offset = group_commit_clamp(self.committed_offset, self.head_offset);
            GroupCommitVerdict::AlreadyCommitted {
                current_resume_offset: self.committed_offset,
            }
        } else {
            self.committed_offset = group_commit_clamp(next_resume, self.head_offset);
            GroupCommitVerdict::Advanced {
                next_resume_offset: self.committed_offset,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_visible_head_bound_monotone_commit_and_in_flight_lease_cap() {
        let mut g = ConsumerGroupLeaseTracker::new("inbox-workers", 4);
        assert_eq!(g.lease_batch(10, 6), 4);
        assert_eq!(g.leased_count(), 4);
        assert_eq!(g.lease_batch(10, 2), 0);

        // Operand at or past visible_head (10) is refused!
        assert_eq!(
            g.commit_upto(10, 10, 1),
            GroupCommitVerdict::OutOfRange {
                upto_offset: 10,
                visible_head: 10,
            }
        );
        assert_eq!(g.leased_count(), 4);

        // Valid commit at offset 5 -> next_resume = 6, releases 2 leases!
        assert_eq!(
            g.commit_upto(5, 10, 2),
            GroupCommitVerdict::Advanced {
                next_resume_offset: 6,
            }
        );
        assert_eq!(g.leased_count(), 2);

        // Stale commit at offset 3 -> monotone idempotent no-op!
        assert_eq!(
            g.commit_upto(3, 10, 0),
            GroupCommitVerdict::AlreadyCommitted {
                current_resume_offset: 6,
            }
        );
    }
}
