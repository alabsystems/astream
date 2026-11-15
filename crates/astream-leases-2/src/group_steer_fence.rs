// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ordered-tier escalated consumer-group commit visibility fence
//! (`Astream.Broker.TlaGroupSteerFence`, Island #292).

#[cfg(clean_islands)]
#[path = "group_steer_fence_island.rs"]
mod group_steer_fence_island;
#[cfg(clean_islands)]
pub use group_steer_fence_island::{group_cursor_cap_clamp, group_cursor_monotone};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn group_cursor_monotone(prev_cursor: u64, cand_cursor: u64) -> u64 {
    if prev_cursor < cand_cursor {
        cand_cursor
    } else {
        prev_cursor
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn group_cursor_cap_clamp(cursor: u64, durable_head: u64) -> u64 {
    if cursor < durable_head {
        cursor
    } else {
        durable_head
    }
}

contract_fn! {
    /// Verified check whether a held group commit record at `commit_offset` is covered by a
    /// completed full flush (`commit_offset < durable_head`), linked via `clean-kernel-defeq`
    /// to `group_commit_released_isl`.
    #[must_use]
    pub const fn group_commit_released(commit_offset: u64, durable_head: u64) -> bool
    clauses [ensures result == (commit_offset < durable_head)]
    {
        commit_offset < durable_head
    }
}

/// Pending escalated commit awaiting a full flush.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HeldGroupCommit {
    /// Log offset of the `/a/commit` record itself.
    pub commit_record_offset: u64,
    /// Target consumer-group cursor (`next` offset to steer readers to once durable).
    pub target_cursor: u64,
}

/// Per-group visibility fence tracking durable vs staged escalated commits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupSteerFence {
    visible_cursor: u64,
    durable_head: u64,
    held: Vec<HeldGroupCommit>,
}

impl Default for GroupSteerFence {
    fn default() -> Self {
        Self::new()
    }
}

impl GroupSteerFence {
    /// Create a fresh fence at cursor `0` and durable head `0`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            visible_cursor: 0,
            durable_head: 0,
            held: Vec::new(),
        }
    }

    /// Cursor visible to a newly attaching `SubscribeGroup` reader (`visible_cursor <= durable_head`).
    #[must_use]
    pub const fn visible_cursor(&self) -> u64 {
        self.visible_cursor
    }

    /// Last observed durable head from full flushes.
    #[must_use]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    /// Count of escalated group commits still awaiting full flush.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.held.len()
    }

    /// Stage a group commit: if `escalated` and not yet covered by `durable_head`, hold its
    /// steering effect until `advance_durable_head` passes `commit_record_offset`.
    pub fn stage_commit(&mut self, commit_record_offset: u64, target_cursor: u64, escalated: bool) {
        if !escalated || group_commit_released(commit_record_offset, self.durable_head) {
            let raised = group_cursor_monotone(self.visible_cursor, target_cursor);
            self.visible_cursor = group_cursor_cap_clamp(raised, self.durable_head);
        } else {
            self.held.push(HeldGroupCommit {
                commit_record_offset,
                target_cursor,
            });
        }
    }

    /// Advance `durable_head` after a full flush completes, releasing every held commit whose
    /// `commit_record_offset < durable_head`.
    pub fn advance_durable_head(&mut self, next_durable_head: u64) -> u64 {
        self.durable_head = group_cursor_monotone(self.durable_head, next_durable_head);
        let mut remaining = Vec::new();
        let mut rest = self.held.as_slice();
        while let [item, tail @ ..] = rest {
            if group_commit_released(item.commit_record_offset, self.durable_head) {
                let raised = group_cursor_monotone(self.visible_cursor, item.target_cursor);
                self.visible_cursor = group_cursor_cap_clamp(raised, self.durable_head);
            } else {
                remaining.push(*item);
            }
            rest = tail;
        }
        self.held = remaining;
        self.visible_cursor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn held_escalated_commit_does_not_steer_readers_until_full_flush() {
        let mut fence = GroupSteerFence::new();
        fence.advance_durable_head(5);
        fence.stage_commit(8, 8, true);
        assert_eq!(fence.visible_cursor(), 0);
        assert_eq!(fence.pending_count(), 1);

        assert_eq!(fence.advance_durable_head(8), 0);
        assert_eq!(fence.pending_count(), 1);

        assert_eq!(fence.advance_durable_head(9), 8);
        assert_eq!(fence.pending_count(), 0);
    }
}
