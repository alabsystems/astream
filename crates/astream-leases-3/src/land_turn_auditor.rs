// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autopilot Land turn-end auditor (`Astream.Agent.TlaLandTurnAuditor`).
//!
//! Enforces `aterm` Autopilot Land's exact parking precondition: a supervised agent session
//! under `autopilot=land` continues every turn end until zero uncommitted files, zero stashes,
//! zero unpushed commits, zero unmerged local branches, and zero parked background tasks
//! remain, AND the agent's final reply defends that state starting with `"Nothing left:"`
//! within a concise summary (`<= MAX_LAND_AUDIT_LINES`).

#![allow(clippy::manual_range_contains)]

#[cfg(clean_islands)]
#[path = "land_turn_auditor_island.rs"]
mod land_turn_auditor_island;
#[cfg(clean_islands)]
pub use land_turn_auditor_island::{land_audit_count_clamp, land_audit_turn_advance};

/// Mirror of Clean's `land_audit_count_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_audit_count_clamp(dirty_items: u64, max_items: u64) -> u64 {
    if dirty_items < max_items {
        dirty_items
    } else {
        max_items
    }
}

/// Mirror of Clean's `land_audit_turn_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_audit_turn_advance(cur_turn: u64, next_turn: u64) -> u64 {
    if cur_turn < next_turn {
        next_turn
    } else {
        cur_turn
    }
}

contract_fn! {
    /// Kernel-certified check that zero unlanded items remain (`dirty_items == 0`),
    /// linked via `clean-kernel-defeq` to `land_audit_is_clean_isl`.
    #[must_use]
    pub const fn land_audit_is_clean(dirty_items: u64) -> bool
    clauses [ensures result == (dirty_items == 0)]
    {
        dirty_items == 0
    }
}

/// Maximum dirty-item count tracked per Land evaluation snapshot.
pub const MAX_LAND_AUDIT_DIRTY_ITEMS: u64 = 1_000_000;

/// Maximum non-empty lines permitted in a `"Nothing left:"` closing defense.
pub const MAX_LAND_AUDIT_LINES: usize = 8;

/// Prefix required on the closing reply that ends an `autopilot=land` session.
pub const LAND_AUDIT_NOTHING_LEFT_PREFIX: &[u8; 13] = b"Nothing left:";

/// Repository and session state evaluated at the end of a turn under `autopilot=land`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LandTurnAuditSnapshot {
    /// Uncommitted tracked modifications, staged files, or untracked non-ignored files.
    pub uncommitted_files: u64,
    /// Commits on `HEAD` not yet pushed to `origin/main`.
    pub unpushed_commits: u64,
    /// Local branches not merged into `origin/main`.
    pub unmerged_branches: u64,
    /// Git stash entries in the repository.
    pub stash_entries: u64,
    /// Running background tasks owned by the session.
    pub running_bg_tasks: u64,
}

impl LandTurnAuditSnapshot {
    /// Clamped total count of unlanded items (`<= MAX_LAND_AUDIT_DIRTY_ITEMS`).
    #[must_use]
    pub const fn total_dirty_items(&self) -> u64 {
        let sum = self
            .uncommitted_files
            .saturating_add(self.unpushed_commits)
            .saturating_add(self.unmerged_branches)
            .saturating_add(self.stash_entries)
            .saturating_add(self.running_bg_tasks);
        land_audit_count_clamp(sum, MAX_LAND_AUDIT_DIRTY_ITEMS)
    }
}

/// Decision emitted by [`LandTurnAuditor::evaluate_turn`] at turn end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LandTurnAuditDecision {
    /// Work is 100% landed on `origin/main` and defended with `"Nothing left:"`; park cleanly.
    ParkDone { turn: u64 },
    /// Work or closing defense is incomplete; inject a continuation prompt naming what remains.
    Continue {
        turn: u64,
        dirty_items: u64,
        reason: &'static str,
    },
}

#[must_use]
const fn trim_ascii_bytes(mut bytes: &[u8]) -> &[u8] {
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = bytes {
        if last.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
    bytes
}

/// Check whether `reply` begins (after leading ASCII whitespace) with `"Nothing left:"`,
/// contains non-empty defense text after the colon, and spans `1..=MAX_LAND_AUDIT_LINES`
/// non-empty lines.
#[must_use]
pub fn valid_nothing_left_audit_defense(reply: &str) -> bool {
    let trimmed = trim_ascii_bytes(reply.as_bytes());
    let Some(after) = trimmed.strip_prefix(b"Nothing left:") else {
        return false;
    };
    if trim_ascii_bytes(after).is_empty() {
        return false;
    }
    let mut non_empty_lines = 0usize;
    let mut cur_has_non_ws = false;
    let mut rest = trimmed;
    while let [b, tail @ ..] = rest {
        if *b == b'\n' {
            if cur_has_non_ws {
                non_empty_lines = non_empty_lines.saturating_add(1);
                if non_empty_lines > MAX_LAND_AUDIT_LINES {
                    return false;
                }
                cur_has_non_ws = false;
            }
        } else if !b.is_ascii_whitespace() {
            cur_has_non_ws = true;
        }
        rest = tail;
    }
    if cur_has_non_ws {
        non_empty_lines = non_empty_lines.saturating_add(1);
    }
    non_empty_lines >= 1 && non_empty_lines <= MAX_LAND_AUDIT_LINES
}

/// Stateful per-session verifier implementing `Astream.Agent.TlaLandTurnAuditor`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LandTurnAuditor {
    turn: u64,
    last_dirty_items: u64,
    parked_done: bool,
}

impl Default for LandTurnAuditor {
    fn default() -> Self {
        Self::new()
    }
}

impl LandTurnAuditor {
    /// Construct a fresh auditor at turn `0` (`parked_done == false`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            turn: 0,
            last_dirty_items: 0,
            parked_done: false,
        }
    }

    /// Monotone turn counter.
    #[must_use]
    pub const fn turn(&self) -> u64 {
        self.turn
    }

    /// Clamped dirty-item count from the most recent turn evaluation.
    #[must_use]
    pub const fn last_dirty_items(&self) -> u64 {
        self.last_dirty_items
    }

    /// Whether the session has satisfied `LandAuditSafetyInv` and parked cleanly.
    #[must_use]
    pub const fn is_parked_done(&self) -> bool {
        self.parked_done
    }

    /// Evaluate turn end against `snapshot` and the agent's `reply`.
    pub fn evaluate_turn(
        &mut self,
        snapshot: &LandTurnAuditSnapshot,
        reply: &str,
    ) -> LandTurnAuditDecision {
        let next_turn = land_audit_turn_advance(self.turn, self.turn.saturating_add(1));
        self.turn = next_turn;
        let dirty = snapshot.total_dirty_items();
        self.last_dirty_items = dirty;

        if !land_audit_is_clean(dirty) {
            self.parked_done = false;
            let reason = if snapshot.running_bg_tasks > 0 {
                "background tasks still running"
            } else if snapshot.uncommitted_files > 0 {
                "uncommitted or untracked files in working tree"
            } else if snapshot.unpushed_commits > 0 {
                "local commits not pushed to remote main"
            } else if snapshot.unmerged_branches > 0 {
                "unmerged local branches remain"
            } else {
                "git stash entries remain"
            };
            return LandTurnAuditDecision::Continue {
                turn: next_turn,
                dirty_items: dirty,
                reason,
            };
        }

        if !valid_nothing_left_audit_defense(reply) {
            self.parked_done = false;
            return LandTurnAuditDecision::Continue {
                turn: next_turn,
                dirty_items: 0,
                reason: "reply does not defend clean main starting with 'Nothing left:'",
            };
        }

        self.parked_done = true;
        LandTurnAuditDecision::ParkDone { turn: next_turn }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_parking_until_git_is_clean_and_nothing_left_defense_is_concise() {
        let mut v = LandTurnAuditor::new();
        let dirty = LandTurnAuditSnapshot {
            uncommitted_files: 0,
            unpushed_commits: 1,
            unmerged_branches: 0,
            stash_entries: 0,
            running_bg_tasks: 0,
        };
        assert_eq!(
            v.evaluate_turn(&dirty, "Nothing left: pushed everything."),
            LandTurnAuditDecision::Continue {
                turn: 1,
                dirty_items: 1,
                reason: "local commits not pushed to remote main",
            }
        );
        assert!(!v.is_parked_done());

        let clean = LandTurnAuditSnapshot {
            uncommitted_files: 0,
            unpushed_commits: 0,
            unmerged_branches: 0,
            stash_entries: 0,
            running_bg_tasks: 0,
        };
        assert_eq!(
            v.evaluate_turn(&clean, "All done!"),
            LandTurnAuditDecision::Continue {
                turn: 2,
                dirty_items: 0,
                reason: "reply does not defend clean main starting with 'Nothing left:'",
            }
        );
        assert!(!v.is_parked_done());

        assert_eq!(
            v.evaluate_turn(
                &clean,
                "Nothing left: HEAD matches origin/main with clean working tree and zero stashes."
            ),
            LandTurnAuditDecision::ParkDone { turn: 3 }
        );
        assert!(v.is_parked_done());
        assert_eq!(v.last_dirty_items(), 0);
        assert_eq!(v.turn(), 3);
    }
}
