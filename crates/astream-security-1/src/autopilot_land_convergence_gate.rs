// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` `autopilot=land` convergence & `Nothing left:` turn-end arbiter
//! (`Astream.Agent.TlaAutopilotLandConvergence`).
//!
//! Enforces `aterm`'s `autopilot=land` harness contract:
//! - Never types while the operator is actively typing or has unsent input,
//! - Immediately parks on a reply to the operator's direct message answered within 10 minutes
//!   outside a harness-continued job,
//! - Continues every turn end while `git` reports uncommitted, unpushed, unmerged, or parked
//!   branch state (`!land_git_clean_b122(unlanded_total)`),
//! - Ends the session's work iff `unlanded_total == 0` AND the reply defends that starting with
//!   `Nothing left:`, monotonically advancing `landed_rev` via [`land_rev_advance_b122`].

#[cfg(clean_islands)]
#[path = "autopilot_land_convergence_gate_island.rs"]
mod autopilot_land_convergence_gate_island;
#[cfg(clean_islands)]
pub use autopilot_land_convergence_gate_island::{land_dirty_clamp_b122, land_rev_advance_b122};

#[cfg(not(clean_islands))]
/// Clamp unlanded git item count to `max_dirty`.
#[must_use]
pub const fn land_dirty_clamp_b122(cand_dirty: u64, max_dirty: u64) -> u64 {
    if cand_dirty < max_dirty {
        cand_dirty
    } else {
        max_dirty
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance verified landed revision watermark.
#[must_use]
pub const fn land_rev_advance_b122(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

contract_fn! {
    /// True iff `unlanded_count == 0` (nothing uncommitted, unpushed, unmerged, or parked).
    #[must_use]
    pub const fn land_git_clean_b122(unlanded_count: u64) -> bool
    clauses [ensures result == (unlanded_count == 0)]
    {
        unlanded_count == 0
    }
}

pub const DIRECT_REPLY_WINDOW_MS: u64 = 600_000; // 10 minutes
pub const MAX_TRACKED_UNLANDED_ITEMS: u64 = 10_000;
const NOTHING_LEFT_PREFIX: &[u8] = b"Nothing left:";

fn starts_with_nothing_left(reply_trimmed: &[u8]) -> bool {
    let mut pfx = NOTHING_LEFT_PREFIX;
    let mut rest = reply_trimmed;
    while let &[pb, ref ptail @ ..] = pfx {
        let &[rb, ref rtail @ ..] = rest else {
            return false;
        };
        if rb != pb {
            return false;
        }
        pfx = ptail;
        rest = rtail;
    }
    true
}

/// Decision emitted by `autopilot=land` at turn end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotLandDecision {
    HoldOperatorTypingOrUnsentInput,
    ParkDirectOperatorReply,
    DoneLanded { landed_rev: u64 },
    ContinueUnlandedGitState { pending_items: u64 },
    ContinueMissingNothingLeftDefense,
}

/// Stateful `autopilot=land` turn-end convergence gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AutopilotLandConvergenceGate {
    pending_items: u64,
    landed_rev: u64,
}

impl Default for AutopilotLandConvergenceGate {
    fn default() -> Self {
        Self::new()
    }
}

impl AutopilotLandConvergenceGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pending_items: 0,
            landed_rev: 0,
        }
    }

    #[must_use]
    pub const fn landed_rev(&self) -> u64 {
        self.landed_rev
    }

    /// Evaluate turn end under `autopilot=land`.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate_turn_end(
        &mut self,
        operator_has_unsent_input: bool,
        in_harness_continued_job: bool,
        is_reply_to_person_msg: bool,
        reply_elapsed_ms: u64,
        git_dirty_or_ahead_or_parked: u64,
        reply_trimmed_bytes: &[u8],
        cand_rev: u64,
    ) -> AutopilotLandDecision {
        if operator_has_unsent_input {
            return AutopilotLandDecision::HoldOperatorTypingOrUnsentInput;
        }
        if !in_harness_continued_job
            && is_reply_to_person_msg
            && reply_elapsed_ms <= DIRECT_REPLY_WINDOW_MS
        {
            return AutopilotLandDecision::ParkDirectOperatorReply;
        }

        self.pending_items =
            land_dirty_clamp_b122(git_dirty_or_ahead_or_parked, MAX_TRACKED_UNLANDED_ITEMS);
        if !land_git_clean_b122(self.pending_items) {
            return AutopilotLandDecision::ContinueUnlandedGitState {
                pending_items: self.pending_items,
            };
        }

        if starts_with_nothing_left(reply_trimmed_bytes) {
            self.landed_rev = land_rev_advance_b122(self.landed_rev, cand_rev);
            AutopilotLandDecision::DoneLanded {
                landed_rev: self.landed_rev,
            }
        } else {
            AutopilotLandDecision::ContinueMissingNothingLeftDefense
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn autopilot_land_enforces_git_clean_nothing_left_and_direct_reply_park() {
        let mut gate = AutopilotLandConvergenceGate::new();

        // Unsent operator input holds typing unconditionally.
        assert_eq!(
            gate.evaluate_turn_end(true, true, false, 100, 0, b"Nothing left: clean", 1),
            AutopilotLandDecision::HoldOperatorTypingOrUnsentInput
        );
        // Direct reply to operator within 10m outside harness job parks without typing.
        assert_eq!(
            gate.evaluate_turn_end(false, false, true, 120_000, 0, b"Here is the answer.", 1),
            AutopilotLandDecision::ParkDirectOperatorReply
        );
        // Claiming `Nothing left:` while git still has 2 unpushed commits continues!
        assert_eq!(
            gate.evaluate_turn_end(false, true, false, 5_000, 2, b"Nothing left: done", 2),
            AutopilotLandDecision::ContinueUnlandedGitState { pending_items: 2 }
        );
        // Clean git without `Nothing left:` defense continues!
        assert_eq!(
            gate.evaluate_turn_end(false, true, false, 5_000, 0, b"All done!", 2),
            AutopilotLandDecision::ContinueMissingNothingLeftDefense
        );
        // Clean git + `Nothing left:` defense lands and advances revision!
        assert_eq!(
            gate.evaluate_turn_end(
                false,
                true,
                false,
                5_000,
                0,
                b"Nothing left: main == origin/main, 0 dirty.",
                5
            ),
            AutopilotLandDecision::DoneLanded { landed_rev: 5 }
        );
    }
}
