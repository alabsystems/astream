// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` `Autopilot=Land` termination and person-reply parking verifier
//! (`Astream.Agent.TlaAutopilotLandVerifier`, Island #275).

#[cfg(clean_islands)]
#[path = "autopilot_land_verifier_island.rs"]
mod autopilot_land_verifier_island;
#[cfg(clean_islands)]
pub use autopilot_land_verifier_island::{land_dirty_bits_clamp, land_reply_elapsed_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_dirty_bits_clamp(bits: u64, cap: u64) -> u64 {
    if bits < cap {
        bits
    } else {
        cap
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_reply_elapsed_clamp(elapsed_ms: u64, window_ms: u64) -> u64 {
    if elapsed_ms < window_ms {
        elapsed_ms
    } else {
        window_ms
    }
}

/// Bit 0: uncommitted tracked or untracked changes remain in the working tree.
pub const DIRTY_UNCOMMITTED: u64 = 1 << 0;
/// Bit 1: local commits have not been pushed to `origin/main`.
pub const DIRTY_UNPUSHED: u64 = 1 << 1;
/// Bit 2: diverged or unmerged commits remain outside `origin/main`.
pub const DIRTY_UNMERGED: u64 = 1 << 2;
/// Bit 3: session work remains parked on a side branch or stash.
pub const DIRTY_PARKED_BRANCH: u64 = 1 << 3;
/// Bit 4: the agent reply defers remaining work for later.
pub const DIRTY_DEFERRED_WORK: u64 = 1 << 4;

/// Maximum valid 5-bit git cleanliness mask (`0x1F = 31`).
pub const MAX_DIRTY_MASK: u64 = 0x1F;

/// 10-minute window (`600_000` ms) within which a direct reply to a person's turn parks.
pub const PERSON_REPLY_WINDOW_MS: u64 = 600_000;

/// Maximum number of non-empty lines allowed in a concise `"Nothing left:"` defense.
pub const MAX_DEFENSE_LINES: usize = 8;

/// Prefix required at the start of a landing defense under `autopilot=land`.
pub const NOTHING_LEFT_PREFIX: &str = "Nothing left:";

contract_fn! {
    /// Verified check that every git/work cleanliness bit is zero (`dirty_mask == 0`),
    /// linked via `clean-kernel-defeq` to `land_git_all_clean_isl`.
    #[must_use]
    pub const fn land_git_all_clean(dirty_mask: u64) -> bool
    clauses [ensures result == (dirty_mask == 0)]
    {
        dirty_mask == 0
    }
}

contract_fn! {
    /// Verified check that a reply to a person's turn arrived within `window_ms`,
    /// linked via `clean-kernel-defeq` to `land_person_window_open_isl`.
    #[must_use]
    pub const fn land_person_window_open(elapsed_ms: u64, window_ms: u64) -> bool
    clauses [ensures result == (elapsed_ms <= window_ms)]
    {
        elapsed_ms <= window_ms
    }
}

/// Decision taken by the `autopilot=land` harness at turn end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LandDecision {
    /// Person is actively typing or holds unsent input; suppress harness typing.
    HoldForUnsentPersonInput,
    /// Turn answered the person's own message within 10 minutes outside a harness job; park.
    ParkPersonTurnReply,
    /// Work is 100% on `origin/main` (`dirty_mask == 0`) and defended with `"Nothing left:"`; park.
    ParkLandedComplete,
    /// Work remains unlanded (`dirty_mask != 0`) or lacks a valid `"Nothing left:"` defense; continue.
    ContinueLanding { dirty_mask: u64 },
}

const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C)
}

const fn trim_ascii_ws(mut s: &[u8]) -> &[u8] {
    while let [head, rest @ ..] = s {
        if is_ascii_ws(*head) {
            s = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = s {
        if is_ascii_ws(*last) {
            s = rest;
        } else {
            break;
        }
    }
    s
}

const fn strip_bytes_prefix<'a>(mut s: &'a [u8], mut pfx: &[u8]) -> Option<&'a [u8]> {
    while let Some((&pb, p_tail)) = pfx.split_first() {
        let Some((&sb, s_tail)) = s.split_first() else {
            return None;
        };
        if sb != pb {
            return None;
        }
        s = s_tail;
        pfx = p_tail;
    }
    Some(s)
}

/// Inspect a reply text to verify whether it starts with `"Nothing left:"` and stays concise.
#[must_use]
pub const fn has_valid_nothing_left_defense(reply: &str) -> bool {
    let trimmed = trim_ascii_ws(reply.as_bytes());
    let Some(after) = strip_bytes_prefix(trimmed, b"Nothing left:") else {
        return false;
    };
    if trim_ascii_ws(after).is_empty() {
        return false;
    }
    let mut non_empty_lines = 0usize;
    let mut line_has_non_ws = false;
    let mut cur = trimmed;
    while let [b, rest @ ..] = cur {
        if *b == b'\n' {
            if line_has_non_ws {
                non_empty_lines = non_empty_lines.saturating_add(1);
                if non_empty_lines > MAX_DEFENSE_LINES {
                    return false;
                }
                line_has_non_ws = false;
            }
        } else if !is_ascii_ws(*b) {
            line_has_non_ws = true;
        }
        cur = rest;
    }
    if line_has_non_ws {
        non_empty_lines = non_empty_lines.saturating_add(1);
        if non_empty_lines > MAX_DEFENSE_LINES {
            return false;
        }
    }
    non_empty_lines >= 1
}

/// Stateful `autopilot=land` turn evaluator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutopilotLandVerifier {
    dirty_mask: u64,
    parked: bool,
    continuing_harness_job: bool,
}

impl Default for AutopilotLandVerifier {
    fn default() -> Self {
        Self::new(true)
    }
}

impl AutopilotLandVerifier {
    /// Create a verifier (`continuing_harness_job = true` when already inside an active harness job).
    #[must_use]
    pub const fn new(continuing_harness_job: bool) -> Self {
        Self {
            dirty_mask: DIRTY_UNCOMMITTED,
            parked: false,
            continuing_harness_job,
        }
    }

    /// Clamped 5-bit cleanliness mask from the most recent `git` check.
    #[must_use]
    pub const fn dirty_mask(&self) -> u64 {
        self.dirty_mask
    }

    /// Whether the session has parked cleanly.
    #[must_use]
    pub const fn is_parked(&self) -> bool {
        self.parked
    }

    /// Whether the harness is actively continuing a landing job.
    #[must_use]
    pub const fn continuing_harness_job(&self) -> bool {
        self.continuing_harness_job
    }

    /// Evaluate a turn end given `raw_dirty_mask`, `reply`, `person_unsent_input`,
    /// `answering_person_prompt`, and `person_elapsed_ms`.
    pub fn evaluate_turn_end(
        &mut self,
        raw_dirty_mask: u64,
        reply: &str,
        person_unsent_input: bool,
        answering_person_prompt: bool,
        person_elapsed_ms: u64,
    ) -> LandDecision {
        let clamped_mask = land_dirty_bits_clamp(raw_dirty_mask, MAX_DIRTY_MASK);
        self.dirty_mask = clamped_mask;

        if person_unsent_input {
            return LandDecision::HoldForUnsentPersonInput;
        }

        if !self.continuing_harness_job && answering_person_prompt {
            let clamped_elapsed = land_reply_elapsed_clamp(
                person_elapsed_ms,
                PERSON_REPLY_WINDOW_MS.saturating_add(1),
            );
            if land_person_window_open(clamped_elapsed, PERSON_REPLY_WINDOW_MS) {
                self.parked = true;
                return LandDecision::ParkPersonTurnReply;
            }
        }

        if land_git_all_clean(clamped_mask) && has_valid_nothing_left_defense(reply) {
            self.parked = true;
            LandDecision::ParkLandedComplete
        } else {
            self.parked = false;
            self.continuing_harness_job = true;
            LandDecision::ContinueLanding {
                dirty_mask: clamped_mask,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn land_requires_both_zero_git_mask_and_concise_nothing_left_defense() {
        let mut v = AutopilotLandVerifier::new(true);
        assert!(v.continuing_harness_job());
        let d1 = v.evaluate_turn_end(
            DIRTY_UNPUSHED,
            "Nothing left: everything pushed to origin/main.",
            false,
            false,
            0,
        );
        assert_eq!(
            d1,
            LandDecision::ContinueLanding {
                dirty_mask: DIRTY_UNPUSHED
            }
        );
        assert!(!v.is_parked());

        let d2 = v.evaluate_turn_end(0, "All done, pushed to main.", false, false, 0);
        assert_eq!(d2, LandDecision::ContinueLanding { dirty_mask: 0 });
        assert!(!v.is_parked());

        let d3 = v.evaluate_turn_end(
            0,
            "Nothing left: HEAD matches origin/main at 6c4174c, working tree and stash clean.",
            false,
            false,
            0,
        );
        assert_eq!(d3, LandDecision::ParkLandedComplete);
        assert!(v.is_parked());
    }

    #[test]
    fn unsent_input_and_person_ten_minute_rule_behave_exact() {
        let mut v = AutopilotLandVerifier::new(false);
        assert_eq!(
            v.evaluate_turn_end(DIRTY_UNCOMMITTED, "working...", true, true, 1_000),
            LandDecision::HoldForUnsentPersonInput
        );
        assert_eq!(
            v.evaluate_turn_end(
                DIRTY_UNCOMMITTED,
                "Here is the explanation.",
                false,
                true,
                599_999
            ),
            LandDecision::ParkPersonTurnReply
        );
        assert!(v.is_parked());

        let mut slow = AutopilotLandVerifier::new(false);
        assert_eq!(
            slow.evaluate_turn_end(DIRTY_PARKED_BRANCH, "Late answer.", false, true, 600_001,),
            LandDecision::ContinueLanding {
                dirty_mask: DIRTY_PARKED_BRANCH
            }
        );
    }
}
