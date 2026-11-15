// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `autopilot=land` terminal completion verifier checking `Nothing left:` defense against live
//! `git` working-tree, index, unpushed-ahead, and parked-branch counts
//! (`aterm` primer, `Astream.Autopilot.TlaLandNothingLeft`).

#[cfg(clean_islands)]
#[path = "land_nothing_left_island.rs"]
mod land_nothing_left_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_dirty_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_land_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use land_nothing_left_island::{ap_dirty_clamp, ap_land_advance};

/// Maximum residual item count tracked in refusal diagnostics.
pub const MAX_LAND_RESIDUALS: u64 = 10_000;

contract_fn! {
    /// Verified zero-residual check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_land_clean_isl`.
    #[must_use]
    pub const fn ap_land_clean(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Verifies that an `autopilot=land` session has genuinely landed everything onto `origin/main`.
#[derive(Debug, Clone, Default)]
pub struct AutopilotLandVerifier {
    checks: u64,
}

fn has_needs_you_line(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut idx = 0usize;
    let mut at_line_start = true;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if b == b'\n' {
            at_line_start = true;
            idx = idx.saturating_add(1);
            continue;
        }
        if at_line_start {
            if b == b' ' || b == b'\t' || b == b'\r' {
                idx = idx.saturating_add(1);
                continue;
            }
            if bytes.get(idx..idx.saturating_add(10)) == Some(b"NEEDS YOU:") {
                return true;
            }
            at_line_start = false;
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl AutopilotLandVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks: 0 }
    }

    pub fn is_session_complete(
        &mut self,
        reply_text: &str,
        uncommitted_files: u64,
        unpushed_commits: u64,
        parked_branches: u64,
    ) -> bool {
        self.checks = ap_land_advance(self.checks, self.checks.saturating_add(1));
        let Some(rest) = reply_text.trim_start().strip_prefix("Nothing left:") else {
            return false;
        };
        if rest.trim().is_empty() || has_needs_you_line(reply_text) {
            return false;
        }
        let residual = uncommitted_files
            .saturating_add(unpushed_commits)
            .saturating_add(parked_branches);
        let clamped = ap_dirty_clamp(residual, MAX_LAND_RESIDUALS);
        ap_land_clean(0, clamped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn land_verifier_accepts_nothing_left_only_when_git_residuals_are_all_zero() {
        let mut v = AutopilotLandVerifier::new();
        assert!(!v.is_session_complete("Nothing left: all on main.", 0, 1, 0));
        assert!(!v.is_session_complete("All done!", 0, 0, 0));
        assert!(v.is_session_complete("Nothing left: pushed 2c42a8d to origin/main.", 0, 0, 0));
    }
}
