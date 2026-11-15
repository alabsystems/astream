// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `targo` explicit verification-lane enforcer (`aterm` primer: *"`targo --unverified <cmd>` builds
//! with no proof claim, `targo trust <cmd>` verifies, and a bare `targo build` is refused until a
//! lane is named"* — `Astream.AtpkgTc.TlaTargoLaneEnforcer`).

#[cfg(clean_islands)]
#[path = "targo_lane_enforcer_island.rs"]
mod targo_lane_enforcer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_lane_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_inv_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use targo_lane_enforcer_island::{tc_inv_advance, tc_lane_clamp};

/// Highest lane code (`0 = MissingLane`, `1 = Unverified`, `2 = TrustVerified`, `3 = ToolPassthrough`).
pub const MAX_TARGO_LANE: u64 = 3;

contract_fn! {
    /// Verified explicit-lane check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tc_lane_explicit_isl`.
    #[must_use]
    pub const fn tc_lane_explicit(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargoLane {
    MissingLane,
    Unverified,
    TrustVerified,
    ToolPassthrough,
}

#[derive(Debug, Clone, Default)]
pub struct TargoLaneParser {
    invocations: u64,
}

impl TargoLaneParser {
    #[must_use]
    pub const fn new() -> Self {
        Self { invocations: 0 }
    }

    pub fn classify_first_arg(&mut self, first_arg: &str) -> (TargoLane, bool) {
        let (lane, code) = match first_arg {
            "--unverified" => (TargoLane::Unverified, 1u64),
            "trust" => (TargoLane::TrustVerified, 2u64),
            "fmt" | "--version" | "-V" | "--help" | "-h" => (TargoLane::ToolPassthrough, 3u64),
            _ => (TargoLane::MissingLane, 0u64),
        };
        let clamped = tc_lane_clamp(code, MAX_TARGO_LANE);
        self.invocations = tc_inv_advance(self.invocations, self.invocations.saturating_add(1));
        (lane, tc_lane_explicit(clamped, 1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_bare_targo_build_and_accepts_trust_or_unverified_lanes() {
        let mut p = TargoLaneParser::new();
        assert_eq!(
            p.classify_first_arg("build"),
            (TargoLane::MissingLane, false)
        );
        assert_eq!(
            p.classify_first_arg("--unverified"),
            (TargoLane::Unverified, true)
        );
        assert_eq!(
            p.classify_first_arg("trust"),
            (TargoLane::TrustVerified, true)
        );
        assert_eq!(
            p.classify_first_arg("fmt"),
            (TargoLane::ToolPassthrough, true)
        );
    }
}
