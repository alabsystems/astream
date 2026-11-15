// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Canonical `aterm` terminal session detector (`TERM_PROGRAM=aterm`, `ATERM_CHILD=1`, or a
//! non-empty `ATERM_SESSION_ID`; `Astream.EnvScrub.TlaAtermDetectProbe`).

#[cfg(clean_islands)]
#[path = "aterm_detect_probe_island.rs"]
mod aterm_detect_probe_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aterm_env_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aterm_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use aterm_detect_probe_island::{aterm_env_clamp, aterm_gen_advance};

/// Number of canonical environment signals (`TERM_PROGRAM`, `ATERM_CHILD`, `ATERM_SESSION_ID`).
pub const MAX_ATERM_SIGNALS: u64 = 3;

contract_fn! {
    /// Verified signal presence (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aterm_active_isl`.
    #[must_use]
    pub const fn aterm_active(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Evaluates the 3-way `aterm` primer detection predicate.
#[derive(Debug, Clone, Default)]
pub struct AtermSessionDetector {
    probes: u64,
}

impl AtermSessionDetector {
    #[must_use]
    pub const fn new() -> Self {
        Self { probes: 0 }
    }

    pub fn is_aterm_terminal(
        &mut self,
        term_program: Option<&str>,
        aterm_child: Option<&str>,
        aterm_session_id: Option<&str>,
    ) -> bool {
        let mut signals = 0u64;
        if term_program == Some("aterm") {
            signals = signals.saturating_add(1);
        }
        if aterm_child == Some("1") {
            signals = signals.saturating_add(1);
        }
        if let Some(sid) = aterm_session_id {
            if !sid.is_empty() {
                signals = signals.saturating_add(1);
            }
        }
        let clamped = aterm_env_clamp(signals, MAX_ATERM_SIGNALS);
        self.probes = aterm_gen_advance(self.probes, self.probes.saturating_add(1));
        aterm_active(clamped, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detector_activates_on_any_of_three_aterm_signals_and_ignores_none() {
        let mut d = AtermSessionDetector::new();
        assert!(!d.is_aterm_terminal(Some("Apple_Terminal"), None, Some("")));
        assert!(d.is_aterm_terminal(Some("aterm"), None, None));
        assert!(d.is_aterm_terminal(None, Some("1"), None));
        assert!(d.is_aterm_terminal(None, None, Some("sid-42")));
    }
}
