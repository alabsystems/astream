// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Stale `rustup` custom toolchain link detector matching `'rustc' is not installed for the custom
//! toolchain 'trust'` and prescribing `aterm pkg repair` (`Astream.AtpkgTc.TlaStaleTrustLinkProbe`).

#[cfg(clean_islands)]
#[path = "stale_trust_link_probe_island.rs"]
mod stale_trust_link_probe_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_err_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_rep_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use stale_trust_link_probe_island::{tc_err_clamp, tc_rep_advance};

/// Diagnostic match score (`1 = stale custom toolchain link`).
pub const STALE_LINK_MATCH: u64 = 1;

contract_fn! {
    /// Verified `aterm pkg repair` prescription check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tc_needs_pkg_repair_isl`.
    #[must_use]
    pub const fn tc_needs_pkg_repair(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct StaleTrustLinkProbe {
    repairs_recommended: u64,
}

fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    let mut idx = 0usize;
    while idx.saturating_add(needle.len()) <= haystack.len() {
        if haystack.get(idx..idx.saturating_add(needle.len())) == Some(needle) {
            return true;
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl StaleTrustLinkProbe {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            repairs_recommended: 0,
        }
    }

    pub fn needs_pkg_repair(&mut self, stderr_text: &str) -> bool {
        let matched = contains_bytes(
            stderr_text.as_bytes(),
            b"is not installed for the custom toolchain 'trust'",
        );
        let score = tc_err_clamp(if matched { 1 } else { 0 }, STALE_LINK_MATCH);
        if tc_needs_pkg_repair(score, STALE_LINK_MATCH) {
            self.repairs_recommended = tc_rep_advance(
                self.repairs_recommended,
                self.repairs_recommended.saturating_add(1),
            );
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_rustup_stale_trust_toolchain_link_diagnostic() {
        let mut p = StaleTrustLinkProbe::new();
        assert!(
            p.needs_pkg_repair("error: 'rustc' is not installed for the custom toolchain 'trust'")
        );
        assert!(!p.needs_pkg_repair("error[E0308]: mismatched types"));
    }
}
