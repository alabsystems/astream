// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Guard blocking `defaults read <domain>` invocations on foreign macOS application domains that
//! pop modal TCC consent boxes (`aterm` primer: *"any `defaults` domain, another app's container"*
//! — `Astream.MacTcc.TlaDefaultsDomainGuard`).

#[cfg(clean_islands)]
#[path = "defaults_domain_guard_island.rs"]
mod defaults_domain_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_dom_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_dom_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use defaults_domain_guard_island::{tcc_dom_advance, tcc_dom_clamp};

/// Domain risk score ceiling (`0 = explicitly requested own domain`, `1 = foreign domain`).
pub const MAX_DOMAIN_RISK: u64 = 1;

contract_fn! {
    /// Verified domain safety predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tcc_domain_allowed_isl`.
    #[must_use]
    pub const fn tcc_domain_allowed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct DefaultsDomainGuard {
    inspected: u64,
}

impl DefaultsDomainGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { inspected: 0 }
    }

    pub fn allow_defaults_domain(&mut self, domain: &str, operator_explicitly_asked: bool) -> bool {
        // Every `defaults` domain is another app's data: the same risk, named or not.
        if domain.trim().is_empty() {
            self.inspected = tcc_dom_advance(self.inspected, self.inspected.saturating_add(1));
            return false;
        }
        let risk = 1u64;
        let clamped_risk = tcc_dom_clamp(risk, MAX_DOMAIN_RISK);
        let budget = if operator_explicitly_asked {
            1u64
        } else {
            0u64
        };
        self.inspected = tcc_dom_advance(self.inspected, self.inspected.saturating_add(1));
        tcc_domain_allowed(budget, clamped_risk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_unprompted_defaults_domain_reads() {
        let mut g = DefaultsDomainGuard::new();
        assert!(!g.allow_defaults_domain("com.apple.Safari", false));
        assert!(g.allow_defaults_domain("dev.aterm.app", true));
    }
}
