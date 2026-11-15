// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Managed `abrew` disabled-stub latch (`aterm` primer: *"Disabling compatibility retains the
//! managed stub and refuses commands; `on` and `status` remain available"* —
//! `Astream.Abrew.TlaDisabledStubLatch`).

#[cfg(clean_islands)]
#[path = "disabled_stub_latch_island.rs"]
mod disabled_stub_latch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_cmd_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_stub_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use disabled_stub_latch_island::{ab_cmd_clamp, ab_stub_advance};

/// Maximum verb clearance (`2`).
pub const MAX_STUB_CLEARANCE: u64 = 2;

contract_fn! {
    /// Verified stub verb permission (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ab_verb_permitted_isl`.
    #[must_use]
    pub const fn ab_verb_permitted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct AbrewStubState {
    compat_enabled: bool,
    calls: u64,
}

impl AbrewStubState {
    #[must_use]
    pub const fn new(compat_enabled: bool) -> Self {
        Self {
            compat_enabled,
            calls: 0,
        }
    }

    pub fn dispatch_verb(&mut self, verb: &str) -> bool {
        self.calls = ab_stub_advance(self.calls, self.calls.saturating_add(1));
        if verb == "on" {
            self.compat_enabled = true;
            return true;
        }
        if verb == "off" {
            self.compat_enabled = false;
            return true;
        }
        let clearance = if self.compat_enabled || verb == "status" {
            2u64
        } else {
            0u64
        };
        let clamped = ab_cmd_clamp(clearance, MAX_STUB_CLEARANCE);
        ab_verb_permitted(clamped, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disabled_stub_refuses_install_but_keeps_status_and_on_available() {
        let mut s = AbrewStubState::new(false);
        assert!(!s.dispatch_verb("install"));
        assert!(s.dispatch_verb("status"));
        assert!(s.dispatch_verb("on"));
        assert!(s.dispatch_verb("install"));
    }
}
