// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Policy classifier enforcing the `aterm` primer rule: *"An agent restart is not a `NEEDS YOU`
//! item; a Mac restart still is"* (`Astream.SelfRst.TlaAgentNotNeedsYou`).

#[cfg(clean_islands)]
#[path = "agent_not_needs_you_island.rs"]
mod agent_not_needs_you_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_kind_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_cls_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use agent_not_needs_you_island::{sr_cls_advance, sr_kind_clamp};

/// Action kind cap (`0 = SelfAgentRestart`, `1 = MacOsKernelRestart`, `2 = MissingCredential`, `3 = PhysicalAccess`).
pub const MAX_RECOVERY_KIND: u64 = 3;

contract_fn! {
    /// Verified human-attention requirement (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sr_requires_person_isl`.
    #[must_use]
    pub const fn sr_requires_person(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryAction {
    SelfAgentRestart,
    MacOsKernelRestart,
    MissingCredential,
    PhysicalAccess,
}

#[derive(Debug, Clone, Default)]
pub struct NeedsYouPolicy {
    classified: u64,
}

impl NeedsYouPolicy {
    #[must_use]
    pub const fn new() -> Self {
        Self { classified: 0 }
    }

    pub fn emits_needs_you(&mut self, action: RecoveryAction) -> bool {
        let code = match action {
            RecoveryAction::SelfAgentRestart => 0u64,
            RecoveryAction::MacOsKernelRestart => 1u64,
            RecoveryAction::MissingCredential => 2u64,
            RecoveryAction::PhysicalAccess => 3u64,
        };
        let clamped = sr_kind_clamp(code, MAX_RECOVERY_KIND);
        self.classified = sr_cls_advance(self.classified, self.classified.saturating_add(1));
        sr_requires_person(clamped, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_agent_restart_never_raises_needs_you_while_mac_restart_does() {
        let mut p = NeedsYouPolicy::new();
        assert!(!p.emits_needs_you(RecoveryAction::SelfAgentRestart));
        assert!(p.emits_needs_you(RecoveryAction::MacOsKernelRestart));
        assert!(p.emits_needs_you(RecoveryAction::MissingCredential));
    }
}
