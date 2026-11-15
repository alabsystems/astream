// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-session SSH-agent signature-request budget capping remote `SSH2_AGENTC_SIGN_REQUEST` uses
//! so a compromised remote host cannot silently sign arbitrary challenges forever
//! (`Astream.SecVault.TlaSshAgentForwardingGate`).

#[cfg(clean_islands)]
#[path = "ssh_agent_forwarding_gate_island.rs"]
mod ssh_agent_forwarding_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_sig_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_sign_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ssh_agent_forwarding_gate_island::{sv_sig_clamp, sv_sign_advance};

/// Hard ceiling on forwarded SSH-agent signatures per grant (`64`).
pub const MAX_SSH_SIGN_BUDGET: u64 = 64;

contract_fn! {
    /// Verified remaining sign-budget check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sv_sign_within_budget_isl`.
    #[must_use]
    pub const fn sv_sign_within_budget(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct SshAgentSignGate {
    budget: u64,
    used: u64,
}

impl SshAgentSignGate {
    #[must_use]
    pub const fn new(budget: u64) -> Self {
        Self {
            budget: sv_sig_clamp(budget, MAX_SSH_SIGN_BUDGET),
            used: 0,
        }
    }

    pub fn try_consume_signature(&mut self) -> bool {
        let next = self.used.saturating_add(1);
        if sv_sign_within_budget(self.budget, next) {
            self.used = sv_sign_advance(self.used, next);
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
    fn exhausts_ssh_agent_sign_budget_deterministically() {
        let mut g = SshAgentSignGate::new(2);
        assert!(g.try_consume_signature());
        assert!(g.try_consume_signature());
        assert!(!g.try_consume_signature());
    }
}
