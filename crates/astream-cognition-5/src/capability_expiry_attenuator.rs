// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotonic `exp=` deadline & `via=` attenuation verifier for `astream-cap`
//! (`Astream.Cap.TlaCapabilityExpiryAttenuator`).
//!
//! Enforces capability delegation invariants when `aterm` spawns worker tabs with attenuated
//! credentials: a delegated child capability's `exp=` deadline is clamped to `<= parent_exp`,
//! scope rights never widen (`(child_scope & !parent_scope) == 0`), and `verify_epoch` advances
//! monotonically.

#[cfg(clean_islands)]
#[path = "capability_expiry_attenuator_island.rs"]
mod capability_expiry_attenuator_island;
#[cfg(clean_islands)]
pub use capability_expiry_attenuator_island::{
    cap_child_exp_clamp_b117, cap_verify_epoch_advance_b117,
};

#[cfg(not(clean_islands))]
/// Clamp a delegated child capability expiry timestamp to `parent_exp`.
#[must_use]
pub const fn cap_child_exp_clamp_b117(requested_exp: u64, parent_exp: u64) -> u64 {
    if requested_exp < parent_exp {
        requested_exp
    } else {
        parent_exp
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `verify_epoch`.
#[must_use]
pub const fn cap_verify_epoch_advance_b117(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `now_secs` is strictly before `exp_secs` (`now_secs < exp_secs`).
    #[must_use]
    pub const fn cap_is_unexpired_b117(now_secs: u64, exp_secs: u64) -> bool
    clauses [ensures result == (now_secs < exp_secs)]
    {
        now_secs < exp_secs
    }
}

/// Result of verifying & attenuating a delegated subagent capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttenuationVerdict {
    Attenuated {
        effective_exp: u64,
        effective_scope_mask: u32,
        verify_epoch: u64,
    },
    RejectedExpired {
        now_secs: u64,
        effective_exp: u64,
    },
    RejectedScopeEscalation {
        parent_scope_mask: u32,
        requested_scope_mask: u32,
    },
    RejectedViaChainTooDeep {
        depth: u8,
        max_via_depth: u8,
    },
}

/// Stateful verifier enforcing `exp=` monotonicity and `via=` hop-depth bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapabilityExpiryAttenuator {
    max_via_depth: u8,
    verify_epoch: u64,
}

impl CapabilityExpiryAttenuator {
    #[must_use]
    pub const fn new(max_via_depth: u8) -> Self {
        let cap = if max_via_depth == 0 { 8 } else { max_via_depth };
        Self {
            max_via_depth: cap,
            verify_epoch: 0,
        }
    }

    #[must_use]
    pub const fn verify_epoch(&self) -> u64 {
        self.verify_epoch
    }

    /// Verify a delegated capability hop against `parent_exp`, `parent_scope_mask`, and `now_secs`.
    pub fn verify_delegation(
        &mut self,
        parent_exp: u64,
        requested_exp: u64,
        parent_scope_mask: u32,
        requested_scope_mask: u32,
        via_depth: u8,
        now_secs: u64,
    ) -> AttenuationVerdict {
        let next_ep = self.verify_epoch.saturating_add(1);
        self.verify_epoch = cap_verify_epoch_advance_b117(self.verify_epoch, next_ep);

        if via_depth > self.max_via_depth {
            return AttenuationVerdict::RejectedViaChainTooDeep {
                depth: via_depth,
                max_via_depth: self.max_via_depth,
            };
        }
        if (requested_scope_mask & !parent_scope_mask) != 0 {
            return AttenuationVerdict::RejectedScopeEscalation {
                parent_scope_mask,
                requested_scope_mask,
            };
        }
        let effective_exp = cap_child_exp_clamp_b117(requested_exp, parent_exp);
        if !cap_is_unexpired_b117(now_secs, effective_exp) {
            return AttenuationVerdict::RejectedExpired {
                now_secs,
                effective_exp,
            };
        }
        AttenuationVerdict::Attenuated {
            effective_exp,
            effective_scope_mask: requested_scope_mask & parent_scope_mask,
            verify_epoch: self.verify_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clamps_child_expiry_and_rejects_privilege_escalation() {
        let mut att = CapabilityExpiryAttenuator::new(4);
        assert_eq!(
            att.verify_delegation(2_000, 9_999, 0b0111, 0b0011, 1, 1_500),
            AttenuationVerdict::Attenuated {
                effective_exp: 2_000,
                effective_scope_mask: 0b0011,
                verify_epoch: 1,
            }
        );
        assert!(matches!(
            att.verify_delegation(2_000, 1_800, 0b0011, 0b0111, 1, 1_500),
            AttenuationVerdict::RejectedScopeEscalation { .. }
        ));
    }
}
