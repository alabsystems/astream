// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Single-writer `ControlToken` claim/grant handoff & trace-free non-holder refusal
//! (`evidence/manifest.toml` `term.fleet.control-handoff`;
//! `Astream.Engine.TlaControlTokenSingleWriterHandoff`).
//!
//! Enforces `Session::apply_input_as` / `Driver::drive_input_as` authority invariants:
//! - Exactly one `(active_gen, active_client_id)` holds write authority at any instant,
//! - A non-holder's `apply_input_as` or `grant` is refused with `RefusedNotHolder` BEFORE touching
//!   the PTY, session log, or `dedup_hw` watermark (leaving zero trace and zero sequence bump!),
//! - `claim` overrides authority unconditionally by advancing `active_gen`, invalidating all
//!   earlier `ControlToken`s immediately!

#[cfg(clean_islands)]
#[path = "control_token_single_writer_handoff_island.rs"]
mod control_token_single_writer_handoff_island;
#[cfg(clean_islands)]
pub use control_token_single_writer_handoff_island::{
    control_gen_advance_b144, holder_dedup_hw_advance_b144,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the session control-authority generation counter.
#[must_use]
pub const fn control_gen_advance_b144(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the active holder's deduplication high-water mark.
#[must_use]
pub const fn holder_dedup_hw_advance_b144(cur_hw: u64, cand_seq: u64) -> u64 {
    if cur_hw < cand_seq {
        cand_seq
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `token` matches both `active_gen` and `active_client_id`.
    #[must_use]
    pub const fn token_matches_active_holder_b144(
        token_gen: u64,
        active_gen: u64,
        token_client_id: u64,
        active_client_id: u64,
    ) -> bool
    clauses [ensures result == (token_gen == active_gen && token_client_id == active_client_id)]
    {
        token_gen == active_gen && token_client_id == active_client_id
    }
}

/// Capability-like single-writer token issued by `claim` or `grant`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HolderToken {
    pub gen: u64,
    pub client_id: u64,
}

/// Verdict for `apply_input_as` or `grant`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlHandoffVerdict {
    AdmittedFreshInput { dedup_hw: u64 },
    DroppedDuplicateInput { dedup_hw: u64 },
    GrantedNewHolder { token: HolderToken },
    RefusedNotHolder,
}

/// Single-writer `ControlToken` arbiter with trace-free non-holder rejection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SingleWriterControlGate {
    active_gen: u64,
    active_client_id: u64,
    holder_dedup_hw: u64,
}

impl SingleWriterControlGate {
    #[must_use]
    pub const fn new(initial_client_id: u64) -> (Self, HolderToken) {
        (
            Self {
                active_gen: 1,
                active_client_id: initial_client_id,
                holder_dedup_hw: 0,
            },
            HolderToken {
                gen: 1,
                client_id: initial_client_id,
            },
        )
    }

    #[must_use]
    pub const fn holder_dedup_hw(&self) -> u64 {
        self.holder_dedup_hw
    }

    /// Explicit override (`claim`): advances `active_gen`, revoking the old holder immediately.
    pub fn claim(&mut self, new_client_id: u64) -> HolderToken {
        let next_gen = self.active_gen.saturating_add(1);
        self.active_gen = control_gen_advance_b144(self.active_gen, next_gen);
        self.active_client_id = new_client_id;
        HolderToken {
            gen: self.active_gen,
            client_id: new_client_id,
        }
    }

    /// Cooperative transfer (`grant`): refused if `caller` is not the active holder!
    pub fn grant(&mut self, caller: HolderToken, target_client_id: u64) -> ControlHandoffVerdict {
        if !token_matches_active_holder_b144(
            caller.gen,
            self.active_gen,
            caller.client_id,
            self.active_client_id,
        ) {
            return ControlHandoffVerdict::RefusedNotHolder;
        }
        ControlHandoffVerdict::GrantedNewHolder {
            token: self.claim(target_client_id),
        }
    }

    /// Authorize `apply_input_as`: non-holders leave `holder_dedup_hw` untouched!
    pub fn apply_input_as(
        &mut self,
        caller: HolderToken,
        client_seq: u64,
    ) -> ControlHandoffVerdict {
        if !token_matches_active_holder_b144(
            caller.gen,
            self.active_gen,
            caller.client_id,
            self.active_client_id,
        ) {
            return ControlHandoffVerdict::RefusedNotHolder;
        }
        if client_seq <= self.holder_dedup_hw {
            return ControlHandoffVerdict::DroppedDuplicateInput {
                dedup_hw: self.holder_dedup_hw,
            };
        }
        self.holder_dedup_hw = holder_dedup_hw_advance_b144(self.holder_dedup_hw, client_seq);
        ControlHandoffVerdict::AdmittedFreshInput {
            dedup_hw: self.holder_dedup_hw,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_holder_input_and_grant_leave_dedup_watermark_untouched() {
        let (mut gate, t1) = SingleWriterControlGate::new(10);
        assert_eq!(
            gate.apply_input_as(t1, 1),
            ControlHandoffVerdict::AdmittedFreshInput { dedup_hw: 1 }
        );
        let t2 = gate.claim(20);
        // Revoked `t1` cannot write or grant, and never bumps `dedup_hw`:
        assert_eq!(
            gate.apply_input_as(t1, 99),
            ControlHandoffVerdict::RefusedNotHolder
        );
        assert_eq!(gate.grant(t1, 30), ControlHandoffVerdict::RefusedNotHolder);
        assert_eq!(gate.holder_dedup_hw(), 1);
        assert_eq!(
            gate.apply_input_as(t2, 2),
            ControlHandoffVerdict::AdmittedFreshInput { dedup_hw: 2 }
        );
    }
}
