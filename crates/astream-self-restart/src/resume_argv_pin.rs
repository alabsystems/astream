// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Conversation-resume context sealer binding `(conversation_id, cwd, argv)` across `aterm ctl
//! @self restart` so the respawned agent attaches to the exact conversation and workspace
//! (`Astream.SelfRst.TlaResumeArgvPin`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "resume_argv_pin_island.rs"]
mod resume_argv_pin_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_argc_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_pin_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use resume_argv_pin_island::{sr_argc_clamp, sr_pin_advance};

/// Maximum recorded argv count (`128`).
pub const MAX_RESUME_ARGC: u64 = 128;

contract_fn! {
    /// Verified resume-seal match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sr_resume_intact_isl`.
    #[must_use]
    pub const fn sr_resume_intact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ResumeContextPin {
    seal: [u8; 32],
    generation: u64,
}

impl ResumeContextPin {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            seal: [0u8; 32],
            generation: 0,
        }
    }

    #[must_use]
    fn compute_seal(conv_id: &[u8], cwd: &[u8], argc: u64) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update_slice(b"aterm-self-restart-v1:");
        h.update_slice(&(conv_id.len() as u64).to_le_bytes());
        h.update_slice(conv_id);
        h.update_slice(&(cwd.len() as u64).to_le_bytes());
        h.update_slice(cwd);
        h.update_slice(&argc.to_le_bytes());
        h.finalize()
    }

    pub fn pin_context(&mut self, conv_id: &[u8], cwd: &[u8], argc: u64) {
        if conv_id.is_empty() || cwd.is_empty() || argc > MAX_RESUME_ARGC {
            return;
        }
        let c = sr_argc_clamp(argc, MAX_RESUME_ARGC);
        self.seal = Self::compute_seal(conv_id, cwd, c);
        self.generation = sr_pin_advance(self.generation, self.generation.saturating_add(1));
    }

    #[must_use]
    pub fn verify_resume(&self, conv_id: &[u8], cwd: &[u8], argc: u64) -> bool {
        if conv_id.is_empty() || cwd.is_empty() || argc > MAX_RESUME_ARGC {
            return false;
        }
        let c = sr_argc_clamp(argc, MAX_RESUME_ARGC);
        let cand = Self::compute_seal(conv_id, cwd, c);
        let eq = self.generation > 0 && ct_eq(&self.seal, &cand);
        sr_resume_intact(if eq { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verifies_exact_conversation_and_cwd_across_restart() {
        let mut p = ResumeContextPin::new();
        p.pin_context(b"conv-123", b"/fixture-home/astream", 4);
        assert!(p.verify_resume(b"conv-123", b"/fixture-home/astream", 4));
        assert!(!p.verify_resume(b"conv-999", b"/fixture-home/astream", 4));
    }
}
