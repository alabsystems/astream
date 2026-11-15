// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-restart handoff checkpoint verifier (`aterm` primer: *"When your agent needs restarting
//! (including to adopt an installed update), do it yourself: save your work and a handoff, read
//! `aterm ctl @self status` and `aterm ctl help restart`, then run `aterm ctl @self restart`"*)
//! refusing `@self restart` until a non-empty handoff note is persisted (`Astream.SelfRst.TlaHandoffSealGate`).

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

use astream_digest::Sha256;

#[cfg(clean_islands)]
#[path = "handoff_seal_gate_island.rs"]
mod handoff_seal_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_bytes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_seal_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use handoff_seal_gate_island::{sr_bytes_clamp, sr_seal_advance};

/// Maximum handoff note length (`262_144` bytes).
pub const MAX_HANDOFF_BYTES: u64 = 262_144;

contract_fn! {
    /// Verified non-empty handoff seal (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sr_handoff_ready_isl`.
    #[must_use]
    pub const fn sr_handoff_ready(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct HandoffSealGate {
    sealed_len: u64,
    digest: [u8; 32],
    epoch: u64,
}

impl HandoffSealGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sealed_len: 0,
            digest: [0u8; 32],
            epoch: 0,
        }
    }

    pub fn record_handoff(&mut self, handoff_markdown: &[u8], status_read: bool) -> bool {
        if !status_read || (handoff_markdown.len() as u64) > MAX_HANDOFF_BYTES {
            return false;
        }
        let mut non_ws = 0u64;
        for &b in handoff_markdown {
            if !b.is_ascii_whitespace() {
                non_ws = non_ws.saturating_add(1);
            }
        }
        if non_ws == 0 {
            return false;
        }
        let len = sr_bytes_clamp(handoff_markdown.len() as u64, MAX_HANDOFF_BYTES);
        if !sr_handoff_ready(len, 16) {
            return false;
        }
        self.sealed_len = len;
        self.digest = Sha256::digest_slice(handoff_markdown);
        self.epoch = sr_seal_advance(self.epoch, self.epoch.saturating_add(1));
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requires_status_read_and_nontrivial_handoff_before_self_restart() {
        let mut g = HandoffSealGate::new();
        assert!(!g.record_handoff(b"handoff summary ready for resume", false));
        assert!(!g.record_handoff(b"short", true));
        assert!(g.record_handoff(b"handoff summary ready for resume", true));
    }
}
