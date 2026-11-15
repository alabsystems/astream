// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded pre-attach `Hello -> Nonce -> Attach` challenge ledger
//! (`Astream.Cap.TlaAttachNonceWindow`).
//!
//! Protects guarded brokers from pre-authentication slowloris nonce exhaustion and single-use
//! challenge replay by bounding live unanswered `Nonce` challenges (`outstanding <= max_live`)
//! and enforcing strictly monotone challenge sequence numbers (`nonce_seq_advance_b84`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "attach_nonce_window_island.rs"]
mod attach_nonce_window_island;
#[cfg(clean_islands)]
pub use attach_nonce_window_island::{nonce_outstanding_clamp, nonce_seq_advance_b84};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn nonce_seq_advance_b84(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn nonce_outstanding_clamp(cand_live: u64, max_live: u64) -> u64 {
    if cand_live < max_live {
        cand_live
    } else {
        max_live
    }
}

contract_fn! {
    /// Verified check whether an unanswered pre-attach nonce slot is available
    /// (`outstanding < max_live`), linked via `clean-kernel-defeq` to `nonce_slot_available_isl`.
    #[must_use]
    pub const fn nonce_slot_available(outstanding: u64, max_live: u64) -> bool
    clauses [ensures result == (outstanding < max_live)]
    {
        outstanding < max_live
    }
}

/// Default cap on unanswered pre-attach `Nonce` challenges (`256`).
pub const DEFAULT_MAX_LIVE_NONCES: u64 = 256;

/// Issued challenge entry awaiting a single `Attach` proof-of-possession.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PendingNonceEntry {
    pub seq: u64,
    pub issued_at_ms: u64,
    pub deadline_ms: u64,
}

/// Bounded single-use `Nonce` challenge window for `Attach` verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttachNonceWindow {
    max_live: u64,
    ttl_ms: u64,
    next_seq: u64,
    live: BTreeMap<u64, PendingNonceEntry>,
}

impl AttachNonceWindow {
    #[must_use]
    pub const fn new(max_live: u64, ttl_ms: u64) -> Self {
        let cap = if max_live == 0 {
            DEFAULT_MAX_LIVE_NONCES
        } else {
            max_live
        };
        let ttl = if ttl_ms == 0 { 5_000 } else { ttl_ms };
        Self {
            max_live: cap,
            ttl_ms: ttl,
            next_seq: 0,
            live: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn outstanding(&self) -> u64 {
        nonce_outstanding_clamp(self.live.len() as u64, self.max_live)
    }

    #[must_use]
    pub const fn next_seq(&self) -> u64 {
        self.next_seq
    }

    /// Evict expired challenges (`deadline_ms <= now_ms`) and return how many were reaped.
    pub fn evict_expired(&mut self, now_ms: u64) -> usize {
        let mut expired_seqs = Vec::new();
        for (&seq, entry) in &self.live {
            if entry.deadline_ms <= now_ms {
                expired_seqs.push(seq);
            }
        }
        let mut rest = expired_seqs.as_slice();
        let mut removed = 0usize;
        while let &[seq, ref tail @ ..] = rest {
            if self.live.remove(&seq).is_some() {
                removed = removed.saturating_add(1);
            }
            rest = tail;
        }
        removed
    }

    /// Issue a fresh monotone challenge sequence if capacity remains after reaping expired challenges.
    pub fn issue(&mut self, now_ms: u64) -> Option<PendingNonceEntry> {
        let _ = self.evict_expired(now_ms);
        let cur_out = self.outstanding();
        if !nonce_slot_available(cur_out, self.max_live) {
            return None;
        }
        let cand_seq = self.next_seq.saturating_add(1);
        let seq = nonce_seq_advance_b84(self.next_seq, cand_seq);
        self.next_seq = seq;
        let entry = PendingNonceEntry {
            seq,
            issued_at_ms: now_ms,
            deadline_ms: now_ms.saturating_add(self.ttl_ms),
        };
        self.live.insert(seq, entry);
        Some(entry)
    }

    /// Consume a challenge exactly once at `now_ms`, rejecting unknown, replayed, or expired `seq`.
    pub fn consume(&mut self, seq: u64, now_ms: u64) -> bool {
        let Some(entry) = self.live.remove(&seq) else {
            return false;
        };
        now_ms < entry.deadline_ms
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_single_use_ttl_and_max_live_window() {
        let mut win = AttachNonceWindow::new(2, 1_000);
        let c1 = win.issue(100).expect("slot 1");
        let c2 = win.issue(150).expect("slot 2");
        assert_eq!(c1.seq, 1);
        assert_eq!(c2.seq, 2);
        // Window full at t=200.
        assert_eq!(win.issue(200), None);

        // Single-use consumption succeeds once and rejects replay.
        assert!(win.consume(c1.seq, 500));
        assert!(!win.consume(c1.seq, 501));

        // Expired c2 fails closed and frees capacity at t=1200.
        assert!(!win.consume(c2.seq, 1_200));
        let c3 = win.issue(1_200).expect("slot 3");
        assert_eq!(c3.seq, 3);
    }
}
