// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! AEAD transport frame-sequence exhaustion & proactive rekey guard
//! (`Astream.Aead.TlaSigmaTranscriptNonceGuard`).
//!
//! Guarantees that a single directional subkey never repeats a frame counter
//! (`frame_seq < hard_cap`, failing closed on counter exhaustion) and signals
//! `needs_rekey` as soon as `frame_seq >= soft_rekey_limit` so long-lived WAN
//! fabric links rotate subkeys seamlessly before hitting `hard_cap`.

#[cfg(clean_islands)]
#[path = "sigma_transcript_nonce_guard_island.rs"]
mod sigma_transcript_nonce_guard_island;
#[cfg(clean_islands)]
pub use sigma_transcript_nonce_guard_island::{aead_frame_seq_clamp, aead_rekey_epoch_advance};

/// Default soft rekey watermark (`1 << 32` frames).
pub const DEFAULT_SOFT_REKEY_FRAMES: u64 = 1u64 << 32;

/// Default hard frame ceiling (`(1 << 48) - 1`) before failing closed to prevent nonce reuse.
pub const DEFAULT_HARD_CAP_FRAMES: u64 = (1u64 << 48) - 1;

#[cfg(not(clean_islands))]
/// Monotonically advance the directional subkey rekey epoch.
#[must_use]
pub const fn aead_rekey_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp per-subkey frame sequence to `hard_cap`.
#[must_use]
pub const fn aead_frame_seq_clamp(cand_seq: u64, hard_cap: u64) -> u64 {
    if cand_seq < hard_cap {
        cand_seq
    } else {
        hard_cap
    }
}

contract_fn! {
    /// True iff `cur_seq < hard_cap` (at least one unique nonce remains).
    #[must_use]
    pub const fn aead_seq_below_cap(cur_seq: u64, hard_cap: u64) -> bool
    clauses [ensures result == (cur_seq < hard_cap)]
    {
        cur_seq < hard_cap
    }
}

/// Refusal when a subkey's frame counter reaches `hard_cap` without rekeying.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonceBudgetError {
    FrameCapExhausted { rekey_epoch: u64, hard_cap: u64 },
}

/// Allocated unique `(rekey_epoch, frame_nonce_seq, should_rekey_soon)` tuple.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllocatedFrameNonce {
    pub rekey_epoch: u64,
    pub frame_seq: u64,
    pub should_rekey_soon: bool,
}

/// Pure stack directional AEAD nonce-budget & rekey tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SigmaTranscriptNonceGuard {
    rekey_epoch: u64,
    frame_seq: u64,
    soft_rekey_limit: u64,
    hard_cap: u64,
}

impl Default for SigmaTranscriptNonceGuard {
    fn default() -> Self {
        Self::new(DEFAULT_SOFT_REKEY_FRAMES, DEFAULT_HARD_CAP_FRAMES)
    }
}

impl SigmaTranscriptNonceGuard {
    #[must_use]
    pub const fn new(soft_rekey_limit: u64, hard_cap: u64) -> Self {
        let cap = if hard_cap == 0 {
            DEFAULT_HARD_CAP_FRAMES
        } else {
            hard_cap
        };
        let soft = if soft_rekey_limit == 0 || soft_rekey_limit > cap {
            cap
        } else {
            soft_rekey_limit
        };
        Self {
            rekey_epoch: 0,
            frame_seq: 0,
            soft_rekey_limit: soft,
            hard_cap: cap,
        }
    }

    #[must_use]
    pub const fn rekey_epoch(&self) -> u64 {
        self.rekey_epoch
    }

    #[must_use]
    pub const fn frame_seq(&self) -> u64 {
        self.frame_seq
    }

    /// Allocate the next unique `(rekey_epoch, frame_seq)` pair, failing closed at `hard_cap`.
    pub fn next_nonce(&mut self) -> Result<AllocatedFrameNonce, NonceBudgetError> {
        if !aead_seq_below_cap(self.frame_seq, self.hard_cap) {
            return Err(NonceBudgetError::FrameCapExhausted {
                rekey_epoch: self.rekey_epoch,
                hard_cap: self.hard_cap,
            });
        }
        let allocated_seq = self.frame_seq;
        let cand_next = self.frame_seq.saturating_add(1);
        self.frame_seq = aead_frame_seq_clamp(cand_next, self.hard_cap);
        Ok(AllocatedFrameNonce {
            rekey_epoch: self.rekey_epoch,
            frame_seq: allocated_seq,
            should_rekey_soon: self.frame_seq >= self.soft_rekey_limit,
        })
    }

    /// Advance `rekey_epoch` and reset `frame_seq` to `0` after deriving a fresh subkey.
    pub fn commit_rekey(&mut self) -> u64 {
        let cand_ep = self.rekey_epoch.saturating_add(1);
        self.rekey_epoch = aead_rekey_epoch_advance(self.rekey_epoch, cand_ep);
        self.frame_seq = 0;
        self.rekey_epoch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signals_soft_rekey_and_fails_closed_at_hard_cap_until_rekeyed() {
        let mut g = SigmaTranscriptNonceGuard::new(2, 3);
        assert_eq!(
            g.next_nonce(),
            Ok(AllocatedFrameNonce {
                rekey_epoch: 0,
                frame_seq: 0,
                should_rekey_soon: false,
            })
        );
        assert_eq!(
            g.next_nonce(),
            Ok(AllocatedFrameNonce {
                rekey_epoch: 0,
                frame_seq: 1,
                should_rekey_soon: true,
            })
        );
        assert_eq!(
            g.next_nonce(),
            Ok(AllocatedFrameNonce {
                rekey_epoch: 0,
                frame_seq: 2,
                should_rekey_soon: true,
            })
        );
        // 4th frame at epoch 0 hits hard_cap = 3 -> fails closed!
        assert_eq!(
            g.next_nonce(),
            Err(NonceBudgetError::FrameCapExhausted {
                rekey_epoch: 0,
                hard_cap: 3,
            })
        );

        assert_eq!(g.commit_rekey(), 1);
        assert_eq!(
            g.next_nonce(),
            Ok(AllocatedFrameNonce {
                rekey_epoch: 1,
                frame_seq: 0,
                should_rekey_soon: false,
            })
        );
    }
}
