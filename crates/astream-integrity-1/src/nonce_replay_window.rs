// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Two-Phase 128-Packet Sliding Anti-Replay Window (`Astream.Aead.TlaAntiReplayWindow`).
//!
//! When AEAD-sealed frames traverse unordered or multipath WAN/relay paths, strict `seq == n + 1`
//! counters drop legitimate reordered datagrams, whereas mutating the replay window *before*
//! Poly1305 tag verification lets a single spoofed high-sequence packet advance `window_hi` and
//! blackhole legitimate traffic.
//!
//! [`SlidingReplayWindow`] separates pre-decryption screening from post-authentication commit:
//! 1. [`SlidingReplayWindow::check_before_open`] is pure/read-only (except optional bounded
//!    rejection telemetry via Clean-origin [`replay_reject_clamp`]), rejecting replays and packets
//!    older than `window_hi - 127` before cipher work runs.
//! 2. [`SlidingReplayWindow::commit_authenticated`] runs *only* after AEAD tag authentication
//!    succeeds, advancing `window_hi` monotonically via Clean-origin [`replay_hi_advance`] and
//!    marking the 128-slot `(lo_bits, hi_bits)` bitmap.

#![allow(
    clippy::assign_op_pattern,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::question_mark
)]

#[cfg(clean_islands)]
#[path = "nonce_replay_window_island.rs"]
mod nonce_replay_window_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replay_reject_clamp(cand_rejects: u64, reject_cap: u64) -> u64 {
    if cand_rejects < reject_cap {
        cand_rejects
    } else {
        reject_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replay_hi_advance(cur_hi: u64, cand_seq: u64) -> u64 {
    if cur_hi < cand_seq {
        cand_seq
    } else {
        cur_hi
    }
}
#[cfg(clean_islands)]
pub use nonce_replay_window_island::{replay_hi_advance, replay_reject_clamp};

/// Width of the sliding anti-replay bitmap (`128` sequence numbers: `0..=127` behind `window_hi`).
pub const REPLAY_WINDOW_BITS: u64 = 128;

/// Default cap on tracked replay-rejection telemetry.
pub const DEFAULT_REPLAY_REJECT_CAP: u64 = 1_000_000;

contract_fn! {
    /// Kernel-certified check that `rejects <= reject_cap`, linked via
    /// `clean-kernel-defeq` to `replay_rejects_within_cap_isl`.
    #[must_use]
    pub const fn replay_rejects_within_cap(rejects: u64, reject_cap: u64) -> bool
    clauses [ensures result == (rejects <= reject_cap)]
    {
        rejects <= reject_cap
    }
}

/// Reason a candidate frame sequence number was rejected by [`SlidingReplayWindow`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayReject {
    /// `seq == u64::MAX` is reserved as nonce-exhaustion sentinel and never accepted.
    ExhaustedMaxNonce,
    /// `seq + 127 < window_hi`: packet fell behind the 128-slot trailing window.
    TooOld { seq: u64, window_hi: u64 },
    /// `seq` was already authenticated and marked inside the current 128-slot window.
    DuplicateReplay { seq: u64 },
}

fn bit_for_delta_in_word(bit_idx: u32) -> u64 {
    match 1u64.checked_shl(bit_idx) {
        Some(mask) => mask,
        None => 0,
    }
}

/// Two-phase 128-slot anti-replay window backed by `Astream.Aead.TlaAntiReplayWindow`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlidingReplayWindow {
    initialized: bool,
    window_hi: u64,
    /// Bitmap for deltas `0..64` (`delta = window_hi - seq`), bit `0` = `window_hi`.
    recent_lo: u64,
    /// Bitmap for deltas `64..128` (`bit = delta - 64`).
    recent_hi: u64,
    reject_count: u64,
    reject_cap: u64,
}

impl SlidingReplayWindow {
    /// Construct an empty anti-replay window with `reject_cap`.
    #[must_use]
    pub const fn new(reject_cap: u64) -> Self {
        Self {
            initialized: false,
            window_hi: 0,
            recent_lo: 0,
            recent_hi: 0,
            reject_count: 0,
            reject_cap,
        }
    }

    /// Construct an anti-replay window with [`DEFAULT_REPLAY_REJECT_CAP`].
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(DEFAULT_REPLAY_REJECT_CAP)
    }

    /// Highest authenticated packet sequence number observed (`0` if uninitialized).
    #[must_use]
    pub const fn window_hi(&self) -> u64 {
        self.window_hi
    }

    /// Clamped count of rejected replay/stale sequence checks (`<= reject_cap`).
    #[must_use]
    pub const fn reject_count(&self) -> u64 {
        self.reject_count
    }

    fn is_delta_marked(&self, delta: u64) -> bool {
        if delta < 64 {
            let mask = bit_for_delta_in_word(delta as u32);
            (self.recent_lo & mask) != 0
        } else if delta < REPLAY_WINDOW_BITS {
            let hi_idx = delta.saturating_sub(64) as u32;
            let mask = bit_for_delta_in_word(hi_idx);
            (self.recent_hi & mask) != 0
        } else {
            true
        }
    }

    fn shift_window_up(&mut self, shift: u64) {
        if shift == 0 {
            return;
        }
        if shift >= REPLAY_WINDOW_BITS {
            self.recent_lo = 0;
            self.recent_hi = 0;
            return;
        }
        if shift >= 64 {
            let rem = shift.saturating_sub(64) as u32;
            self.recent_hi = match self.recent_lo.checked_shl(rem) {
                Some(v) => v,
                None => 0,
            };
            self.recent_lo = 0;
        } else {
            let s = shift as u32;
            let inv = 64u32.saturating_sub(s);
            let hi_shifted = match self.recent_hi.checked_shl(s) {
                Some(v) => v,
                None => 0,
            };
            let carry = match self.recent_lo.checked_shr(inv) {
                Some(v) => v,
                None => 0,
            };
            let lo_shifted = match self.recent_lo.checked_shl(s) {
                Some(v) => v,
                None => 0,
            };
            self.recent_hi = hi_shifted | carry;
            self.recent_lo = lo_shifted;
        }
    }

    /// Screen `seq` *before* running AEAD decryption without advancing `window_hi` or marking bits.
    pub fn check_before_open(&mut self, seq: u64) -> Result<(), ReplayReject> {
        if seq == u64::MAX {
            self.reject_count =
                replay_reject_clamp(self.reject_count.saturating_add(1), self.reject_cap);
            return Err(ReplayReject::ExhaustedMaxNonce);
        }
        if !self.initialized || seq > self.window_hi {
            return Ok(());
        }
        let delta = self.window_hi.saturating_sub(seq);
        if delta >= REPLAY_WINDOW_BITS {
            self.reject_count =
                replay_reject_clamp(self.reject_count.saturating_add(1), self.reject_cap);
            return Err(ReplayReject::TooOld {
                seq,
                window_hi: self.window_hi,
            });
        }
        if self.is_delta_marked(delta) {
            self.reject_count =
                replay_reject_clamp(self.reject_count.saturating_add(1), self.reject_cap);
            return Err(ReplayReject::DuplicateReplay { seq });
        }
        Ok(())
    }

    /// Commit `seq` *after* AEAD tag authentication succeeds, advancing `window_hi` monotonically
    /// and marking `seq` as seen.
    pub fn commit_authenticated(&mut self, seq: u64) -> Result<u64, ReplayReject> {
        if let Err(e) = self.check_before_open(seq) {
            return Err(e);
        }
        if !self.initialized {
            self.initialized = true;
            self.window_hi = seq;
            self.recent_lo = 1;
            self.recent_hi = 0;
            return Ok(self.window_hi);
        }

        if seq > self.window_hi {
            let next_hi = replay_hi_advance(self.window_hi, seq);
            let shift = next_hi.saturating_sub(self.window_hi);
            self.shift_window_up(shift);
            self.window_hi = next_hi;
            self.recent_lo = self.recent_lo | (1);
            return Ok(self.window_hi);
        }

        let delta = self.window_hi.saturating_sub(seq);
        if delta < 64 {
            self.recent_lo = self.recent_lo | (bit_for_delta_in_word(delta as u32));
        } else {
            self.recent_hi =
                self.recent_hi | (bit_for_delta_in_word(delta.saturating_sub(64) as u32));
        }
        Ok(self.window_hi)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unauthenticated_check_does_not_poison_window_and_128_bit_slide_rejects_replays() {
        let mut w = SlidingReplayWindow::new(10);
        // Spoofed high packet passes pre-check, fails AEAD outside, never committed -> window_hi stays 0!
        assert_eq!(w.check_before_open(5000), Ok(()));
        assert_eq!(w.window_hi(), 0);

        // Genuine packet 100 commits.
        assert_eq!(w.commit_authenticated(100), Ok(100));
        assert_eq!(
            w.commit_authenticated(100),
            Err(ReplayReject::DuplicateReplay { seq: 100 })
        );

        // Advance to 200 (shift by 100 -> 100 sits at delta 100 inside recent_hi!).
        assert_eq!(w.commit_authenticated(200), Ok(200));
        assert_eq!(
            w.commit_authenticated(100),
            Err(ReplayReject::DuplicateReplay { seq: 100 })
        );
        // Out-of-order 105 (delta 95) and 199 (delta 1) both succeed once and reject replay!
        assert_eq!(w.commit_authenticated(105), Ok(200));
        assert_eq!(w.commit_authenticated(199), Ok(200));
        assert_eq!(
            w.commit_authenticated(105),
            Err(ReplayReject::DuplicateReplay { seq: 105 })
        );

        // Boundary: 200 - 127 = 73 is inside window; 72 (delta 128) is TooOld!
        assert_eq!(w.commit_authenticated(73), Ok(200));
        assert_eq!(
            w.commit_authenticated(72),
            Err(ReplayReject::TooOld {
                seq: 72,
                window_hi: 200,
            })
        );
        assert!(replay_rejects_within_cap(w.reject_count(), 10));
    }
}
