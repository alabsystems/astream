// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Collision-Free Incremental `Screen` Checkpoint Deduplicator
//! (`Astream.Term.TlaScreenCheckpointDigest`).
//!
//! When `aterm-restore` periodically checkpoints dozens of idle and active terminal tabs,
//! writing identical full `Screen::serialize()` blobs on every tick amplifies SSD wear and
//! snapshot log churn. Hashing alone (`FNV`/`XXHash`) cannot safely elide checkpoints without
//! risking a 64-bit collision silently dropping a real terminal change.
//!
//! [`IncrementalScreenCheckpoint`] combines a fast 64-bit FNV-1a pre-filter with exact
//! `Screen::serialize()` byte comparison — upholding `s1 == s2 <=> s1.serialize() == s2.serialize()`
//! injectivity with zero false skips — while bounding retained baseline memory via Clean-origin
//! [`screen_ckpt_bytes_clamp`] and enforcing monotone checkpoint sequence numbers via
//! Clean-origin [`screen_ckpt_seq_advance`].

use astream_term::screen::Screen;

#[cfg(clean_islands)]
#[path = "screen_injectivity_island.rs"]
mod screen_injectivity_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn screen_ckpt_bytes_clamp(cand_bytes: u64, byte_cap: u64) -> u64 {
    if cand_bytes < byte_cap {
        cand_bytes
    } else {
        byte_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn screen_ckpt_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}
#[cfg(clean_islands)]
pub use screen_injectivity_island::{screen_ckpt_bytes_clamp, screen_ckpt_seq_advance};

/// Default retained baseline snapshot cap per tab (`4 MiB`).
pub const DEFAULT_SCREEN_CKPT_BYTE_CAP: u64 = 4 * 1024 * 1024;

contract_fn! {
    /// Kernel-certified check that `retained_bytes <= byte_cap`, linked via
    /// `clean-kernel-defeq` to `screen_ckpt_within_cap_isl`.
    #[must_use]
    pub const fn screen_ckpt_within_cap(retained_bytes: u64, byte_cap: u64) -> bool
    clauses [ensures result == (retained_bytes <= byte_cap)]
    {
        retained_bytes <= byte_cap
    }
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut cur = bytes;
    while let &[b, ref rest @ ..] = cur {
        h = (h ^ (b as u64)).wrapping_mul(0x0100_0000_01b3);
        cur = rest;
    }
    h
}

/// Decision returned when evaluating a candidate [`Screen`] for checkpointing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScreenCheckpointDecision {
    /// Exact byte match against the previously persisted checkpoint; write may be skipped.
    UnchangedSkip { last_ckpt_seq: u64 },
    /// `Screen` changed (or exceeded the retained baseline cache cap and therefore forces a
    /// fresh persisted checkpoint).
    EmitCheckpoint {
        ckpt_seq: u64,
        serialized: Vec<u8>,
        oversize_uncached: bool,
    },
}

/// Stateful per-tab checkpoint deduplicator backed by `Astream.Term.TlaScreenCheckpointDigest`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncrementalScreenCheckpoint {
    last_serialized: Option<Vec<u8>>,
    last_fast_tag: u64,
    retained_bytes: u64,
    byte_cap: u64,
    ckpt_seq: u64,
}

impl IncrementalScreenCheckpoint {
    /// Construct a deduplicator with `byte_cap` maximum retained baseline bytes.
    #[must_use]
    pub const fn new(byte_cap: u64) -> Self {
        Self {
            last_serialized: None,
            last_fast_tag: 0,
            retained_bytes: 0,
            byte_cap,
            ckpt_seq: 0,
        }
    }

    /// Construct a deduplicator with [`DEFAULT_SCREEN_CKPT_BYTE_CAP`] (`4 MiB`).
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(DEFAULT_SCREEN_CKPT_BYTE_CAP)
    }

    /// Currently retained baseline snapshot byte count (`<= byte_cap`).
    #[must_use]
    pub const fn retained_bytes(&self) -> u64 {
        self.retained_bytes
    }

    /// Monotone checkpoint sequence number of the last emitted snapshot.
    #[must_use]
    pub const fn ckpt_seq(&self) -> u64 {
        self.ckpt_seq
    }

    /// Drop any cached baseline bytes (forcing the next evaluation to emit a full checkpoint)
    /// while preserving monotone `ckpt_seq`.
    pub fn clear_cached_baseline(&mut self) {
        self.last_serialized = None;
        self.last_fast_tag = 0;
        self.retained_bytes = 0;
    }

    /// Evaluate a serialized `Screen` image (`Screen::serialize()`) and decide whether a new
    /// checkpoint must be persisted.
    pub fn evaluate_serialized(&mut self, serialized: Vec<u8>) -> ScreenCheckpointDecision {
        let tag = fnv1a64(&serialized);
        if let Some(prev) = &self.last_serialized {
            if self.last_fast_tag == tag && prev.as_slice() == serialized.as_slice() {
                return ScreenCheckpointDecision::UnchangedSkip {
                    last_ckpt_seq: self.ckpt_seq,
                };
            }
        }

        let cand_seq = self.ckpt_seq.saturating_add(1);
        let next_seq = screen_ckpt_seq_advance(self.ckpt_seq, cand_seq);
        self.ckpt_seq = next_seq;

        let raw_len = serialized.len() as u64;
        if raw_len <= self.byte_cap {
            self.retained_bytes = screen_ckpt_bytes_clamp(raw_len, self.byte_cap);
            self.last_fast_tag = tag;
            self.last_serialized = Some(serialized.clone());
            ScreenCheckpointDecision::EmitCheckpoint {
                ckpt_seq: next_seq,
                serialized,
                oversize_uncached: false,
            }
        } else {
            // Snapshot exceeds retained RAM budget: emit it faithfully and evict cached baseline
            // rather than retaining an unbounded buffer.
            self.last_serialized = None;
            self.last_fast_tag = 0;
            self.retained_bytes = screen_ckpt_bytes_clamp(0, self.byte_cap);
            ScreenCheckpointDecision::EmitCheckpoint {
                ckpt_seq: next_seq,
                serialized,
                oversize_uncached: true,
            }
        }
    }

    /// Serialize `screen` and evaluate whether a checkpoint write is required.
    pub fn evaluate_screen(&mut self, screen: &Screen) -> ScreenCheckpointDecision {
        self.evaluate_serialized(screen.serialize())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_identical_screen_and_emits_on_single_cell_mutation() {
        use astream_term::record::Record;
        use astream_term::screen::Folder;

        let mut ckpt = IncrementalScreenCheckpoint::with_defaults();
        let mut folder = Folder::new(80, 24);
        folder.apply(&Record::Out(b"hello aterm restore\r\n".to_vec()));
        let screen = folder.clone().into_screen();

        let first = ckpt.evaluate_screen(&screen);
        match first {
            ScreenCheckpointDecision::EmitCheckpoint {
                ckpt_seq,
                oversize_uncached,
                ..
            } => {
                assert_eq!(ckpt_seq, 1);
                assert!(!oversize_uncached);
            }
            ScreenCheckpointDecision::UnchangedSkip { .. } => panic!("expected first emit"),
        }
        assert!(screen_ckpt_within_cap(
            ckpt.retained_bytes(),
            DEFAULT_SCREEN_CKPT_BYTE_CAP
        ));

        assert_eq!(
            ckpt.evaluate_screen(&screen),
            ScreenCheckpointDecision::UnchangedSkip { last_ckpt_seq: 1 }
        );

        folder.apply(&Record::Out(b"!".to_vec()));
        let screen2 = folder.into_screen();
        match ckpt.evaluate_screen(&screen2) {
            ScreenCheckpointDecision::EmitCheckpoint { ckpt_seq, .. } => {
                assert_eq!(ckpt_seq, 2);
            }
            ScreenCheckpointDecision::UnchangedSkip { .. } => panic!("expected mutation emit"),
        }
    }

    #[test]
    fn oversize_snapshot_emits_without_exceeding_retained_byte_cap() {
        let mut ckpt = IncrementalScreenCheckpoint::new(16);
        let payload = vec![b'x'; 64];
        match ckpt.evaluate_serialized(payload) {
            ScreenCheckpointDecision::EmitCheckpoint {
                ckpt_seq,
                oversize_uncached,
                ..
            } => {
                assert_eq!(ckpt_seq, 1);
                assert!(oversize_uncached);
            }
            ScreenCheckpointDecision::UnchangedSkip { .. } => panic!("expected emit"),
        }
        assert_eq!(ckpt.retained_bytes(), 0);
        assert!(screen_ckpt_within_cap(ckpt.retained_bytes(), 16));
    }
}
