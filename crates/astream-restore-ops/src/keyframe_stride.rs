// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Adaptive `ASOP` keyframe stride controller bounding worst-case VT tail fold cost between
//! crash-restore snapshots (`aterm-restore`, `Astream.Restore.TlaKeyframeStride`).

#[cfg(clean_islands)]
#[path = "keyframe_stride_island.rs"]
mod keyframe_stride_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kf_tail_bytes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kf_snapshot_off_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use keyframe_stride_island::{kf_snapshot_off_advance, kf_tail_bytes_clamp};

/// Hard ceiling on unfolded history bytes between crash-restore keyframes (`256` KiB).
pub const MAX_FOLD_TAIL_BYTES: u64 = 262_144;

contract_fn! {
    /// Verified stride trigger (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kf_due_at_tail_isl`.
    #[must_use]
    pub const fn kf_due_at_tail(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Adaptive crash-restore keyframe scheduler.
#[derive(Debug, Clone)]
pub struct KeyframeStrideController {
    stride_bytes: u64,
    last_snapshot_offset: u64,
    tail_bytes: u64,
}

impl KeyframeStrideController {
    #[must_use]
    pub const fn new(stride_bytes: u64) -> Self {
        let clamped = kf_tail_bytes_clamp(stride_bytes, MAX_FOLD_TAIL_BYTES);
        Self {
            stride_bytes: if clamped == 0 { 4096 } else { clamped },
            last_snapshot_offset: 0,
            tail_bytes: 0,
        }
    }

    #[must_use]
    pub const fn last_snapshot_offset(&self) -> u64 {
        self.last_snapshot_offset
    }

    /// Accumulates `chunk_len` bytes of recorded PTY history and returns `true` iff a fresh
    /// `Screen` keyframe must be emitted into the crash-restore region.
    pub fn record_output_chunk(&mut self, chunk_len: u64) -> bool {
        let next = self.tail_bytes.saturating_add(chunk_len);
        self.tail_bytes = kf_tail_bytes_clamp(next, MAX_FOLD_TAIL_BYTES);
        kf_due_at_tail(self.tail_bytes, self.stride_bytes)
    }

    /// Commits a keyframe folded through `offset`, resetting accumulated tail bytes.
    pub fn commit_keyframe(&mut self, offset: u64) -> u64 {
        self.last_snapshot_offset = kf_snapshot_off_advance(self.last_snapshot_offset, offset);
        self.tail_bytes = 0;
        self.last_snapshot_offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keyframe_stride_fires_at_tail_budget_and_advances_snapshot_monotonically() {
        let mut ctl = KeyframeStrideController::new(16_384);
        assert!(!ctl.record_output_chunk(10_000));
        assert!(ctl.record_output_chunk(8_000));
        assert_eq!(ctl.commit_keyframe(42), 42);
        assert_eq!(ctl.commit_keyframe(30), 42);
        assert!(!ctl.record_output_chunk(1_000));
    }
}
