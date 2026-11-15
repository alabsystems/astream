// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-layer (sealed AEAD + inner wire frame) frame-atomic idle-timeout resume cursor
//! (`evidence/manifest.toml` `broker.drain-idle-window-frame-atomic`;
//! `Astream.Aead.TlaFrameAtomicIdleStopCursor`).
//!
//! Guarantees that `Subscription::set_read_timeout` stops cleanly even when a `TimedOut`/`WouldBlock`
//! read interrupts BOTH a 64 KiB sealed AEAD record AND a 200 KiB inner `astream-wire` frame:
//! - Partial ciphertext bytes (`sealed_partial`) and already-opened plaintext prefix bytes
//!   (`inner_partial`) are retained in-place without advancing the AEAD open nonce past an
//!   unopened record,
//! - `TimedOut` returns `IdlePausePreservedPartial`, whereas `EOF` while either partial buffer is
//!   non-empty returns `UnexpectedEofMidFrame`!

#[cfg(clean_islands)]
#[path = "frame_atomic_idle_stop_cursor_island.rs"]
mod frame_atomic_idle_stop_cursor_island;
#[cfg(clean_islands)]
pub use frame_atomic_idle_stop_cursor_island::{
    inner_frame_partial_clamp_b146, sealed_partial_clamp_b146,
};

/// Maximum single sealed AEAD wire chunk (`64 KiB + 20 B` header/tag).
pub const MAX_SEALED_CHUNK_WIRE_BYTES: u64 = 65_556;
/// Maximum inner `astream-wire` frame (`16 MiB + 12 B`).
pub const MAX_INNER_WIRE_FRAME_BYTES: u64 = 16 * 1024 * 1024 + 12;

#[cfg(not(clean_islands))]
/// Clamp buffered partial sealed-record wire bytes to `sealed_cap`.
#[must_use]
pub const fn sealed_partial_clamp_b146(cand_sealed: u64, sealed_cap: u64) -> u64 {
    if cand_sealed < sealed_cap {
        cand_sealed
    } else {
        sealed_cap
    }
}

#[cfg(not(clean_islands))]
/// Clamp buffered partial inner wire-frame bytes to `inner_cap`.
#[must_use]
pub const fn inner_frame_partial_clamp_b146(cand_inner: u64, inner_cap: u64) -> u64 {
    if cand_inner < inner_cap {
        cand_inner
    } else {
        inner_cap
    }
}

contract_fn! {
    /// True iff both the outer AEAD recv buffer and inner wire-frame buffer sit at a clean boundary.
    #[must_use]
    pub const fn at_clean_dual_layer_boundary_b146(
        sealed_partial: u64,
        inner_partial: u64,
    ) -> bool
    clauses [ensures result == (sealed_partial == 0 && inner_partial == 0)]
    {
        sealed_partial == 0 && inner_partial == 0
    }
}

/// Outcome of a read step across the dual sealed/wire receive buffers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DualLayerReadOutcome {
    IdlePausePreservedPartial {
        sealed_partial: u64,
        inner_partial: u64,
    },
    CleanEofAtFrameBoundary,
    UnexpectedEofMidFrame {
        sealed_partial: u64,
        inner_partial: u64,
    },
    CompletedWholeFrame {
        frame_bytes: u64,
    },
}

/// Dual-layer partial-frame cursor across sealed TCP and `astream-wire` framing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameAtomicIdleCursor {
    sealed_partial: u64,
    inner_partial: u64,
}

impl FrameAtomicIdleCursor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sealed_partial: 0,
            inner_partial: 0,
        }
    }

    pub fn on_read_timeout(&mut self, raw_sealed: u64, raw_inner: u64) -> DualLayerReadOutcome {
        self.sealed_partial = sealed_partial_clamp_b146(raw_sealed, MAX_SEALED_CHUNK_WIRE_BYTES);
        self.inner_partial = inner_frame_partial_clamp_b146(raw_inner, MAX_INNER_WIRE_FRAME_BYTES);
        DualLayerReadOutcome::IdlePausePreservedPartial {
            sealed_partial: self.sealed_partial,
            inner_partial: self.inner_partial,
        }
    }

    #[must_use]
    pub const fn on_eof(&self) -> DualLayerReadOutcome {
        if at_clean_dual_layer_boundary_b146(self.sealed_partial, self.inner_partial) {
            DualLayerReadOutcome::CleanEofAtFrameBoundary
        } else {
            DualLayerReadOutcome::UnexpectedEofMidFrame {
                sealed_partial: self.sealed_partial,
                inner_partial: self.inner_partial,
            }
        }
    }

    pub fn complete_inner_frame(&mut self, frame_bytes: u64) -> DualLayerReadOutcome {
        self.sealed_partial = 0;
        self.inner_partial = 0;
        DualLayerReadOutcome::CompletedWholeFrame { frame_bytes }
    }
}

impl Default for FrameAtomicIdleCursor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timeout_mid_sealed_and_mid_frame_resumes_whole_whereas_eof_mid_frame_errors() {
        let mut c = FrameAtomicIdleCursor::new();
        assert_eq!(c.on_eof(), DualLayerReadOutcome::CleanEofAtFrameBoundary);

        // Timeout 150 KB into a 200 KB record (18 KB into 3rd sealed chunk):
        assert_eq!(
            c.on_read_timeout(18_432, 131_072),
            DualLayerReadOutcome::IdlePausePreservedPartial {
                sealed_partial: 18_432,
                inner_partial: 131_072
            }
        );
        // EOF right there is classified as `UnexpectedEofMidFrame`, never clean close!
        assert_eq!(
            c.on_eof(),
            DualLayerReadOutcome::UnexpectedEofMidFrame {
                sealed_partial: 18_432,
                inner_partial: 131_072
            }
        );
        // Subsequent `take` completes the 200 KB frame and leaves cursor at clean boundary:
        assert_eq!(
            c.complete_inner_frame(204_800),
            DualLayerReadOutcome::CompletedWholeFrame {
                frame_bytes: 204_800
            }
        );
        assert_eq!(c.on_eof(), DualLayerReadOutcome::CleanEofAtFrameBoundary);
    }
}
