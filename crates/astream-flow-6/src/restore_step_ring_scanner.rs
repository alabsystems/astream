// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm-restore` crash-restore step-ring zero-gap classifier
//! (`Astream.Wire.TlaRestoreStepRingScanner`, Island #277).
//!
//! Zero slice indexing or `SliceIndex::get` calls are used here so `astream-wire`
//! maintains `0` new `runtime_checked` obligations under Trust verification.

#[cfg(clean_islands)]
#[path = "restore_step_ring_scanner_island.rs"]
mod restore_step_ring_scanner_island;
#[cfg(clean_islands)]
pub use restore_step_ring_scanner_island::{
    restore_resync_budget_advance, restore_ring_valid_clamp,
};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn restore_ring_valid_clamp(valid_len: u64, ring_cap: u64) -> u64 {
    if valid_len < ring_cap {
        valid_len
    } else {
        ring_cap
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn restore_resync_budget_advance(floor_budget: u64, scaled_budget: u64) -> u64 {
    if floor_budget < scaled_budget {
        scaled_budget
    } else {
        floor_budget
    }
}

/// Minimum linear CRC resync budget (`16 MiB`, matching `steps::RESYNC_CRC_FLOOR`).
pub const RESTORE_RESYNC_CRC_FLOOR: u64 = 16 * 1024 * 1024;

/// Slope multiplier (`2x` remaining bytes) for linear CRC resync budgeting.
pub const RESTORE_RESYNC_PER_BYTE: u64 = 2;

contract_fn! {
    /// Verified check `valid_len <= ring_cap`, linked via `clean-kernel-defeq` to
    /// `restore_gap_within_ring_isl`.
    #[must_use]
    pub const fn restore_gap_within_ring(valid_len: u64, ring_cap: u64) -> bool
    clauses [ensures result == (valid_len <= ring_cap)]
    {
        valid_len <= ring_cap
    }
}

/// Classification of the tail of an `aterm-restore` step-ring region.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RingWalkEnd {
    /// Records tiled the entire region cleanly (`valid_len == region.len()`).
    CleanFull { valid_len: usize },
    /// Scan stopped at `valid_len` and every trailing byte in `valid_len..region.len()` is `0x00`.
    ZeroGap { valid_len: usize, gap_bytes: usize },
    /// Scan stopped at `valid_len` with non-zero interrupted record bytes in the tail.
    TornRecord {
        valid_len: usize,
        first_nonzero_rel: usize,
    },
    /// Structural step/CRC fault (`OutOfOrder`, `CorruptFrame` followed by intact frame, etc.).
    Fault { valid_len: usize, fault_at: usize },
}

/// Compute the linear CRC resync budget `max(scanned_tail * 2, 16 MiB)` without overflow.
#[must_use]
pub const fn linear_resync_crc_budget(tail_bytes: usize) -> u64 {
    let scaled = (tail_bytes as u64).saturating_mul(RESTORE_RESYNC_PER_BYTE);
    restore_resync_budget_advance(RESTORE_RESYNC_CRC_FLOOR, scaled)
}

/// Check whether `tail` consists solely of `0x00` bytes; returns `None` if all zero, or
/// `Some(rel_offset)` of the first non-zero byte using slice pattern matching only.
#[must_use]
pub const fn first_nonzero_offset(mut tail: &[u8]) -> Option<usize> {
    let mut off = 0usize;
    while let [b, rest @ ..] = tail {
        if *b != 0 {
            return Some(off);
        }
        tail = rest;
        off = off.saturating_add(1);
    }
    None
}

/// Classify a step-ring scan outcome given `region`, `valid_len`, and optional `fault_at`.
#[must_use]
pub const fn classify_ring_tail(
    region: &[u8],
    raw_valid_len: usize,
    fault_at: Option<usize>,
) -> RingWalkEnd {
    let clamped = restore_ring_valid_clamp(raw_valid_len as u64, region.len() as u64) as usize;
    if let Some(at) = fault_at {
        let clamped_at = restore_ring_valid_clamp(at as u64, region.len() as u64) as usize;
        return RingWalkEnd::Fault {
            valid_len: clamped,
            fault_at: clamped_at,
        };
    }
    let mut tail = region;
    let mut rem = clamped;
    while rem > 0 {
        let [_, rest @ ..] = tail else {
            return RingWalkEnd::CleanFull { valid_len: clamped };
        };
        tail = rest;
        rem = rem.saturating_sub(1);
    }
    if tail.is_empty() {
        return RingWalkEnd::CleanFull { valid_len: clamped };
    }
    match first_nonzero_offset(tail) {
        None => RingWalkEnd::ZeroGap {
            valid_len: clamped,
            gap_bytes: tail.len(),
        },
        Some(rel) => RingWalkEnd::TornRecord {
            valid_len: clamped,
            first_nonzero_rel: rel,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_gap_vs_torn_vs_fault_and_linear_budget() {
        let mut buf = [0u8; 64];
        buf[0] = 0xAA;
        buf[15] = 0xBB;
        assert_eq!(
            classify_ring_tail(&buf, 16, None),
            RingWalkEnd::ZeroGap {
                valid_len: 16,
                gap_bytes: 48,
            }
        );
        assert!(restore_gap_within_ring(16, 64));

        buf[20] = 0x7F;
        assert_eq!(
            classify_ring_tail(&buf, 16, None),
            RingWalkEnd::TornRecord {
                valid_len: 16,
                first_nonzero_rel: 4,
            }
        );

        buf[20] = 0;
        assert_eq!(
            classify_ring_tail(&buf, 16, Some(16)),
            RingWalkEnd::Fault {
                valid_len: 16,
                fault_at: 16,
            }
        );

        assert_eq!(
            linear_resync_crc_budget(4 * 1024 * 1024),
            RESTORE_RESYNC_CRC_FLOOR
        );
        assert_eq!(
            linear_resync_crc_budget(8 * 1024 * 1024),
            RESTORE_RESYNC_CRC_FLOOR
        );
        assert_eq!(
            linear_resync_crc_budget(8 * 1024 * 1024 + 1),
            RESTORE_RESYNC_CRC_FLOOR + 2
        );
    }
}
