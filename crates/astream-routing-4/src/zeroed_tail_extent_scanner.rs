// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Preallocated zeroed-tail extent vs mid-file corruption classifier
//! (`Astream.Engine.TlaZeroedTailExtentScanner`).
//!
//! After power loss on APFS/XFS/ext4, `fallocate` or metadata-first `ftruncate`
//! can leave a contiguous run of `0x00` bytes after the last sealed WAL record.
//! A pure `0x00` tail up to `max_scan_bytes` may be safely truncated back to
//! `sealed_end_offset`, whereas ANY non-zero byte appearing after the zeroed
//! header proves out-of-order / mid-file corruption and MUST fail closed!

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

#[cfg(clean_islands)]
#[path = "zeroed_tail_extent_scanner_island.rs"]
mod zeroed_tail_extent_scanner_island;
#[cfg(clean_islands)]
pub use zeroed_tail_extent_scanner_island::{tail_scan_clamp, valid_prefix_advance};

/// Default maximum preallocated zeroed tail (`4 MiB`) eligible for clean truncation.
pub const DEFAULT_MAX_ZERO_TAIL_BYTES: usize = 4 * 1024 * 1024;

#[cfg(not(clean_islands))]
/// Monotonically advance the verified intact WAL byte prefix.
#[must_use]
pub const fn valid_prefix_advance(cur_prefix: u64, cand_prefix: u64) -> u64 {
    if cur_prefix < cand_prefix {
        cand_prefix
    } else {
        cur_prefix
    }
}

#[cfg(not(clean_islands))]
/// Clamp scanned tail length to `max_scan_bytes`.
#[must_use]
pub const fn tail_scan_clamp(cand_bytes: u64, max_scan_bytes: u64) -> u64 {
    if cand_bytes < max_scan_bytes {
        cand_bytes
    } else {
        max_scan_bytes
    }
}

contract_fn! {
    /// True iff zero non-zero bytes appeared inside the zeroed tail extent.
    #[must_use]
    pub const fn tail_pure_zero(dirty_after_zero: u64, zero_expected: u64) -> bool
    clauses [ensures result == (dirty_after_zero == zero_expected)]
    {
        dirty_after_zero == zero_expected
    }
}

/// Classification of trailing bytes after the last valid WAL frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TailExtentVerdict {
    /// No trailing bytes (`tail.is_empty()`).
    ExactEnd { verified_len: u64 },
    /// Pure `0x00` preallocated extent safe to truncate to `truncate_to`.
    TruncateZeroedExtent { truncate_to: u64, zero_bytes: u64 },
    /// Non-zero byte at `relative_offset` inside zeroed region -> mid-file corruption!
    CorruptNonZeroAfterZero { relative_offset: u64, byte: u8 },
    /// Trailing extent exceeds `max_scan_bytes` -> refuse automatic truncation.
    TailExceedsScanBudget {
        tail_len: usize,
        max_scan_bytes: usize,
    },
}

/// Stateful WAL tail extent verifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ZeroedTailExtentScanner {
    verified_prefix: u64,
    last_scanned_tail: u64,
    max_scan_bytes: usize,
}

impl Default for ZeroedTailExtentScanner {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_ZERO_TAIL_BYTES)
    }
}

impl ZeroedTailExtentScanner {
    #[must_use]
    pub const fn new(max_scan_bytes: usize) -> Self {
        let cap = if max_scan_bytes == 0 {
            DEFAULT_MAX_ZERO_TAIL_BYTES
        } else {
            max_scan_bytes
        };
        Self {
            verified_prefix: 0,
            last_scanned_tail: 0,
            max_scan_bytes: cap,
        }
    }

    #[must_use]
    pub const fn verified_prefix(&self) -> u64 {
        self.verified_prefix
    }

    #[must_use]
    pub const fn last_scanned_tail(&self) -> u64 {
        self.last_scanned_tail
    }

    /// Classify `tail` bytes starting at `sealed_end_offset`.
    #[allow(clippy::manual_unwrap_or)]
    pub fn classify_tail(&mut self, sealed_end_offset: u64, tail: &[u8]) -> TailExtentVerdict {
        self.verified_prefix = valid_prefix_advance(self.verified_prefix, sealed_end_offset);
        if tail.is_empty() {
            self.last_scanned_tail = 0;
            return TailExtentVerdict::ExactEnd {
                verified_len: self.verified_prefix,
            };
        }
        if tail.len() > self.max_scan_bytes {
            self.last_scanned_tail = tail_scan_clamp(tail.len() as u64, self.max_scan_bytes as u64);
            return TailExtentVerdict::TailExceedsScanBudget {
                tail_len: tail.len(),
                max_scan_bytes: self.max_scan_bytes,
            };
        }

        let mut dirty_count = 0u64;
        let mut first_dirty: Option<(u64, u8)> = None;
        let mut idx = 0u64;
        let mut rest = tail;
        while let &[b, ref rem @ ..] = rest {
            if b != 0 {
                dirty_count = dirty_count.saturating_add(1);
                if first_dirty.is_none() {
                    first_dirty = Some((idx, b));
                }
            }
            idx = idx.saturating_add(1);
            rest = rem;
        }

        let scanned = tail_scan_clamp(tail.len() as u64, self.max_scan_bytes as u64);
        self.last_scanned_tail = scanned;

        if tail_pure_zero(dirty_count, 0) {
            TailExtentVerdict::TruncateZeroedExtent {
                truncate_to: self.verified_prefix,
                zero_bytes: scanned,
            }
        } else {
            let (rel, byte) = match first_dirty {
                Some(pair) => pair,
                None => (0, 1),
            };
            TailExtentVerdict::CorruptNonZeroAfterZero {
                relative_offset: rel,
                byte,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncates_pure_zero_extent_and_refuses_sparse_hole_corruption() {
        let mut scanner = ZeroedTailExtentScanner::new(4096);
        assert_eq!(
            scanner.classify_tail(1024, &[0u8; 512]),
            TailExtentVerdict::TruncateZeroedExtent {
                truncate_to: 1024,
                zero_bytes: 512,
            }
        );

        let mut hole_then_data = [0u8; 64];
        hole_then_data[40] = 0xAA;
        assert_eq!(
            scanner.classify_tail(2048, &hole_then_data),
            TailExtentVerdict::CorruptNonZeroAfterZero {
                relative_offset: 40,
                byte: 0xAA,
            }
        );
    }
}
