// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded ZWJ / combining extended-grapheme-cluster scalar & cell-width fence
//! (`Astream.Term.TlaGraphemeClusterWidthFence`).
//!
//! Protects `astream-term` cell storage against degenerate PTY ZWJ (`U+200D`) / combining-mark
//! bombs while keeping single-scalar `char_display_width` behavior untouched (`aterm-conformance`).

#[cfg(clean_islands)]
#[path = "grapheme_cluster_width_fence_island.rs"]
mod grapheme_cluster_width_fence_island;
#[cfg(clean_islands)]
pub use grapheme_cluster_width_fence_island::{
    cluster_seq_advance_b110, grapheme_scalars_clamp_b110,
};

#[cfg(not(clean_islands))]
/// Clamp codepoints accumulated in a single terminal cell's grapheme cluster to `max_scalars`.
#[must_use]
pub const fn grapheme_scalars_clamp_b110(cand_scalars: u64, max_scalars: u64) -> u64 {
    if cand_scalars < max_scalars {
        cand_scalars
    } else {
        max_scalars
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance finalized grapheme-cluster sequence counter.
#[must_use]
pub const fn cluster_seq_advance_b110(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff the current grapheme cluster can absorb another combining/ZWJ scalar below `max_scalars`.
    #[must_use]
    pub const fn grapheme_can_append_scalar_b110(cur_scalars: u64, max_scalars: u64) -> bool
    clauses [ensures result == (cur_scalars < max_scalars)]
    {
        cur_scalars < max_scalars
    }
}

/// Maximum Unicode scalar values attached to a single terminal grid cell.
pub const MAX_CLUSTER_SCALARS: usize = 8;

/// Outcome of feeding a continuation scalar (ZWJ / VS16 / combining mark) to the active cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClusterAppendOutcome {
    Appended { scalar_count: u64, cell_width: u8 },
    CappedDropContinuation { cluster_seq: u64 },
}

/// Bounded per-cell extended grapheme cluster accumulator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphemeClusterWidthFence {
    scalars: [u32; MAX_CLUSTER_SCALARS],
    scalar_count: u64,
    cell_width: u8,
    cluster_seq: u64,
}

impl Default for GraphemeClusterWidthFence {
    fn default() -> Self {
        Self::new()
    }
}

impl GraphemeClusterWidthFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            scalars: [0; MAX_CLUSTER_SCALARS],
            scalar_count: 0,
            cell_width: 0,
            cluster_seq: 0,
        }
    }

    #[must_use]
    pub const fn scalar_count(&self) -> u64 {
        self.scalar_count
    }

    #[must_use]
    pub const fn cell_width(&self) -> u8 {
        self.cell_width
    }

    /// Start a new base cell with `base_cp` and single-scalar `base_width` (`1` or `2`).
    pub fn start_base(&mut self, base_cp: u32, base_width: u8) {
        let next_seq = self.cluster_seq.saturating_add(1);
        self.cluster_seq = cluster_seq_advance_b110(self.cluster_seq, next_seq);
        self.scalars = [0; MAX_CLUSTER_SCALARS];
        self.scalars[0] = base_cp;
        self.scalar_count = 1;
        self.cell_width = if base_width > 2 { 2 } else { base_width };
    }

    /// Append a zero-width joiner, variation selector (`U+FE0F` widens `1 -> 2`), or combining mark.
    pub fn push_continuation(&mut self, cp: u32) -> ClusterAppendOutcome {
        let cap = MAX_CLUSTER_SCALARS as u64;
        if !grapheme_can_append_scalar_b110(self.scalar_count, cap) {
            return ClusterAppendOutcome::CappedDropContinuation {
                cluster_seq: self.cluster_seq,
            };
        }
        let Some(dst) = self.scalars.get_mut(self.scalar_count as usize) else {
            return ClusterAppendOutcome::CappedDropContinuation {
                cluster_seq: self.cluster_seq,
            };
        };
        *dst = cp;
        let cand = self.scalar_count.saturating_add(1);
        self.scalar_count = grapheme_scalars_clamp_b110(cand, cap);
        if cp == 0xFE0F && self.cell_width == 1 {
            self.cell_width = 2;
        }
        ClusterAppendOutcome::Appended {
            scalar_count: self.scalar_count,
            cell_width: self.cell_width,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widens_on_vs16_and_caps_runaway_zwj_bombs() {
        let mut f = GraphemeClusterWidthFence::new();
        f.start_base(0x2764, 1);
        assert_eq!(
            f.push_continuation(0xFE0F),
            ClusterAppendOutcome::Appended {
                scalar_count: 2,
                cell_width: 2,
            }
        );
        for _ in 0..6 {
            assert!(matches!(
                f.push_continuation(0x200D),
                ClusterAppendOutcome::Appended { .. }
            ));
        }
        assert_eq!(
            f.push_continuation(0x200D),
            ClusterAppendOutcome::CappedDropContinuation { cluster_seq: 1 }
        );
    }
}
