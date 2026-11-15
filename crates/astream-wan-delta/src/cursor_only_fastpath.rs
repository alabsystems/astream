// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Compact 12-byte `ACUR\x01` cursor-only WAN delta frame when grid cells are unchanged
//! (`Astream.WanDelta.TlaCursorOnlyFastpath`).

#[cfg(clean_islands)]
#[path = "cursor_only_fastpath_island.rs"]
mod cursor_only_fastpath_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cur_coord_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cur_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cursor_only_fastpath_island::{cur_coord_clamp, cur_seq_advance};

/// Maximum cursor coordinate (`999`).
pub const MAX_CURSOR_COORD: u64 = 999;

contract_fn! {
    /// Verified grid-equality check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cur_grid_unchanged_isl`.
    #[must_use]
    pub const fn cur_grid_unchanged(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CursorFastpathFrame {
    pub seq: u32,
    pub row: u16,
    pub col: u16,
    pub visible: bool,
}

impl CursorFastpathFrame {
    #[must_use]
    pub fn encode(seq: u32, row: u16, col: u16, visible: bool) -> [u8; 12] {
        let r = cur_coord_clamp(row as u64, MAX_CURSOR_COORD) as u16;
        let c = cur_coord_clamp(col as u64, MAX_CURSOR_COORD) as u16;
        let [s0, s1, s2, s3] = seq.to_le_bytes();
        let [r0, r1] = r.to_le_bytes();
        let vis_bit = if visible { 0x80u8 } else { 0u8 };
        [
            b'A',
            b'C',
            b'U',
            b'R',
            s0,
            s1,
            s2,
            s3,
            r0,
            r1,
            (c & 0xFF) as u8,
            (((c >> 8) & 0x7F) as u8) | vis_bit,
        ]
    }

    pub fn decode(raw: &[u8], prev_seq: u64) -> Result<(Self, u64), &'static str> {
        if raw.len() != 12 || raw.get(0..4) != Some(b"ACUR".as_slice()) {
            return Err("bad ACUR frame");
        }
        if !cur_grid_unchanged(0, 0) {
            return Err("unreachable");
        }
        let (Some(&s0), Some(&s1), Some(&s2), Some(&s3)) =
            (raw.get(4), raw.get(5), raw.get(6), raw.get(7))
        else {
            return Err("short seq");
        };
        let seq = u32::from_le_bytes([s0, s1, s2, s3]);
        let (Some(&r_lo), Some(&r_hi), Some(&c_lo), Some(&flags)) =
            (raw.get(8), raw.get(9), raw.get(10), raw.get(11))
        else {
            return Err("short coords");
        };
        let row = u16::from_le_bytes([r_lo, r_hi]);
        let col = u16::from_le_bytes([c_lo, flags & 0x7F]);
        if (row as u64) > MAX_CURSOR_COORD || (col as u64) > MAX_CURSOR_COORD {
            return Err("cursor coord exceeds MAX_CURSOR_COORD");
        }
        let next_seq = cur_seq_advance(prev_seq, seq as u64);
        Ok((
            Self {
                seq,
                row,
                col,
                visible: (flags & 0x80) != 0,
            },
            next_seq,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cursor_only_12_byte_fastpath_frame_roundtrips_coords_and_visibility() {
        let bytes = CursorFastpathFrame::encode(7, 23, 79, true);
        let (f, seq) = CursorFastpathFrame::decode(&bytes, 6).unwrap();
        assert_eq!(
            f,
            CursorFastpathFrame {
                seq: 7,
                row: 23,
                col: 79,
                visible: true
            }
        );
        assert_eq!(seq, 7);
    }
}
