// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Run-length encoder/decoder for uniform-attribute terminal cell runs over low-bandwidth WAN links
//! (`Astream.WanDelta.TlaRleBlankCells`).

#[cfg(clean_islands)]
#[path = "rle_blank_cells_island.rs"]
mod rle_blank_cells_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rle_run_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rle_decoded_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use rle_blank_cells_island::{rle_decoded_advance, rle_run_clamp};

/// Maximum cells decoded from a single WAN RLE row frame (`1024` columns, decompression-bomb guard!).
pub const MAX_WAN_ROW_CELLS: u64 = 1_024;

contract_fn! {
    /// Verified row-width bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `rle_fits_cols_isl`.
    #[must_use]
    pub const fn rle_fits_cols(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Encodes `(ascii_glyph, attr_tag)` cells into `(run_len_u16_le, glyph, attr_tag)` 4-byte tuples.
#[must_use]
pub fn encode_cell_runs(cells: &[(u8, u8)]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(&first) = cells.get(i) {
        let mut run = 1usize;
        while run < usize::from(u16::MAX) {
            if cells.get(i.saturating_add(run)) == Some(&first) {
                run = run.saturating_add(1);
            } else {
                break;
            }
        }
        out.extend_from_slice(&(run as u16).to_le_bytes());
        out.push(first.0);
        out.push(first.1);
        i = i.saturating_add(run);
    }
    out
}

/// Decodes RLE cell tuples fail-closed, enforcing `total_cells <= max_cols` (decompression-bomb proof!).
pub fn decode_cell_runs(wire: &[u8], max_cols: u64) -> Result<Vec<(u8, u8)>, &'static str> {
    if (wire.len() & 3) != 0 {
        return Err("truncated 4-byte RLE cell tuple");
    }
    let cap = rle_run_clamp(max_cols, MAX_WAN_ROW_CELLS);
    let mut out = Vec::new();
    let mut decoded = 0u64;
    let mut off = 0usize;
    while off < wire.len() {
        let (Some(&lo), Some(&hi), Some(&ch), Some(&attr)) = (
            wire.get(off),
            wire.get(off.saturating_add(1)),
            wire.get(off.saturating_add(2)),
            wire.get(off.saturating_add(3)),
        ) else {
            return Err("short rle");
        };
        let run = u16::from_le_bytes([lo, hi]) as u64;
        if run == 0 {
            return Err("zero-length RLE run forbidden");
        }
        let next = decoded.saturating_add(run);
        if !rle_fits_cols(cap, next) {
            return Err("RLE row exceeds column cap (decompression bomb refused)");
        }
        decoded = rle_decoded_advance(decoded, next);
        let mut k = 0u64;
        while k < run {
            out.push((ch, attr));
            k = k.saturating_add(1);
        }
        off = off.saturating_add(4);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blank_row_compresses_to_4_bytes_roundtrips_and_blocks_rle_bomb() {
        let mut row = vec![(b' ', 0u8); 120];
        row[0] = (b'$', 2);
        let enc = encode_cell_runs(&row);
        assert_eq!(enc.len(), 8); // 2 runs * 4B = 8B for 120 cells!
        assert_eq!(decode_cell_runs(&enc, 120).unwrap(), row);
        assert!(decode_cell_runs(&enc, 80).is_err());
    }
}
