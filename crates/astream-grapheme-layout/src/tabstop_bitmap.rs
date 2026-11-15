// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Custom VT horizontal tab-stop bitmap (`HTS` `ESC H`, `TBC` `CSI 0 g` / `CSI 3 g`, `CHT` `CSI I`)
//! supporting up to `512` columns in `8` `u64` words (`Astream.Grapheme.TlaTabstopBitmap`).

#[cfg(clean_islands)]
#[path = "tabstop_bitmap_island.rs"]
mod tabstop_bitmap_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_tab_col_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_tab_ops_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use tabstop_bitmap_island::{gr_tab_col_clamp, gr_tab_ops_advance};

/// Maximum column index (`511`, i.e., `512` columns total).
pub const MAX_TABSTOP_COL: u64 = 511;

contract_fn! {
    /// Verified next-stop bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gr_next_tab_in_row_isl`.
    #[must_use]
    pub const fn gr_next_tab_in_row(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Bitset of horizontal tab stops initialized to standard `8`-column intervals.
#[derive(Debug, Clone)]
pub struct VtTabstopRow {
    words: [u64; 8],
    max_col: u64,
    ops: u64,
}

impl VtTabstopRow {
    #[must_use]
    pub fn standard_8col(cols: u64) -> Self {
        let max_col = gr_tab_col_clamp(cols.saturating_sub(1), MAX_TABSTOP_COL);
        let mut s = Self {
            words: [0; 8],
            max_col,
            ops: 0,
        };
        let mut c = 8u64;
        while c <= max_col {
            s.set_stop(c);
            c = c.saturating_add(8);
        }
        s
    }

    pub fn set_stop(&mut self, col: u64) {
        let c = gr_tab_col_clamp(col, self.max_col);
        let w_idx = (c >> 6) as usize;
        let bit = c & 63;
        if let Some(w) = self.words.get_mut(w_idx) {
            *w |= 1u64 << (bit & 63);
        }
        self.ops = gr_tab_ops_advance(self.ops, self.ops.saturating_add(1));
    }

    pub fn clear_all(&mut self) {
        self.words = [0; 8];
        self.ops = gr_tab_ops_advance(self.ops, self.ops.saturating_add(1));
    }

    #[must_use]
    pub fn next_stop_after(&self, cur_col: u64) -> u64 {
        let mut c = cur_col.saturating_add(1);
        while c <= self.max_col {
            let w_idx = (c >> 6) as usize;
            let bit = c & 63;
            if let Some(&w) = self.words.get(w_idx) {
                if (w & (1u64 << (bit & 63))) != 0 {
                    let _ = gr_next_tab_in_row(self.max_col, c);
                    return c;
                }
            }
            c = c.saturating_add(1);
        }
        self.max_col
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tabstop_bitmap_advances_to_default_8_or_custom_hts_and_clamps_at_margin() {
        let mut t = VtTabstopRow::standard_8col(80);
        assert_eq!(t.next_stop_after(0), 8);
        t.clear_all();
        t.set_stop(12);
        assert_eq!(t.next_stop_after(0), 12);
        assert_eq!(t.next_stop_after(12), 79);
    }
}
