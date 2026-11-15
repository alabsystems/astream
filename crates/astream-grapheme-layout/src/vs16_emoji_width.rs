// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Variation Selector-15 (`U+FE0E` text `1`-col) vs Variation Selector-16 (`U+FE0F` emoji `2`-col)
//! presentation width resolver (`DECSET 2027` grapheme width mode; `Astream.Grapheme.TlaVs16EmojiWidth`).

#[cfg(clean_islands)]
#[path = "vs16_emoji_width_island.rs"]
mod vs16_emoji_width_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_width_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_vs_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use vs16_emoji_width_island::{gr_vs_advance, gr_width_clamp};

/// Maximum terminal columns occupied by a single grapheme cluster (`2`).
pub const MAX_GRAPHEME_CELL_WIDTH: u64 = 2;

contract_fn! {
    /// Verified wide-cell check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gr_is_wide_cell_isl`.
    #[must_use]
    pub const fn gr_is_wide_cell(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Resolves cell width (`1` or `2`) when `U+FE0E` / `U+FE0F` modifies a base codepoint.
#[derive(Debug, Clone, Default)]
pub struct VariationWidthResolver {
    mode_2027_enabled: bool,
    upgrades: u64,
}

impl VariationWidthResolver {
    #[must_use]
    pub const fn new(mode_2027_enabled: bool) -> Self {
        Self {
            mode_2027_enabled,
            upgrades: 0,
        }
    }

    pub fn resolve_width(&mut self, base_width: u64, selector: Option<char>) -> u64 {
        let mut w = gr_width_clamp(base_width, MAX_GRAPHEME_CELL_WIDTH);
        if self.mode_2027_enabled {
            match selector {
                Some('\u{FE0F}') => {
                    w = 2;
                    self.upgrades = gr_vs_advance(self.upgrades, self.upgrades.saturating_add(1));
                }
                Some('\u{FE0E}') => {
                    w = 1;
                }
                _ => {}
            }
        }
        let clamped = gr_width_clamp(w, MAX_GRAPHEME_CELL_WIDTH);
        let _ = gr_is_wide_cell(clamped, 2);
        clamped
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vs16_upgrades_text_symbol_to_two_columns_when_mode_2027_active() {
        let mut r = VariationWidthResolver::new(true);
        assert_eq!(r.resolve_width(1, Some('\u{FE0F}')), 2);
        assert_eq!(r.resolve_width(2, Some('\u{FE0E}')), 1);
    }
}
