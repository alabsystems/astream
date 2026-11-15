// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Unicode Box Drawing (`U+2500..=U+257F`) & Block Elements (`U+2580..=U+259F`) procedural Metal
//! quad router ensuring TUI borders (`tmux`, `btop`, `lazygit`) snap pixel-sharp with zero seam
//! gaps (`Astream.MetalDmg.TlaBoxDrawingProcedural`).

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
#[path = "box_drawing_procedural_island.rs"]
mod box_drawing_procedural_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_cp_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_quad_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use box_drawing_procedural_island::{md_cp_clamp, md_quad_advance};

/// Unicode scalar ceiling (`0x10_FFFF`).
pub const MAX_UNICODE_SCALAR: u64 = 0x10_FFFF;

contract_fn! {
    /// Verified procedural-range match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `md_is_procedural_box_isl`.
    #[must_use]
    pub const fn md_is_procedural_box(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ProceduralGlyphRouter {
    routed_quads: u64,
}

impl ProceduralGlyphRouter {
    #[must_use]
    pub const fn new() -> Self {
        Self { routed_quads: 0 }
    }

    pub fn is_procedural_cell(&mut self, ch: char) -> bool {
        let cp = md_cp_clamp(ch as u64, MAX_UNICODE_SCALAR);
        let in_box_or_block = (0x2500 <= cp) && (cp <= 0x259F);
        if md_is_procedural_box(if in_box_or_block { 1 } else { 0 }, 1) {
            self.routed_quads =
                md_quad_advance(self.routed_quads, self.routed_quads.saturating_add(1));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn routes_box_drawing_and_block_elements_to_procedural_quads() {
        let mut r = ProceduralGlyphRouter::new();
        assert!(r.is_procedural_cell('\u{2500}'));
        assert!(r.is_procedural_cell('\u{2588}'));
        assert!(!r.is_procedural_cell('A'));
    }
}
