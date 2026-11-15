// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SGR sub-parameter underline styles (`4:0`..`4:5`) and underline color (`58` / `59`) pen
//! state (`Astream.Term.TlaUnderlineStyle`).
//!
//! Models Kitty / VTE / `aterm` styled underlines used by compiler diagnostic TUIs, Neovim,
//! and Helix:
//! - `CSI 4:0 m` / `CSI 24 m` -> [`UnderlineStyle::None`]
//! - `CSI 4 m` / `CSI 4:1 m` -> [`UnderlineStyle::Single`]
//! - `CSI 4:2 m` / `CSI 21 m` -> [`UnderlineStyle::Double`]
//! - `CSI 4:3 m` -> [`UnderlineStyle::Curly`] (undercurl)
//! - `CSI 4:4 m` -> [`UnderlineStyle::Dotted`]
//! - `CSI 4:5 m` -> [`UnderlineStyle::Dashed`]
//! - `CSI 58;2;r;g;b m` / `CSI 58:2::r:g:b m` -> RGB underline color; `CSI 59 m` resets.

#[cfg(clean_islands)]
#[path = "sgr_underline_style_island.rs"]
mod sgr_underline_style_island;
#[cfg(clean_islands)]
pub use sgr_underline_style_island::{underline_rgb_clamp, underline_style_clamp};

/// Mirror of Clean's `underline_style_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn underline_style_clamp(raw_style: u64, max_style: u64) -> u64 {
    if raw_style < max_style {
        raw_style
    } else {
        max_style
    }
}

/// Mirror of Clean's `underline_rgb_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn underline_rgb_clamp(raw_chan: u64, max_chan: u64) -> u64 {
    if raw_chan < max_chan {
        raw_chan
    } else {
        max_chan
    }
}

contract_fn! {
    /// Kernel-certified check that `style` is within `[0, max_style]` (`style <= max_style`),
    /// linked via `clean-kernel-defeq` to `underline_style_valid_isl`.
    #[must_use]
    pub const fn underline_style_valid(style: u64, max_style: u64) -> bool
    clauses [ensures result == (style <= max_style)]
    {
        style <= max_style
    }
}

/// Highest defined SGR `4:<subparam>` underline style code (`5 = Dashed`).
pub const MAX_UNDERLINE_STYLE_CODE: u64 = 5;

/// SGR underline style (`4:0` .. `4:5`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[repr(u8)]
pub enum UnderlineStyle {
    /// `4:0` / `24`: no underline.
    #[default]
    None = 0,
    /// `4` / `4:1`: standard single straight underline.
    Single = 1,
    /// `4:2` / `21`: double straight underline.
    Double = 2,
    /// `4:3`: wavy / curly undercurl (diagnostic squiggles).
    Curly = 3,
    /// `4:4`: dotted underline.
    Dotted = 4,
    /// `4:5`: dashed underline.
    Dashed = 5,
}

impl UnderlineStyle {
    /// Convert an SGR `4:<subparam>` integer into an [`UnderlineStyle`], returning `None`
    /// for unknown subparameters (`> 5`) so callers ignore unrecognized extensions per ECMA-48.
    #[must_use]
    pub const fn from_subparam(sub: u16) -> Option<Self> {
        if !underline_style_valid(sub as u64, MAX_UNDERLINE_STYLE_CODE) {
            return None;
        }
        let code = underline_style_clamp(sub as u64, MAX_UNDERLINE_STYLE_CODE);
        match code {
            0 => Some(Self::None),
            1 => Some(Self::Single),
            2 => Some(Self::Double),
            3 => Some(Self::Curly),
            4 => Some(Self::Dotted),
            _ => Some(Self::Dashed),
        }
    }

    /// Numeric SGR `4:<code>` subparameter (`0..=5`).
    #[must_use]
    pub const fn code(self) -> u8 {
        self as u8
    }
}

/// Optional SGR `58` underline color override (`59` resets to `Default`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum UnderlineColor {
    /// Use the cell's foreground color (`SGR 59`).
    #[default]
    Default,
    /// 256-color palette index (`SGR 58;5;idx`).
    Indexed(u8),
    /// 24-bit RGB underline color (`SGR 58;2;r;g;b` / `58:2::r:g:b`).
    Rgb(u8, u8, u8),
}

/// Combined underline pen state (`style` + `color`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct UnderlinePen {
    /// Active underline style.
    pub style: UnderlineStyle,
    /// Active underline color override.
    pub color: UnderlineColor,
}

impl UnderlinePen {
    /// Construct the default reset underline pen (`None`, `Default`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            style: UnderlineStyle::None,
            color: UnderlineColor::Default,
        }
    }

    /// Apply `CSI 4:<subparam> m` (unknown subparameters leave `self.style` unchanged).
    pub const fn apply_sgr4_subparam(&mut self, sub: u16) {
        if let Some(st) = UnderlineStyle::from_subparam(sub) {
            self.style = st;
        }
    }

    /// Apply `CSI 58;2;r;g;b m` or `CSI 58:2::r:g:b m` with channel clamping (`0..=255`).
    pub const fn set_rgb(&mut self, r: u16, g: u16, b: u16) {
        let rc = underline_rgb_clamp(r as u64, 255) as u8;
        let gc = underline_rgb_clamp(g as u64, 255) as u8;
        let bc = underline_rgb_clamp(b as u64, 255) as u8;
        self.color = UnderlineColor::Rgb(rc, gc, bc);
    }

    /// Apply `CSI 58;5;idx m` with palette clamping (`0..=255`).
    pub const fn set_indexed(&mut self, idx: u16) {
        let ic = underline_rgb_clamp(idx as u64, 255) as u8;
        self.color = UnderlineColor::Indexed(ic);
    }

    /// Apply `CSI 59 m` (reset underline color only, preserving `self.style`).
    pub const fn reset_color(&mut self) {
        self.color = UnderlineColor::Default;
    }

    /// Apply `CSI 24 m` (turn off underline style, preserving `self.color`).
    pub const fn clear_style(&mut self) {
        self.style = UnderlineStyle::None;
    }

    /// Apply `CSI 0 m` (reset both style and color).
    pub const fn reset_all(&mut self) {
        *self = Self::new();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn undercurl_and_rgb_underline_color_transitions_preserve_invariants() {
        let mut pen = UnderlinePen::new();
        pen.apply_sgr4_subparam(3);
        pen.set_rgb(255, 90, 400);
        assert_eq!(pen.style, UnderlineStyle::Curly);
        assert_eq!(pen.color, UnderlineColor::Rgb(255, 90, 255));

        // Unknown subparam 99 is ignored cleanly.
        pen.apply_sgr4_subparam(99);
        assert_eq!(pen.style, UnderlineStyle::Curly);

        pen.reset_color();
        assert_eq!(pen.color, UnderlineColor::Default);
        assert_eq!(pen.style, UnderlineStyle::Curly);

        pen.clear_style();
        assert_eq!(pen.style, UnderlineStyle::None);
    }
}
