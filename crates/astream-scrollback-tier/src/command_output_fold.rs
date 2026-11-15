// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Semantic `OSC 133` `C..D` command-output fold range calculator collapsing multi-thousand-line
//! build logs in `aterm` while preserving exact raw scrollback line numbering
//! (`Astream.ScrollTier.TlaCommandOutputFold`).

#[cfg(clean_islands)]
#[path = "command_output_fold_island.rs"]
mod command_output_fold_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_lines_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_fold_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use command_output_fold_island::{sb_fold_advance, sb_lines_clamp};

/// Maximum single folded command-output span (`1_000_000` lines).
pub const MAX_FOLD_SPAN_LINES: u64 = 1_000_000;

contract_fn! {
    /// Verified non-empty ordered fold span (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sb_fold_range_valid_isl`.
    #[must_use]
    pub const fn sb_fold_range_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoldSpan {
    pub start_line: u64,
    pub end_line: u64,
    pub hidden_lines: u64,
}

#[derive(Debug, Clone, Default)]
pub struct CommandOutputFolder {
    folds_created: u64,
}

impl CommandOutputFolder {
    #[must_use]
    pub const fn new() -> Self {
        Self { folds_created: 0 }
    }

    pub fn create_fold(&mut self, start_line: u64, end_line: u64) -> Option<FoldSpan> {
        let min_end = start_line.saturating_add(2);
        if !sb_fold_range_valid(end_line, min_end) {
            return None;
        }
        let hidden = sb_lines_clamp(end_line.saturating_sub(start_line), MAX_FOLD_SPAN_LINES);
        self.folds_created =
            sb_fold_advance(self.folds_created, self.folds_created.saturating_add(1));
        Some(FoldSpan {
            start_line,
            end_line,
            hidden_lines: hidden,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn creates_fold_for_multiline_command_output_and_skips_single_line() {
        let mut f = CommandOutputFolder::new();
        assert_eq!(f.create_fold(10, 11), None);
        let span = f.create_fold(10, 250).expect("valid fold");
        assert_eq!(span.hidden_lines, 240);
    }
}
