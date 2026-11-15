// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions this crate's Clean islands compile.
//!
//! An island (`*_island.rs`) mounts only under `cfg(clean_islands)`, which build.rs
//! sets when the compiler answers that it is Trust: no stock rustc can lex Clean. Under
//! Trust, each function an island compiles from Clean (`clean_origin_mir` I5) is the one
//! Rust calls; under every other compiler it is its twin below, written from the same
//! definition. The tests hold the twins, and whichever function a build calls, to the
//! answers the island gives, which every Trust test run re-checks against the island.

/// `echo_watermark_monotone` as `predict_island.rs` defines it in Clean:
/// `if cur_wm < new_wm then new_wm else cur_wm`.
#[must_use]
pub const fn echo_watermark_monotone(cur_wm: u64, new_wm: u64) -> u64 {
    if cur_wm < new_wm {
        new_wm
    } else {
        cur_wm
    }
}

/// `echo_causal_watermark_select` as `predict_island.rs` defines it in Clean:
/// `if in_off == pred_in_off then next_wm else cur_wm`.
#[must_use]
pub const fn echo_causal_watermark_select(
    in_off: u64,
    pred_in_off: u64,
    next_wm: u64,
    cur_wm: u64,
) -> u64 {
    if in_off == pred_in_off {
        next_wm
    } else {
        cur_wm
    }
}

/// `event_advance_offset_monotone` as `events_island.rs` defines it in Clean:
/// `if cur_offset < next_offset then next_offset else cur_offset`.
#[must_use]
pub const fn event_advance_offset_monotone(cur_offset: u64, next_offset: u64) -> u64 {
    if cur_offset < next_offset {
        next_offset
    } else {
        cur_offset
    }
}

/// `op_clamp_scroll_top` as `ops_island.rs` defines it in Clean:
/// `if top < bottom then top else bottom`.
#[must_use]
pub const fn op_clamp_scroll_top(top: u64, bottom: u64) -> u64 {
    if top < bottom {
        top
    } else {
        bottom
    }
}

/// `perceive_clamp_take_count` as `perceive_island.rs` defines it in Clean:
/// `if requested < total then requested else total`.
#[must_use]
pub const fn perceive_clamp_take_count(requested: u64, total: u64) -> u64 {
    if requested < total {
        requested
    } else {
        total
    }
}

/// `record_client_seq_advance` as `record_island.rs` defines it in Clean:
/// `if cur_seq < proposed_seq then proposed_seq else cur_seq`.
#[must_use]
pub const fn record_client_seq_advance(cur_seq: u64, proposed_seq: u64) -> u64 {
    if cur_seq < proposed_seq {
        proposed_seq
    } else {
        cur_seq
    }
}

/// `render_clamp_end_offset` as `render_island.rs` defines it in Clean:
/// `if to_off < max_off then to_off else max_off`.
#[must_use]
pub const fn render_clamp_end_offset(to_off: u64, max_off: u64) -> u64 {
    if to_off < max_off {
        to_off
    } else {
        max_off
    }
}

/// `screen_clamp_dim` as `screen_island.rs` defines it in Clean:
/// `if dim < max_dim then dim else max_dim`.
#[must_use]
pub const fn screen_clamp_dim(dim: u64, max_dim: u64) -> u64 {
    if dim < max_dim {
        dim
    } else {
        max_dim
    }
}

/// `program_rule_cap_clamp` as `program_predict_island.rs` defines it in Clean:
/// `if count < cap then count else cap`.
#[must_use]
pub const fn program_rule_cap_clamp(count: u64, cap: u64) -> u64 {
    if count < cap {
        count
    } else {
        cap
    }
}

/// `color_clamp_channel` as `color_island.rs` defines it in Clean:
/// `if val < max_val then val else max_val`.
#[must_use]
pub const fn color_clamp_channel(val: u64, max_val: u64) -> u64 {
    if val < max_val {
        val
    } else {
        max_val
    }
}

/// `combining_cap_clamp` as `color_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn combining_cap_clamp(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
    }
}

/// `wide_cell_width_clamp` as `wide_island.rs` defines it in Clean:
/// `if width < max_width then width else max_width`.
#[must_use]
pub const fn wide_cell_width_clamp(width: u64, max_width: u64) -> u64 {
    if width < max_width {
        width
    } else {
        max_width
    }
}

/// `wide_spacer_col_clamp` as `wide_island.rs` defines it in Clean:
/// `if next_col < line_end then next_col else line_end`.
#[must_use]
pub const fn wide_spacer_col_clamp(next_col: u64, line_end: u64) -> u64 {
    if next_col < line_end {
        next_col
    } else {
        line_end
    }
}

/// `sync_bytes_clamp` as `sync_island.rs` defines it in Clean:
/// `if proposed_bytes < byte_cap then proposed_bytes else byte_cap`.
#[must_use]
pub const fn sync_bytes_clamp(proposed_bytes: u64, byte_cap: u64) -> u64 {
    if proposed_bytes < byte_cap {
        proposed_bytes
    } else {
        byte_cap
    }
}

/// `sync_hold_ticks_clamp` as `sync_island.rs` defines it in Clean:
/// `if proposed_ticks < tick_cap then proposed_ticks else tick_cap`.
#[must_use]
pub const fn sync_hold_ticks_clamp(proposed_ticks: u64, tick_cap: u64) -> u64 {
    if proposed_ticks < tick_cap {
        proposed_ticks
    } else {
        tick_cap
    }
}

/// `vs_width_clamp` as `vs_island.rs` defines it in Clean:
/// `if proposed_width < max_width then proposed_width else max_width`.
#[must_use]
pub const fn vs_width_clamp(proposed_width: u64, max_width: u64) -> u64 {
    if proposed_width < max_width {
        proposed_width
    } else {
        max_width
    }
}

/// `vs_cursor_advance_clamp` as `vs_island.rs` defines it in Clean:
/// `if next_col < line_end then next_col else line_end`.
#[must_use]
pub const fn vs_cursor_advance_clamp(next_col: u64, line_end: u64) -> u64 {
    if next_col < line_end {
        next_col
    } else {
        line_end
    }
}

/// `echo_queue_len_clamp` as `overlap_echo_island.rs` defines it in Clean:
/// `if proposed_len < cap then proposed_len else cap`.
#[must_use]
pub const fn echo_queue_len_clamp(proposed_len: u64, cap: u64) -> u64 {
    if proposed_len < cap {
        proposed_len
    } else {
        cap
    }
}

/// `echo_matched_advance` as `overlap_echo_island.rs` defines it in Clean:
/// `if cur_off < cand_off then cand_off else cur_off`.
#[must_use]
pub const fn echo_matched_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

#[cfg(test)]
#[path = "../../astream-wire/twin_answers.rs"]
mod twin_answers;

#[cfg(test)]
mod tests {
    use super::twin_answers::answers;

    // Each function's answers over every operand tuple of `EDGES` (`twin_answers.rs`), as
    // indices into it. `crate::...` is the island's function under Trust and the twin
    // elsewhere, so every build holds the twin to the island's answers.
    #[test]
    fn the_twins_answer_as_the_islands_do() {
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::predict::echo_watermark_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::echo_watermark_monotone(a, b)), want);
        let want =
            "000111222012012012012012012012012012000111222012012012012012012012012012000111222";
        assert_eq!(
            answers(|[a, b, c, d]| crate::predict::echo_causal_watermark_select(a, b, c, d)),
            want
        );
        assert_eq!(
            answers(|[a, b, c, d]| super::echo_causal_watermark_select(a, b, c, d)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::events::event_advance_offset_monotone(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::event_advance_offset_monotone(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::ops::op_clamp_scroll_top(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::op_clamp_scroll_top(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::perceive::perceive_clamp_take_count(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::perceive_clamp_take_count(a, b)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::record::record_client_seq_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::record_client_seq_advance(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::render::render_clamp_end_offset(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::render_clamp_end_offset(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::screen::screen_clamp_dim(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::screen_clamp_dim(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::program_predict::program_rule_cap_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::program_rule_cap_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::screen::color_clamp_channel(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::color_clamp_channel(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::screen::combining_cap_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::combining_cap_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::screen::wide_cell_width_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::wide_cell_width_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::screen::wide_spacer_col_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::wide_spacer_col_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::events::sync_bytes_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::sync_bytes_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::events::sync_hold_ticks_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::sync_hold_ticks_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::screen::vs_width_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::vs_width_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::screen::vs_cursor_advance_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::vs_cursor_advance_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::overlap_echo::echo_queue_len_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::echo_queue_len_clamp(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::overlap_echo::echo_matched_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::echo_matched_advance(a, b)), want);
    }

    // Not vacuous: `echo_watermark_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
