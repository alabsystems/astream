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

/// `replay_cursor_monotone` as `replay_island.rs` defines it in Clean:
/// `if cur_cursor < next_cursor then next_cursor else cur_cursor`.
#[must_use]
pub const fn replay_cursor_monotone(cur_cursor: u64, next_cursor: u64) -> u64 {
    if cur_cursor < next_cursor {
        next_cursor
    } else {
        cur_cursor
    }
}

/// `demo_clamp_poll_index` as `demo_island.rs` defines it in Clean:
/// `if idx < max_reads then idx else max_reads`.
#[must_use]
pub const fn demo_clamp_poll_index(idx: u64, max_reads: u64) -> u64 {
    if idx < max_reads {
        idx
    } else {
        max_reads
    }
}

/// `keyed_clamp_cutoff` as `keyed_island.rs` defines it in Clean:
/// `if seen < tape_len then seen else tape_len`.
#[must_use]
pub const fn keyed_clamp_cutoff(seen: u64, tape_len: u64) -> u64 {
    if seen < tape_len {
        seen
    } else {
        tape_len
    }
}

/// `record_mono_advance` as `record_island.rs` defines it in Clean:
/// `if prev < now then now else prev`.
#[must_use]
pub const fn record_mono_advance(prev: u64, now: u64) -> u64 {
    if prev < now {
        now
    } else {
        prev
    }
}

/// `seam_false_reads_advance` as `seam_island.rs` defines it in Clean:
/// `if cur < next then next else cur`.
#[must_use]
pub const fn seam_false_reads_advance(cur: u64, next: u64) -> u64 {
    if cur < next {
        next
    } else {
        cur
    }
}

/// `shadow_nonzero_bit` as `shadow_island.rs` defines it in Clean:
/// `if 0 < val then code else 0`.
#[must_use]
pub const fn shadow_nonzero_bit(val: u64, code: u64) -> u64 {
    if 0 < val {
        code
    } else {
        0
    }
}

/// `shadow_code_select` as `shadow_island.rs` defines it in Clean:
/// `if 0 < primary_count then primary_code else fallback_code`.
#[must_use]
pub const fn shadow_code_select(primary_count: u64, primary_code: u64, fallback_code: u64) -> u64 {
    if 0 < primary_count {
        primary_code
    } else {
        fallback_code
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
            answers(|[a, b]| crate::replay::replay_cursor_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::replay_cursor_monotone(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::demo::demo_clamp_poll_index(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::demo_clamp_poll_index(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::keyed::keyed_clamp_cutoff(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::keyed_clamp_cutoff(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::record::record_mono_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::record_mono_advance(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::seam::seam_false_reads_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::seam_false_reads_advance(a, b)),
            want
        );
        let want = "000012012";
        assert_eq!(
            answers(|[a, b]| crate::shadow::shadow_nonzero_bit(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::shadow_nonzero_bit(a, b)), want);
        let want = "012012012000111222000111222";
        assert_eq!(
            answers(|[a, b, c]| crate::shadow::shadow_code_select(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::shadow_code_select(a, b, c)),
            want
        );
        for &a in &super::twin_answers::EDGES {
            for &b in &super::twin_answers::EDGES {
                let want_taint = if a > 0 || b > 0 { 1 } else { 0 };
                assert_eq!(crate::shadow::shadow_taint_latch(a, b), want_taint);
                let want_exit = if a > 0 {
                    1
                } else if b > 0 {
                    3
                } else {
                    0
                };
                assert_eq!(crate::shadow::shadow_exit_code(a, b), want_exit);
            }
        }
    }

    // Not vacuous: `replay_cursor_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
