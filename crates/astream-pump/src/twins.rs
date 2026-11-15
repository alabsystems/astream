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

/// `pump_offset_monotone` as `pump_island.rs` defines it in Clean:
/// `if cur_off < deliv_off then deliv_off else cur_off`.
#[must_use]
pub const fn pump_offset_monotone(cur_off: u64, deliv_off: u64) -> u64 {
    if cur_off < deliv_off {
        deliv_off
    } else {
        cur_off
    }
}

/// `wake_dispatch_seq_advance` as `wake_dispatch_island.rs` defines it in Clean:
/// `if prev_seq < cand_seq then cand_seq else prev_seq`.
#[must_use]
pub const fn wake_dispatch_seq_advance(prev_seq: u64, cand_seq: u64) -> u64 {
    if prev_seq < cand_seq {
        cand_seq
    } else {
        prev_seq
    }
}

/// `wake_task_payload_clamp` as `wake_dispatch_island.rs` defines it in Clean:
/// `if raw_len < max_len then raw_len else max_len`.
#[must_use]
pub const fn wake_task_payload_clamp(raw_len: u64, max_len: u64) -> u64 {
    if raw_len < max_len {
        raw_len
    } else {
        max_len
    }
}

/// `nested_turn_seq_advance` as `nested_drive_island.rs` defines it in Clean:
/// `if prev_turn < cand_turn then cand_turn else prev_turn`.
#[must_use]
pub const fn nested_turn_seq_advance(prev_turn: u64, cand_turn: u64) -> u64 {
    if prev_turn < cand_turn {
        cand_turn
    } else {
        prev_turn
    }
}

/// `nested_prompt_bytes_clamp` as `nested_drive_island.rs` defines it in Clean:
/// `if raw_len < max_len then raw_len else max_len`.
#[must_use]
pub const fn nested_prompt_bytes_clamp(raw_len: u64, max_len: u64) -> u64 {
    if raw_len < max_len {
        raw_len
    } else {
        max_len
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
        assert_eq!(answers(|[a, b]| crate::pump_offset_monotone(a, b)), want);
        assert_eq!(answers(|[a, b]| super::pump_offset_monotone(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::wake_dispatch::wake_dispatch_seq_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::wake_dispatch_seq_advance(a, b)),
            want
        );
        let want_clamp = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::wake_dispatch::wake_task_payload_clamp(a, b)),
            want_clamp
        );
        assert_eq!(
            answers(|[a, b]| super::wake_task_payload_clamp(a, b)),
            want_clamp
        );
        assert_eq!(
            answers(|[a, b]| crate::nested_drive::nested_turn_seq_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::nested_turn_seq_advance(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::nested_drive::nested_prompt_bytes_clamp(a, b)),
            want_clamp
        );
        assert_eq!(
            answers(|[a, b]| super::nested_prompt_bytes_clamp(a, b)),
            want_clamp
        );
    }

    // Not vacuous: `pump_offset_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
