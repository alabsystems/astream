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

/// `fork_prefix_bound` as `fork_island.rs` defines it in Clean:
/// `if at_off < len then at_off else len`.
#[must_use]
pub const fn fork_prefix_bound(at_off: u64, len: u64) -> u64 {
    if at_off < len {
        at_off
    } else {
        len
    }
}

/// `cog_clamp_call_count` as `cog_island.rs` defines it in Clean:
/// `if count < max_calls then count else max_calls`.
#[must_use]
pub const fn cog_clamp_call_count(count: u64, max_calls: u64) -> u64 {
    if count < max_calls {
        count
    } else {
        max_calls
    }
}

/// `envelope_clamp_call_cap` as `envelope_island.rs` defines it in Clean:
/// `if n < max_cap then n else max_cap`.
#[must_use]
pub const fn envelope_clamp_call_cap(n: u64, max_cap: u64) -> u64 {
    if n < max_cap {
        n
    } else {
        max_cap
    }
}

/// `fixture_clamp_transcript_len` as `fixtures_island.rs` defines it in Clean:
/// `if len < max_len then len else max_len`.
#[must_use]
pub const fn fixture_clamp_transcript_len(len: u64, max_len: u64) -> u64 {
    if len < max_len {
        len
    } else {
        max_len
    }
}

/// `turn_step_advance` as `turn_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn turn_step_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// `unified_reached_advance` as `unified_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn unified_reached_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// `fleet_clamp_cut_len` as `fleet_island.rs` defines it in Clean:
/// `if cut_len < total then cut_len else total`.
#[must_use]
pub const fn fleet_clamp_cut_len(cut_len: u64, total: u64) -> u64 {
    if cut_len < total {
        cut_len
    } else {
        total
    }
}

/// `foreign_tape_cursor_advance` as `foreign_tape_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn foreign_tape_cursor_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// `foreign_tape_clamp_records` as `foreign_tape_island.rs` defines it in Clean:
/// `if count < max_records then count else max_records`.
#[must_use]
pub const fn foreign_tape_clamp_records(count: u64, max_records: u64) -> u64 {
    if count < max_records {
        count
    } else {
        max_records
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
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::fork::fork_prefix_bound(a, b)), want);
        assert_eq!(answers(|[a, b]| super::fork_prefix_bound(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::cog::cog_clamp_call_count(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::cog_clamp_call_count(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::envelope::envelope_clamp_call_cap(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::envelope_clamp_call_cap(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::fixtures::fixture_clamp_transcript_len(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::fixture_clamp_transcript_len(a, b)),
            want
        );
        let want = "012112222";
        assert_eq!(answers(|[a, b]| crate::turn::turn_step_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::turn_step_advance(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::unified::unified_reached_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::unified_reached_advance(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::fleet::fleet_clamp_cut_len(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::fleet_clamp_cut_len(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::foreign_tape::foreign_tape_cursor_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::foreign_tape_cursor_advance(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::foreign_tape::foreign_tape_clamp_records(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::foreign_tape_clamp_records(a, b)),
            want
        );
    }

    // Not vacuous: `fork_prefix_bound` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { b } else { a }), "000011012");
    }
}
