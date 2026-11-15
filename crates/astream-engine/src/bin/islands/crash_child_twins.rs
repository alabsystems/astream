// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions `crash_child_island.rs` compiles from Clean, for the
//! `crash_child` binary under a compiler that cannot lex the island (see the crate's
//! `src/twins.rs`). The test holds the twin, and whichever function the build calls, to
//! the answers the island gives, which every Trust test run re-checks against it.

/// `crash_child_advance_seq` as `crash_child_island.rs` defines it in Clean:
/// `if seq < next then next else seq`.
#[must_use]
pub const fn crash_child_advance_seq(seq: u64, next: u64) -> u64 {
    if seq < next {
        next
    } else {
        seq
    }
}

#[cfg(test)]
#[path = "../../../../astream-wire/twin_answers.rs"]
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
        assert_eq!(answers(|[a, b]| crate::crash_child_advance_seq(a, b)), want);
        assert_eq!(answers(|[a, b]| super::crash_child_advance_seq(a, b)), want);
    }

    // Not vacuous: `crash_child_advance_seq` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
