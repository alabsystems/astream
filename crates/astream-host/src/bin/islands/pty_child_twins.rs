// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions `pty_child_island.rs` compiles from Clean, for the
//! `pty_child` binary under a compiler that cannot lex the island (see the crate's
//! `src/twins.rs`). The test holds the twin, and whichever function the build calls, to
//! the answers the island gives, which every Trust test run re-checks against it.

/// `pty_child_clamp_len` as `pty_child_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn pty_child_clamp_len(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
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
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::pty_child_clamp_len(a, b)), want);
        assert_eq!(answers(|[a, b]| super::pty_child_clamp_len(a, b)), want);
    }

    // Not vacuous: `pty_child_clamp_len` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { b } else { a }), "000011012");
    }
}
