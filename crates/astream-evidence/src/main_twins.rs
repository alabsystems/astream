// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions `main_island.rs` compiles from Clean, for the
//! `main` binary under a compiler that cannot lex the island (see the crate's
//! `src/twins.rs`). The test holds the twin, and whichever function the build calls, to
//! the answers the island gives, which every Trust test run re-checks against it.

/// `cli_passed_advance` as `main_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn cli_passed_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
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
        assert_eq!(answers(|[a, b]| crate::cli_passed_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::cli_passed_advance(a, b)), want);
    }

    // Not vacuous: `cli_passed_advance` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
