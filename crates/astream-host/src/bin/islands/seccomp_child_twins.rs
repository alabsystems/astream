// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions `seccomp_child_island.rs` compiles from Clean, for the
//! `seccomp_child` binary under a compiler that cannot lex the island.

/// `seccomp_child_clamp_read` as `seccomp_child_island.rs` defines it in Clean:
/// `if got < cap then got else cap`.
#[must_use]
pub const fn seccomp_child_clamp_read(got: u64, cap: u64) -> u64 {
    if got < cap {
        got
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

    #[test]
    fn the_twins_answer_as_the_islands_do() {
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::seccomp_child_clamp_read(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::seccomp_child_clamp_read(a, b)),
            want
        );
    }

    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { b } else { a }), "000011012");
    }
}
