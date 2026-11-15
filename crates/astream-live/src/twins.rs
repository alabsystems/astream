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

/// `live_bridge_advance_step` as `live_island.rs` defines it in Clean:
/// `if cur_step < next_step then next_step else cur_step`.
#[must_use]
pub const fn live_bridge_advance_step(cur_step: u64, next_step: u64) -> u64 {
    if cur_step < next_step {
        next_step
    } else {
        cur_step
    }
}

/// `json_clamp_depth` as `json_island.rs` defines it in Clean:
/// `if depth < max_depth then depth else max_depth`.
#[must_use]
pub const fn json_clamp_depth(depth: u64, max_depth: u64) -> u64 {
    if depth < max_depth {
        depth
    } else {
        max_depth
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
            answers(|[a, b]| crate::live_bridge_advance_step(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::live_bridge_advance_step(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::json::json_clamp_depth(a, b)), want);
        assert_eq!(answers(|[a, b]| super::json_clamp_depth(a, b)), want);
    }

    // Not vacuous: `live_bridge_advance_step` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
