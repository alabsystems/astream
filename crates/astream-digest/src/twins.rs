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

/// `sha256_partial_take` as `digest_island.rs` defines it in Clean:
/// `if data_len < avail then data_len else avail`.
#[must_use]
pub const fn sha256_partial_take(avail: u64, data_len: u64) -> u64 {
    if data_len < avail {
        data_len
    } else {
        avail
    }
}

/// `sha256_clamp_partial_len` as `digest_island.rs` defines it in Clean:
/// `if buf_len < max_partial then buf_len else max_partial`.
#[must_use]
pub const fn sha256_clamp_partial_len(buf_len: u64, max_partial: u64) -> u64 {
    if buf_len < max_partial {
        buf_len
    } else {
        max_partial
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
        assert_eq!(answers(|[a, b]| crate::sha256_partial_take(a, b)), want);
        assert_eq!(answers(|[a, b]| super::sha256_partial_take(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::sha256_clamp_partial_len(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::sha256_clamp_partial_len(a, b)),
            want
        );
    }

    // Not vacuous: `sha256_partial_take` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if b < a { a } else { b }), "000011012");
    }
}
