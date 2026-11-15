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

/// `gate_violation_advance` as `gate_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn gate_violation_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// `manifest_claim_count_advance` as `manifest_island.rs` defines it in Clean:
/// `if prev < next then next else prev`.
#[must_use]
pub const fn manifest_claim_count_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// `needle_clamp_count` as `needles_island.rs` defines it in Clean:
/// `if count < max_count then count else max_count`.
#[must_use]
pub const fn needle_clamp_count(count: u64, max_count: u64) -> u64 {
    if count < max_count {
        count
    } else {
        max_count
    }
}

/// `render_clamp_span_start` as `render_island.rs` defines it in Clean:
/// `if begin_pos < end_pos then begin_pos else end_pos`.
#[must_use]
pub const fn render_clamp_span_start(begin_pos: u64, end_pos: u64) -> u64 {
    if begin_pos < end_pos {
        begin_pos
    } else {
        end_pos
    }
}

/// `claim_elapsed_clamp` as `timeout_island.rs` defines it in Clean:
/// `if elapsed_ms < limit_ms then elapsed_ms else limit_ms`.
#[must_use]
pub const fn claim_elapsed_clamp(elapsed_ms: u64, limit_ms: u64) -> u64 {
    if elapsed_ms < limit_ms {
        elapsed_ms
    } else {
        limit_ms
    }
}

/// `claim_timeout_floor` as `timeout_island.rs` defines it in Clean:
/// `if floor_ms < requested_ms then requested_ms else floor_ms`.
#[must_use]
pub const fn claim_timeout_floor(requested_ms: u64, floor_ms: u64) -> u64 {
    if floor_ms < requested_ms {
        requested_ms
    } else {
        floor_ms
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
            answers(|[a, b]| crate::gate::gate_violation_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::gate_violation_advance(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::manifest::manifest_claim_count_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::manifest_claim_count_advance(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::needles::needle_clamp_count(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::needle_clamp_count(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::render::render_clamp_span_start(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::render_clamp_span_start(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::timeout::claim_elapsed_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::claim_elapsed_clamp(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::timeout::claim_timeout_floor(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::claim_timeout_floor(a, b)), want);
    }

    // Not vacuous: `gate_violation_advance` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
