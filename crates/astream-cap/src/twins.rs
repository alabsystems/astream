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

/// `cap_clock_advance_monotone` as `cap_island.rs` defines it in Clean:
/// `if cur_ms < sample_ms then sample_ms else cur_ms`.
#[must_use]
pub const fn cap_clock_advance_monotone(cur_ms: u64, sample_ms: u64) -> u64 {
    if cur_ms < sample_ms {
        sample_ms
    } else {
        cur_ms
    }
}

/// `attenuate_expiry_min` as `cap_island.rs` defines it in Clean:
/// `if parent_exp < child_exp then parent_exp else child_exp`.
#[must_use]
pub const fn attenuate_expiry_min(parent_exp: u64, child_exp: u64) -> u64 {
    if parent_exp < child_exp {
        parent_exp
    } else {
        child_exp
    }
}

/// `live_expiry_or_zero` as `cap_island.rs` defines it in Clean:
/// `if exp <= now_ms then zero_val else exp`.
#[must_use]
pub const fn live_expiry_or_zero(exp: u64, now_ms: u64, zero_val: u64) -> u64 {
    if exp <= now_ms {
        zero_val
    } else {
        exp
    }
}

/// `ceiling_rule_index_clamp` as `ceiling_island.rs` defines it in Clean:
/// `if idx < max_rules then idx else max_rules`.
#[must_use]
pub const fn ceiling_rule_index_clamp(idx: u64, max_rules: u64) -> u64 {
    if idx < max_rules {
        idx
    } else {
        max_rules
    }
}

/// `ceiling_mode_subsumes_code` as `ceiling_island.rs` defines it in Clean:
/// `if ceiling_rw < member_rw then 0 else 1`.
#[must_use]
pub const fn ceiling_mode_subsumes_code(ceiling_rw: u64, member_rw: u64) -> u64 {
    if ceiling_rw < member_rw {
        0
    } else {
        1
    }
}

/// `capfile_line_advance` as `capfile_island.rs` defines it in Clean:
/// `if cur < cand then cand else cur`.
///
/// Test-only: the twin a stock build calls is `capfile.rs`'s own, inline, because `asb`
/// compiles that file by path and it can reach no `crate::` item. This copy lets a Trust
/// test run, where `capfile.rs`'s twin is not compiled, hold the definition to the
/// island's answers; outside tests nothing calls it, and `#![deny(dead_code)]` refuses it.
#[cfg(test)]
#[must_use]
pub const fn capfile_line_advance(cur: u64, cand: u64) -> u64 {
    if cur < cand {
        cand
    } else {
        cur
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
            answers(|[a, b]| crate::cap_clock_advance_monotone(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::cap_clock_advance_monotone(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::attenuate_expiry_min(a, b)), want);
        assert_eq!(answers(|[a, b]| super::attenuate_expiry_min(a, b)), want);
        let want = "012012012111012012222222012";
        assert_eq!(
            answers(|[a, b, c]| crate::live_expiry_or_zero(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::live_expiry_or_zero(a, b, c)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::capfile::capfile_line_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::capfile_line_advance(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::ceiling_rule_index_clamp(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::ceiling_rule_index_clamp(a, b)),
            want
        );
        let want = "100110111";
        assert_eq!(
            answers(|[a, b]| crate::ceiling_mode_subsumes_code(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::ceiling_mode_subsumes_code(a, b)),
            want
        );
    }

    // Not vacuous: `cap_clock_advance_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
