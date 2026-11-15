// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twin of `asb_drain_count_advance` (`bin/islands/asb_island.rs`).

/// `asb_drain_count_advance` as `asb_island.rs` defines it in Clean:
/// `if cur < next then next else cur`.
#[must_use]
pub const fn asb_drain_count_advance(cur: u64, next: u64) -> u64 {
    if cur < next {
        next
    } else {
        cur
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
        let want = "012112222";
        assert_eq!(answers(|[a, b]| crate::asb_drain_count_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::asb_drain_count_advance(a, b)), want);
    }

    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
