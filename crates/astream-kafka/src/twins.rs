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

/// `kafka_clamp_str_len` as `kafka_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn kafka_clamp_str_len(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
    }
}

/// `kafka_negotiate_error_code` as `kafka_island.rs` defines it in Clean:
/// `if max_ver < req_ver then unsupported_code else none_code`.
#[must_use]
pub const fn kafka_negotiate_error_code(
    req_ver: u64,
    max_ver: u64,
    unsupported_code: u64,
    none_code: u64,
) -> u64 {
    if max_ver < req_ver {
        unsupported_code
    } else {
        none_code
    }
}

/// `kafka_batch_offset_advance` as `batch_island.rs` defines it in Clean:
/// `if cur_head < next_head then next_head else cur_head`.
#[must_use]
pub const fn kafka_batch_offset_advance(cur_head: u64, next_head: u64) -> u64 {
    if cur_head < next_head {
        next_head
    } else {
        cur_head
    }
}

/// `kafka_fetch_clamp_bytes` as `batch_island.rs` defines it in Clean:
/// `if avail < max_bytes then avail else max_bytes`.
#[must_use]
pub const fn kafka_fetch_clamp_bytes(avail: u64, max_bytes: u64) -> u64 {
    if avail < max_bytes {
        avail
    } else {
        max_bytes
    }
}

/// `kafka_generation_advance` as `group_island.rs` defines it in Clean:
/// `if cur_gen < next_gen then next_gen else cur_gen`.
#[must_use]
pub const fn kafka_generation_advance(cur_gen: u64, next_gen: u64) -> u64 {
    if cur_gen < next_gen {
        next_gen
    } else {
        cur_gen
    }
}

/// `kafka_partition_clamp` as `group_island.rs` defines it in Clean:
/// `if requested < max_parts then requested else max_parts`.
#[must_use]
pub const fn kafka_partition_clamp(requested: u64, max_parts: u64) -> u64 {
    if requested < max_parts {
        requested
    } else {
        max_parts
    }
}

/// `kafka_compact_len_clamp` as `compact_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn kafka_compact_len_clamp(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
    }
}

/// `kafka_decompress_cap_clamp` as `compact_island.rs` defines it in Clean:
/// `if decoded_len < max_cap then decoded_len else max_cap`.
#[must_use]
pub const fn kafka_decompress_cap_clamp(decoded_len: u64, max_cap: u64) -> u64 {
    if decoded_len < max_cap {
        decoded_len
    } else {
        max_cap
    }
}

/// `kafka_sasl_phase_advance` as `sasl_island.rs` defines it in Clean:
/// `if cur_phase < next_phase then next_phase else cur_phase`.
#[must_use]
pub const fn kafka_sasl_phase_advance(cur_phase: u64, next_phase: u64) -> u64 {
    if cur_phase < next_phase {
        next_phase
    } else {
        cur_phase
    }
}

/// `kafka_sasl_pbkdf2_clamp` as `sasl_island.rs` defines it in Clean:
/// `if iters < max_iters then iters else max_iters`.
#[must_use]
pub const fn kafka_sasl_pbkdf2_clamp(iters: u64, max_iters: u64) -> u64 {
    if iters < max_iters {
        iters
    } else {
        max_iters
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
        assert_eq!(answers(|[a, b]| crate::kafka_clamp_str_len(a, b)), want);
        assert_eq!(answers(|[a, b]| super::kafka_clamp_str_len(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::compress::kafka_compact_len_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::kafka_compact_len_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::compress::kafka_decompress_cap_clamp(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::kafka_decompress_cap_clamp(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| crate::record_batch::kafka_fetch_clamp_bytes(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::kafka_fetch_clamp_bytes(a, b)), want);
        let want_adv = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::record_batch::kafka_batch_offset_advance(a, b)),
            want_adv
        );
        assert_eq!(
            answers(|[a, b]| super::kafka_batch_offset_advance(a, b)),
            want_adv
        );
        assert_eq!(
            answers(|[a, b]| crate::server::kafka_generation_advance(a, b)),
            want_adv
        );
        assert_eq!(
            answers(|[a, b]| super::kafka_generation_advance(a, b)),
            want_adv
        );
        assert_eq!(
            answers(|[a, b]| crate::server::kafka_partition_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::kafka_partition_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::sasl::kafka_sasl_pbkdf2_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::kafka_sasl_pbkdf2_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::sasl::kafka_sasl_phase_advance(a, b)),
            want_adv
        );
        assert_eq!(
            answers(|[a, b]| super::kafka_sasl_phase_advance(a, b)),
            want_adv
        );
        let want =
            "012012012012012012012012012000111222012012012012012012000111222000111222012012012";
        assert_eq!(
            answers(|[a, b, c, d]| crate::kafka_negotiate_error_code(a, b, c, d)),
            want
        );
        assert_eq!(
            answers(|[a, b, c, d]| super::kafka_negotiate_error_code(a, b, c, d)),
            want
        );
    }

    // Not vacuous: `kafka_clamp_str_len` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { b } else { a }), "000011012");
    }
}
