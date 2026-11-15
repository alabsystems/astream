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

/// `aead_seq_monotone` as `stream_island.rs` defines it in Clean:
/// `if cur_seq < next_seq then next_seq else cur_seq`.
#[cfg(feature = "stream")]
#[must_use]
pub const fn aead_seq_monotone(cur_seq: u64, next_seq: u64) -> u64 {
    if cur_seq < next_seq {
        next_seq
    } else {
        cur_seq
    }
}

/// `aead_clamp_sealed_len` as `aead_island.rs` defines it in Clean:
/// `if overhead < sealed_len then sealed_len else overhead`.
#[must_use]
pub const fn aead_clamp_sealed_len(overhead: u64, sealed_len: u64) -> u64 {
    if overhead < sealed_len {
        sealed_len
    } else {
        overhead
    }
}

/// `handshake_clamp_info_len` as `handshake_island.rs` defines it in Clean:
/// `if max_len < len then max_len else len`.
#[cfg(feature = "handshake")]
#[must_use]
pub const fn handshake_clamp_info_len(len: u64, max_len: u64) -> u64 {
    if max_len < len {
        max_len
    } else {
        len
    }
}

/// `roam_amp_budget_clamp` as `roam_island.rs` defines it in Clean:
/// `if tx_cand < budget_cap then tx_cand else budget_cap`.
#[cfg(feature = "handshake")]
#[must_use]
pub const fn roam_amp_budget_clamp(tx_cand: u64, budget_cap: u64) -> u64 {
    if tx_cand < budget_cap {
        tx_cand
    } else {
        budget_cap
    }
}

/// `roam_epoch_advance` as `roam_island.rs` defines it in Clean:
/// `if prev < cand then cand else prev`.
#[cfg(feature = "handshake")]
#[must_use]
pub const fn roam_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

/// `identity_clamp_ctx_len` as `identity_island.rs` defines it in Clean:
/// `if max_len < len then max_len else len`.
#[cfg(feature = "identity")]
#[must_use]
pub const fn identity_clamp_ctx_len(len: u64, max_len: u64) -> u64 {
    if max_len < len {
        max_len
    } else {
        len
    }
}

/// `cert_validity_clamp` as `cert_island.rs` defines it in Clean:
/// `if raw < cap then raw else cap`.
#[cfg(feature = "identity")]
#[must_use]
pub const fn cert_validity_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

/// `cert_epoch_advance` as `cert_island.rs` defines it in Clean:
/// `if prev < cand then cand else prev`.
#[cfg(feature = "identity")]
#[must_use]
pub const fn cert_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
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
        #[cfg(feature = "stream")]
        {
            let want = "012112222";
            assert_eq!(
                answers(|[a, b]| crate::stream::aead_seq_monotone(a, b)),
                want
            );
            assert_eq!(answers(|[a, b]| super::aead_seq_monotone(a, b)), want);
        }
        let want = "012112222";
        assert_eq!(answers(|[a, b]| crate::aead_clamp_sealed_len(a, b)), want);
        assert_eq!(answers(|[a, b]| super::aead_clamp_sealed_len(a, b)), want);
        #[cfg(feature = "handshake")]
        {
            let want = "000011012";
            assert_eq!(
                answers(|[a, b]| crate::handshake::handshake_clamp_info_len(a, b)),
                want
            );
            assert_eq!(
                answers(|[a, b]| super::handshake_clamp_info_len(a, b)),
                want
            );
            assert_eq!(
                answers(|[a, b]| crate::roam::roam_amp_budget_clamp(a, b)),
                want
            );
            assert_eq!(answers(|[a, b]| super::roam_amp_budget_clamp(a, b)), want);
            let want_mono = "012112222";
            assert_eq!(
                answers(|[a, b]| crate::roam::roam_epoch_advance(a, b)),
                want_mono
            );
            assert_eq!(answers(|[a, b]| super::roam_epoch_advance(a, b)), want_mono);
        }
        #[cfg(feature = "identity")]
        {
            let want = "000011012";
            assert_eq!(
                answers(|[a, b]| crate::identity::identity_clamp_ctx_len(a, b)),
                want
            );
            assert_eq!(answers(|[a, b]| super::identity_clamp_ctx_len(a, b)), want);
            assert_eq!(
                answers(|[a, b]| crate::cert::cert_validity_clamp(a, b)),
                want
            );
            assert_eq!(answers(|[a, b]| super::cert_validity_clamp(a, b)), want);
            let want_mono = "012112222";
            assert_eq!(
                answers(|[a, b]| crate::cert::cert_epoch_advance(a, b)),
                want_mono
            );
            assert_eq!(answers(|[a, b]| super::cert_epoch_advance(a, b)), want_mono);
        }
    }

    // Not vacuous: `aead_seq_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
