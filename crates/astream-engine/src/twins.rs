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

/// `control_handoff_holder` as `control_island.rs` defines it in Clean:
/// `next_holder`.
#[must_use]
pub const fn control_handoff_holder(_cur_holder: u64, next_holder: u64) -> u64 {
    next_holder
}

/// `journal_committed_monotone` as `durable_island.rs` defines it in Clean:
/// `if cur_steps < next_steps then next_steps else cur_steps`.
#[must_use]
pub const fn journal_committed_monotone(cur_steps: u64, next_steps: u64) -> u64 {
    if cur_steps < next_steps {
        next_steps
    } else {
        cur_steps
    }
}

/// `journal_step_match_or_keep` as `durable_island.rs` defines it in Clean:
/// `if step_index == cur_steps then next_steps else cur_steps`.
#[must_use]
pub const fn journal_step_match_or_keep(step_index: u64, cur_steps: u64, next_steps: u64) -> u64 {
    if step_index == cur_steps {
        next_steps
    } else {
        cur_steps
    }
}

/// `logical_clock_advance_past_tick` as `effects_island.rs` defines it in Clean:
/// `if cur_tick < next_ts then next_ts else cur_tick`.
#[must_use]
pub const fn logical_clock_advance_past_tick(cur_tick: u64, _ts: u64, next_ts: u64) -> u64 {
    if cur_tick < next_ts {
        next_ts
    } else {
        cur_tick
    }
}

/// `envelope_clamp_cause_len` as `envelope_island.rs` defines it in Clean:
/// `if raw_len < max_len then raw_len else max_len`.
#[must_use]
pub const fn envelope_clamp_cause_len(raw_len: u64, max_len: u64) -> u64 {
    if raw_len < max_len {
        raw_len
    } else {
        max_len
    }
}

/// `fleet_clamp_to_cut` as `fleet_island.rs` defines it in Clean:
/// `if seq < cut_off then seq else cut_off`.
#[must_use]
pub const fn fleet_clamp_to_cut(seq: u64, cut_off: u64) -> u64 {
    if seq < cut_off {
        seq
    } else {
        cut_off
    }
}

/// `fork_clamped_index` as `fork_island.rs` defines it in Clean:
/// `if idx < len then idx else len`.
#[must_use]
pub const fn fork_clamped_index(idx: u64, len: u64) -> u64 {
    if idx < len {
        idx
    } else {
        len
    }
}

/// `log_advance_offset_monotone` as `log_island.rs` defines it in Clean:
/// `if cur_next < assigned_next then assigned_next else cur_next`.
#[must_use]
pub const fn log_advance_offset_monotone(cur_next: u64, assigned_next: u64) -> u64 {
    if cur_next < assigned_next {
        assigned_next
    } else {
        cur_next
    }
}

/// `session_bump_high_water` as `session_island.rs` defines it in Clean:
/// `if cur_hw < client_seq then client_seq else cur_hw`.
#[must_use]
pub const fn session_bump_high_water(cur_hw: u64, client_seq: u64) -> u64 {
    if cur_hw < client_seq {
        client_seq
    } else {
        cur_hw
    }
}

/// `store_advance_valid_len` as `store_island.rs` defines it in Clean:
/// `if cur_len < next_len then next_len else cur_len`.
#[must_use]
pub const fn store_advance_valid_len(cur_len: u64, next_len: u64) -> u64 {
    if cur_len < next_len {
        next_len
    } else {
        cur_len
    }
}

/// `merkle_parent_count_clamp` as `merkle_island.rs` defines it in Clean:
/// `if raw_parents < max_parents then raw_parents else max_parents`.
#[must_use]
pub const fn merkle_parent_count_clamp(raw_parents: u64, max_parents: u64) -> u64 {
    if raw_parents < max_parents {
        raw_parents
    } else {
        max_parents
    }
}

/// `dag_committed_advance` as `dag_island.rs` defines it in Clean:
/// `if cur_committed < next_committed then next_committed else cur_committed`.
#[must_use]
pub const fn dag_committed_advance(cur_committed: u64, next_committed: u64) -> u64 {
    if cur_committed < next_committed {
        next_committed
    } else {
        cur_committed
    }
}

/// `dist_lease_expiry_advance` as `dist_dag_island.rs` defines it in Clean:
/// `if cur_expiry < proposed_expiry then proposed_expiry else cur_expiry`.
#[must_use]
pub const fn dist_lease_expiry_advance(cur_expiry: u64, proposed_expiry: u64) -> u64 {
    if cur_expiry < proposed_expiry {
        proposed_expiry
    } else {
        cur_expiry
    }
}

/// `dist_winner_offset_min` as `dist_dag_island.rs` defines it in Clean:
/// `if candidate_offset < cur_winner then candidate_offset else cur_winner`.
#[must_use]
pub const fn dist_winner_offset_min(cur_winner: u64, candidate_offset: u64) -> u64 {
    if candidate_offset < cur_winner {
        candidate_offset
    } else {
        cur_winner
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
        let want = "012012012";
        assert_eq!(
            answers(|[a, b]| crate::control::control_handoff_holder(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::control_handoff_holder(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::durable::journal_committed_monotone(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::journal_committed_monotone(a, b)),
            want
        );
        let want = "012111222000012222000111012";
        assert_eq!(
            answers(|[a, b, c]| crate::durable::journal_step_match_or_keep(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::journal_step_match_or_keep(a, b, c)),
            want
        );
        let want = "012012012112112112222222222";
        assert_eq!(
            answers(|[a, b, c]| crate::effects::logical_clock_advance_past_tick(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::logical_clock_advance_past_tick(a, b, c)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::envelope::envelope_clamp_cause_len(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::envelope_clamp_cause_len(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::fleet::fleet_clamp_to_cut(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::fleet_clamp_to_cut(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::fork::fork_clamped_index(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::fork_clamped_index(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::log::log_advance_offset_monotone(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::log_advance_offset_monotone(a, b)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::session::session_bump_high_water(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::session_bump_high_water(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::store::store_advance_valid_len(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::store_advance_valid_len(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::merkle::merkle_parent_count_clamp(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::merkle_parent_count_clamp(a, b)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::dag::dag_committed_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::dag_committed_advance(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::distributed::dist_lease_expiry_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::dist_lease_expiry_advance(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::distributed::dist_winner_offset_min(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::dist_winner_offset_min(a, b)), want);
    }

    // Not vacuous: `journal_committed_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
