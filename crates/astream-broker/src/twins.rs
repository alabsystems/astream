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

/// `group_commit_monotone` as `proto_island.rs` defines it in Clean:
/// `if cur_upto < req_upto then req_upto else cur_upto`.
#[must_use]
pub const fn group_commit_monotone(cur_upto: u64, req_upto: u64) -> u64 {
    if cur_upto < req_upto {
        req_upto
    } else {
        cur_upto
    }
}

/// `high_water_monotone` as `proto_island.rs` defines it in Clean:
/// `if cur_hw < seq then seq else cur_hw`.
#[must_use]
pub const fn high_water_monotone(cur_hw: u64, seq: u64) -> u64 {
    if cur_hw < seq {
        seq
    } else {
        cur_hw
    }
}

/// `compact_floor_monotone` as `proto_island.rs` defines it in Clean:
/// `if base_off < req_min then req_min else base_off`.
#[must_use]
pub const fn compact_floor_monotone(req_min: u64, base_off: u64) -> u64 {
    if base_off < req_min {
        req_min
    } else {
        base_off
    }
}

/// `epoch_advance_monotone` as `proto_island.rs` defines it in Clean:
/// `if cur_epoch < req_epoch then req_epoch else cur_epoch`.
#[must_use]
pub const fn epoch_advance_monotone(cur_epoch: u64, req_epoch: u64) -> u64 {
    if cur_epoch < req_epoch {
        req_epoch
    } else {
        cur_epoch
    }
}

/// `replica_ack_monotone` as `proto_island.rs` defines it in Clean:
/// `if cur_ack < new_ack then new_ack else cur_ack`.
#[must_use]
pub const fn replica_ack_monotone(cur_ack: u64, new_ack: u64) -> u64 {
    if cur_ack < new_ack {
        new_ack
    } else {
        cur_ack
    }
}

/// `committed_watermark` as `proto_island.rs` defines it in Clean:
/// `if head_offset < replica_ack then head_offset else replica_ack`.
#[must_use]
pub const fn committed_watermark(head_offset: u64, replica_ack: u64) -> u64 {
    if head_offset < replica_ack {
        head_offset
    } else {
        replica_ack
    }
}

/// `credit_horizon_monotone` as `proto_island.rs` defines it in Clean:
/// `if cur_horizon < new_horizon then new_horizon else cur_horizon`.
#[must_use]
pub const fn credit_horizon_monotone(cur_horizon: u64, new_horizon: u64) -> u64 {
    if cur_horizon < new_horizon {
        new_horizon
    } else {
        cur_horizon
    }
}

/// `fenced_ack_select` as `proto_island.rs` defines it in Clean:
/// `if req_epoch < leader_epoch then cur_ack else healed_ack`.
#[must_use]
pub const fn fenced_ack_select(
    req_epoch: u64,
    leader_epoch: u64,
    cur_ack: u64,
    healed_ack: u64,
) -> u64 {
    if req_epoch < leader_epoch {
        cur_ack
    } else {
        healed_ack
    }
}

/// `window_gate_send` as `proto_island.rs` defines it in Clean:
/// `if sent_seq < credit_horizon then clamped_cand else fallback_sent`.
#[must_use]
pub const fn window_gate_send(
    sent_seq: u64,
    credit_horizon: u64,
    clamped_cand: u64,
    fallback_sent: u64,
) -> u64 {
    if sent_seq < credit_horizon {
        clamped_cand
    } else {
        fallback_sent
    }
}

/// `brecord_clamp_body_len` as `brecord_island.rs` defines it in Clean:
/// `if len < max_len then len else max_len`.
#[must_use]
pub const fn brecord_clamp_body_len(len: u64, max_len: u64) -> u64 {
    if len < max_len {
        len
    } else {
        max_len
    }
}

/// `logid_generation_advance` as `logid_island.rs` defines it in Clean:
/// `if cur_gen < next_gen then next_gen else cur_gen`.
#[must_use]
pub const fn logid_generation_advance(cur_gen: u64, next_gen: u64) -> u64 {
    if cur_gen < next_gen {
        next_gen
    } else {
        cur_gen
    }
}

/// `recover_unit_start_advance` as `recover_island.rs` defines it in Clean:
/// `if seal_end < floor then floor else seal_end`.
#[must_use]
pub const fn recover_unit_start_advance(seal_end: u64, floor: u64) -> u64 {
    if seal_end < floor {
        floor
    } else {
        seal_end
    }
}

/// `storage_len_advance` as `storage_island.rs` defines it in Clean:
/// `if cur_len < next_len then next_len else cur_len`.
#[must_use]
pub const fn storage_len_advance(cur_len: u64, next_len: u64) -> u64 {
    if cur_len < next_len {
        next_len
    } else {
        cur_len
    }
}

/// `sharded_clamp_index` as `sharded_island.rs` defines it in Clean:
/// `if idx < shards then idx else shards`.
#[must_use]
pub const fn sharded_clamp_index(idx: u64, shards: u64) -> u64 {
    if idx < shards {
        idx
    } else {
        shards
    }
}

/// `store_head_advance` as `store_island.rs` defines it in Clean:
/// `if cur_head < next_head then next_head else cur_head`.
#[must_use]
pub const fn store_head_advance(cur_head: u64, next_head: u64) -> u64 {
    if cur_head < next_head {
        next_head
    } else {
        cur_head
    }
}

/// `client_walk_page_advance` as `client_island.rs` defines it in Clean:
/// `if cur_pages < next_pages then next_pages else cur_pages`.
#[must_use]
pub const fn client_walk_page_advance(cur_pages: u64, next_pages: u64) -> u64 {
    if cur_pages < next_pages {
        next_pages
    } else {
        cur_pages
    }
}

/// `broker_batch_clamp` as `broker_island.rs` defines it in Clean:
/// `if queued < max_batch then queued else max_batch`.
#[must_use]
pub const fn broker_batch_clamp(queued: u64, max_batch: u64) -> u64 {
    if queued < max_batch {
        queued
    } else {
        max_batch
    }
}

/// `broker_bt_advance` as `bt_island.rs` defines it in Clean:
/// `if prev_bt < wall_ms then wall_ms else prev_bt`.
#[must_use]
pub const fn broker_bt_advance(prev_bt: u64, wall_ms: u64) -> u64 {
    if prev_bt < wall_ms {
        wall_ms
    } else {
        prev_bt
    }
}

/// `at_rest_version_advance` as `at_rest_island.rs` defines it in Clean:
/// `if prev_ver < next_ver then next_ver else prev_ver`.
#[must_use]
pub const fn at_rest_version_advance(prev_ver: u64, next_ver: u64) -> u64 {
    if prev_ver < next_ver {
        next_ver
    } else {
        prev_ver
    }
}

/// `tail_wake_head_advance` as `tail_wake_island.rs` defines it in Clean:
/// `if cur_matched < new_vis then new_vis else cur_matched`.
#[must_use]
pub const fn tail_wake_head_advance(cur_matched: u64, new_vis: u64) -> u64 {
    if cur_matched < new_vis {
        new_vis
    } else {
        cur_matched
    }
}

/// `tail_skip_clamp` as `tail_wake_island.rs` defines it in Clean:
/// `if cand_skip < vis_head then cand_skip else vis_head`.
#[must_use]
pub const fn tail_skip_clamp(cand_skip: u64, vis_head: u64) -> u64 {
    if cand_skip < vis_head {
        cand_skip
    } else {
        vis_head
    }
}

/// `rate_tokens_clamp` as `rate_island.rs` defines it in Clean:
/// `if cand_tokens < burst then cand_tokens else burst`.
#[must_use]
pub const fn rate_tokens_clamp(cand_tokens: u64, burst: u64) -> u64 {
    if cand_tokens < burst {
        cand_tokens
    } else {
        burst
    }
}

/// `rate_clock_advance` as `rate_island.rs` defines it in Clean:
/// `if prev_ms < now_ms then now_ms else prev_ms`.
#[must_use]
pub const fn rate_clock_advance(prev_ms: u64, now_ms: u64) -> u64 {
    if prev_ms < now_ms {
        now_ms
    } else {
        prev_ms
    }
}

/// `federation_cursor_advance` as `federation_island.rs` defines it in Clean:
/// `if cur_cursor < next_cursor then next_cursor else cur_cursor`.
#[must_use]
pub const fn federation_cursor_advance(cur_cursor: u64, next_cursor: u64) -> u64 {
    if cur_cursor < next_cursor {
        next_cursor
    } else {
        cur_cursor
    }
}

/// `federation_seq_clamp` as `federation_island.rs` defines it in Clean:
/// `if src_offset < max_seq then src_offset else max_seq`.
#[must_use]
pub const fn federation_seq_clamp(src_offset: u64, max_seq: u64) -> u64 {
    if src_offset < max_seq {
        src_offset
    } else {
        max_seq
    }
}

/// `federation_commit_bound` as `federation_island.rs` defines it in Clean:
/// `if upto < held then upto else held`.
#[must_use]
pub const fn federation_commit_bound(upto: u64, held: u64) -> u64 {
    if upto < held {
        upto
    } else {
        held
    }
}

/// `relay_floor_raise` as `relay_island.rs` defines it in Clean:
/// `if floor < seq then seq else floor`.
#[cfg(any(test, all(feature = "retention", feature = "relay")))]
#[must_use]
pub const fn relay_floor_raise(floor: u64, seq: u64) -> u64 {
    if floor < seq {
        seq
    } else {
        floor
    }
}

/// `relay_floor_admits` as `relay_island.rs` defines it in Clean:
/// `if floor < seq then 1 else 0`.
#[must_use]
pub const fn relay_floor_admits(floor: u64, seq: u64) -> u64 {
    if floor < seq {
        1
    } else {
        0
    }
}

/// `failover_epoch_advance` as `failover_island.rs` defines it in Clean:
/// `if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch`.
#[must_use]
pub const fn failover_epoch_advance(cur_epoch: u64, proposed_epoch: u64) -> u64 {
    if cur_epoch < proposed_epoch {
        proposed_epoch
    } else {
        cur_epoch
    }
}

/// `failover_quorum_clamp` as `failover_island.rs` defines it in Clean:
/// `if votes < cluster_size then votes else cluster_size`.
#[must_use]
pub const fn failover_quorum_clamp(votes: u64, cluster_size: u64) -> u64 {
    if votes < cluster_size {
        votes
    } else {
        cluster_size
    }
}

/// `refill_join_cursor_max` as `refill_island.rs` defines it in Clean:
/// `if inbox_oldest < lane_from then lane_from else inbox_oldest`.
#[must_use]
pub const fn refill_join_cursor_max(lane_from: u64, inbox_oldest: u64) -> u64 {
    if inbox_oldest < lane_from {
        lane_from
    } else {
        inbox_oldest
    }
}

/// `refill_debt_clamp` as `refill_island.rs` defines it in Clean:
/// `if debt < slack then debt else slack`.
#[must_use]
pub const fn refill_debt_clamp(debt: u64, slack: u64) -> u64 {
    if debt < slack {
        debt
    } else {
        slack
    }
}

/// `sticky_fence_min_seq` as `sticky_fence_island.rs` defines it in Clean:
/// `if cur_fence < failed_seq then cur_fence else failed_seq`.
#[must_use]
pub const fn sticky_fence_min_seq(cur_fence: u64, failed_seq: u64) -> u64 {
    if cur_fence < failed_seq {
        cur_fence
    } else {
        failed_seq
    }
}

/// `sticky_fence_seq_allowed` as `sticky_fence_island.rs` defines it in Clean:
/// `if fence_seq < req_seq then 0 else 1`.
#[must_use]
pub const fn sticky_fence_seq_allowed(fence_seq: u64, req_seq: u64) -> u64 {
    if fence_seq < req_seq {
        0
    } else {
        1
    }
}

/// `sticky_fence_admits_code_isl` as `sticky_fence_island.rs` defines it in Clean:
/// `if 0 < fenced then sticky_fence_seq_allowed fence_seq req_seq else 1`.
#[cfg(test)]
#[must_use]
pub const fn sticky_fence_admits_code(fenced: u64, fence_seq: u64, req_seq: u64) -> u64 {
    if 0 < fenced {
        sticky_fence_seq_allowed(fence_seq, req_seq)
    } else {
        1
    }
}

/// `last_view_available_advance` as `last_view_island.rs` defines it in Clean:
/// `if cur_avail < vis_head then vis_head else cur_avail`.
#[must_use]
pub const fn last_view_available_advance(cur_avail: u64, vis_head: u64) -> u64 {
    if cur_avail < vis_head {
        vis_head
    } else {
        cur_avail
    }
}

/// `last_view_prune_clamp` as `last_view_island.rs` defines it in Clean:
/// `if steps < max_work then steps else max_work`.
#[must_use]
pub const fn last_view_prune_clamp(steps: u64, max_work: u64) -> u64 {
    if steps < max_work {
        steps
    } else {
        max_work
    }
}

/// `last_view_not_before_avail` as `last_view_island.rs` defines it in Clean:
/// `if req_vis < avail then 0 else 1`.
#[must_use]
pub const fn last_view_not_before_avail(avail: u64, req_vis: u64) -> u64 {
    if req_vis < avail {
        0
    } else {
        1
    }
}

/// `last_view_not_above_pub` as `last_view_island.rs` defines it in Clean:
/// `if pub_head < req_vis then 0 else 1`.
#[must_use]
pub const fn last_view_not_above_pub(pub_head: u64, req_vis: u64) -> u64 {
    if pub_head < req_vis {
        0
    } else {
        1
    }
}

/// `last_view_window_admits_code_isl` as `last_view_island.rs` defines it in Clean:
/// `if 0 < last_view_not_before_avail avail req_vis then last_view_not_above_pub pub_head req_vis else 0`.
#[cfg(test)]
#[must_use]
pub const fn last_view_window_admits_code(avail: u64, pub_head: u64, req_vis: u64) -> u64 {
    if 0 < last_view_not_before_avail(avail, req_vis) {
        last_view_not_above_pub(pub_head, req_vis)
    } else {
        0
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
            answers(|[a, b]| crate::proto::group_commit_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::group_commit_monotone(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::proto::high_water_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::high_water_monotone(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::proto::compact_floor_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::compact_floor_monotone(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::proto::epoch_advance_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::epoch_advance_monotone(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::proto::replica_ack_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::replica_ack_monotone(a, b)), want);
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::proto::committed_watermark(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::committed_watermark(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::proto::credit_horizon_monotone(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::credit_horizon_monotone(a, b)), want);
        let want =
            "012012012000111222000111222012012012012012012000111222012012012012012012012012012";
        assert_eq!(
            answers(|[a, b, c, d]| crate::proto::fenced_ack_select(a, b, c, d)),
            want
        );
        assert_eq!(
            answers(|[a, b, c, d]| super::fenced_ack_select(a, b, c, d)),
            want
        );
        let want =
            "012012012000111222000111222012012012012012012000111222012012012012012012012012012";
        assert_eq!(
            answers(|[a, b, c, d]| crate::proto::window_gate_send(a, b, c, d)),
            want
        );
        assert_eq!(
            answers(|[a, b, c, d]| super::window_gate_send(a, b, c, d)),
            want
        );
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::brecord_clamp_body_len(a, b)), want);
        assert_eq!(answers(|[a, b]| super::brecord_clamp_body_len(a, b)), want);
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::logid_generation_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::logid_generation_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| crate::recover_unit_start_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::recover_unit_start_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| crate::storage_len_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::storage_len_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::store_head_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::store_head_advance(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::client_walk_page_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::client_walk_page_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| crate::broker_bt_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::broker_bt_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::at_rest_version_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::at_rest_version_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::tail_wake_head_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::tail_wake_head_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::rate_clock_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::rate_clock_advance(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::federation_cursor_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::federation_cursor_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| crate::failover_epoch_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| super::failover_epoch_advance(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::relay_floor::relay_floor_raise(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::relay_floor_raise(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::refill_join_cursor_max(a, b)), want);
        assert_eq!(answers(|[a, b]| super::refill_join_cursor_max(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::last_view_available_advance(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::last_view_available_advance(a, b)),
            want
        );
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::sharded_clamp_index(a, b)), want);
        assert_eq!(answers(|[a, b]| super::sharded_clamp_index(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::broker_batch_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::broker_batch_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::tail_skip_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::tail_skip_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::rate_tokens_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::rate_tokens_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::federation_seq_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::federation_seq_clamp(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::federation::federation_commit_bound(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::federation_commit_bound(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::failover_quorum_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::failover_quorum_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::refill_debt_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::refill_debt_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::sticky_fence_min_seq(a, b)), want);
        assert_eq!(answers(|[a, b]| super::sticky_fence_min_seq(a, b)), want);
        let want = "011001000";
        assert_eq!(
            answers(|[a, b]| crate::relay_floor::relay_floor_admits(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::relay_floor_admits(a, b)), want);
        let want = "100110111";
        assert_eq!(
            answers(|[a, b]| crate::sticky_fence_seq_allowed(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::sticky_fence_seq_allowed(a, b)),
            want
        );
        let want = "111111111100110111100110111";
        assert_eq!(
            answers(|[a, b, c]| crate::sticky_fence_admits_code(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::sticky_fence_admits_code(a, b, c)),
            want
        );
        let want = "000011012";
        assert_eq!(answers(|[a, b]| crate::last_view_prune_clamp(a, b)), want);
        assert_eq!(answers(|[a, b]| super::last_view_prune_clamp(a, b)), want);
        let want = "100110111";
        assert_eq!(answers(|[a, b]| crate::last_view_not_above_pub(a, b)), want);
        assert_eq!(answers(|[a, b]| super::last_view_not_above_pub(a, b)), want);
        let want = "111011001";
        assert_eq!(
            answers(|[a, b]| crate::last_view_not_before_avail(a, b)),
            want
        );
        assert_eq!(
            answers(|[a, b]| super::last_view_not_before_avail(a, b)),
            want
        );
        let want = "100110111000010011000000001";
        assert_eq!(
            answers(|[a, b, c]| crate::last_view_window_admits_code(a, b, c)),
            want
        );
        assert_eq!(
            answers(|[a, b, c]| super::last_view_window_admits_code(a, b, c)),
            want
        );
    }

    // Not vacuous: `group_commit_monotone` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { a } else { b }), "012112222");
    }
}
