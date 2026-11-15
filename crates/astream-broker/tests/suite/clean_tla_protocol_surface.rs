//! End-to-end verification of the Clean-Origin (`I5`) protocol transition kernels
//! and `#[ensures]` `clean-kernel-defeq` guards across `astream-wire`, `astream-cap`,
//! and `astream-broker`.

use astream_broker::proto::{
    can_send_in_window, committed_watermark, compact_floor_monotone, credit_horizon_monotone,
    epoch_advance_monotone, epoch_is_fenced, fenced_replica_watermark, group_commit_monotone,
    high_water_monotone, offset_is_committed, replica_ack_monotone, will_is_fenced,
    windowed_send_advance,
};
use astream_broker::{BrokerLog, BrokerRecord, CreditWindow};
use astream_wire::cut::{
    causal_step_frontier, frontier_includes, heal_frontier_monotone, meet_frontier_monotone,
    CausalCut,
};
use astream_wire::receipt::{deadline_elapsed, monotone_clock_tick, FabricReceipt, ReceiptVerdict};
use astream_wire::Offset;

/// Operands at the boundaries the hand-written kernels below turn on: zero and one, the
/// 63/64 edge of a SHA-256 block, and the top of the range.
const GRID: [u64; 9] = [0, 1, 2, 62, 63, 64, 65, u64::MAX - 1, u64::MAX];

// `causal_step_frontier` is hand-written Rust, not compiled from Clean: it answers as
// `causal_step_frontier_isl`, the island's composition of the Clean-Origin functions it
// restates, on every grid tuple.
#[test]
fn causal_step_frontier_answers_as_its_island_composition() {
    use astream_wire::cut::causal_gate_frontier;

    let mut gated = false;
    for cut in GRID {
        for req in GRID {
            for cur in GRID {
                for cand in GRID {
                    let island =
                        causal_gate_frontier(req, cut, heal_frontier_monotone(cur, cand), cur);
                    assert_eq!(
                        causal_step_frontier(cut, req, cur, cand),
                        island,
                        "causal_step_frontier({cut}, {req}, {cur}, {cand})"
                    );
                    gated |= island != heal_frontier_monotone(cur, cand);
                }
            }
        }
    }
    // Not vacuous: the grid reaches a cause the cut does not include, where the gate
    // keeps the effect frontier short of the healed one.
    assert!(gated);
}

// `sha256_next_buf_len` is hand-written Rust (masks where the island subtracts): it answers
// as `sha256_next_buf_len_isl`, the island's composition of `sha256_clamp_partial_len` and
// `sha256_partial_take`, on every grid tuple.
#[test]
fn sha256_next_buf_len_answers_as_its_island_composition() {
    use astream_digest::{sha256_clamp_partial_len, sha256_next_buf_len, sha256_partial_take};

    let mut filled_sides = [false; 2];
    for cur in GRID {
        for data in GRID {
            for tail in GRID {
                let island = if cur == 0 {
                    sha256_clamp_partial_len(tail, 63)
                } else {
                    let clamped_cur = sha256_clamp_partial_len(cur, 63);
                    let take = sha256_partial_take(64 - clamped_cur, data);
                    let partial = clamped_cur + take < 64;
                    filled_sides[usize::from(partial)] = true;
                    if partial {
                        clamped_cur + take
                    } else {
                        sha256_clamp_partial_len(tail, 63)
                    }
                };
                assert_eq!(
                    sha256_next_buf_len(cur, data, tail),
                    island,
                    "sha256_next_buf_len({cur}, {data}, {tail})"
                );
            }
        }
    }
    // Not vacuous: the grid both leaves a partial block and completes one.
    assert_eq!(filled_sides, [true, true]);
}

// `attenuate_bounded_expiry` is hand-written Rust: it answers as
// `attenuate_bounded_expiry_isl`, the island's composition of `attenuate_expiry_min` and
// `live_expiry_or_zero`, on every grid tuple.
#[cfg(feature = "cap")]
#[test]
fn attenuate_bounded_expiry_answers_as_its_island_composition() {
    use astream_cap::{attenuate_bounded_expiry, attenuate_expiry_min, live_expiry_or_zero};

    let mut lapsed = false;
    for now in GRID {
        for parent in GRID {
            for child in GRID {
                let tightest = attenuate_expiry_min(parent, child);
                let island = live_expiry_or_zero(tightest, now, 0);
                assert_eq!(
                    attenuate_bounded_expiry(now, parent, child),
                    island,
                    "attenuate_bounded_expiry({now}, {parent}, {child})"
                );
                lapsed |= island != tightest;
            }
        }
    }
    // Not vacuous: the grid reaches a nonzero expiry the clock has passed.
    assert!(lapsed);
}

#[test]
fn clean_origin_causal_cut_and_receipt_kernels_enforce_tla_invariants() {
    // 1. 4-parameter Chandy-Lamport causal_step_frontier kernel:
    // If cause_req (10) > cause_cut (7), the effect frontier stays at eff_cur (3).
    assert_eq!(causal_step_frontier(7, 10, 3, 9), 3);
    // Once cause_cut advances to 10 (cause_req <= cause_cut), eff_cur advances to max(3, 9) = 9.
    let healed_cause = heal_frontier_monotone(7, 10);
    assert_eq!(healed_cause, 10);
    assert!(frontier_includes(healed_cause, 10));
    assert_eq!(causal_step_frontier(healed_cause, 10, 3, 9), 9);
    // Pointwise meet is greatest lower bound:
    assert_eq!(meet_frontier_monotone(9, 5), 5);

    let mut cut: CausalCut<&str> = CausalCut::new();
    cut.advance("a", Offset(7));
    assert!(!cut.advance_effect_if_causal("b", Offset(9), Some((&"a", Offset(10)))));
    assert_eq!(cut.offset_of(&"b"), None);
    assert!(cut.advance_and_heal_edge("b", Offset(9), Some(("a", Offset(10)))));
    assert_eq!(cut.offset_of(&"a"), Some(Offset(10)));
    assert_eq!(cut.offset_of(&"b"), Some(Offset(9)));

    // 2. Monotone fabric receipt clock & deadline guard:
    let t1 = monotone_clock_tick(1_000, 950);
    assert_eq!(t1, 1_000);
    let t2 = monotone_clock_tick(t1, 1_050);
    assert_eq!(t2, 1_050);
    assert!(!deadline_elapsed(1_100, t2));
    assert!(deadline_elapsed(1_050, t2));
    assert!(FabricReceipt::new_expired(Offset(4), 1_100, t2).is_err());
    let exp = FabricReceipt::new_expired(Offset(4), 1_050, t2).expect("deadline elapsed at 1050");
    assert_eq!(exp.bt_ms(), 1_050);
    assert_eq!(FabricReceipt::tick_clock(1_050, 1_020), 1_050);
    let ack = FabricReceipt::Ack {
        re: Offset(4),
        verdict: ReceiptVerdict::Handled,
        bt_ms: FabricReceipt::tick_clock(1_050, 1_020),
    };
    assert_eq!(ack.bt_ms(), 1_050);
}

#[test]
fn clean_origin_broker_replication_and_credit_window_kernels_enforce_tla_invariants() {
    // 1. 4-parameter Clean-origin `fenced_ack_select` + 5-parameter `fenced_replica_watermark`:
    assert_eq!(astream_broker::proto::fenced_ack_select(2, 3, 8, 15), 8);
    assert_eq!(astream_broker::proto::fenced_ack_select(3, 3, 8, 15), 15);
    // Stale follower ack (req_epoch=2 < leader_epoch=3) is fenced: watermark stays min(head=20, cur_ack=8) = 8.
    assert!(epoch_is_fenced(3, 2));
    assert_eq!(fenced_replica_watermark(3, 2, 20, 8, 15), 8);
    // Current-epoch follower ack (req_epoch=3 >= leader_epoch=3) advances cur_ack to 15, watermark = min(20, 15) = 15.
    assert!(!epoch_is_fenced(3, 3));
    assert_eq!(fenced_replica_watermark(3, 3, 20, 8, 15), 15);
    // Follower ack exceeding primary_head (cand_ack=25 > head=20) is clamped to primary_head=20.
    assert_eq!(fenced_replica_watermark(3, 3, 20, 15, 25), 20);

    // Verify through real BrokerLog:
    let dir = std::env::temp_dir().join(format!(
        "astream-clean-tla-surface-{}-{}",
        std::process::id(),
        1
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let log_path = dir.join("broker.log");
    let mut log = BrokerLog::open(&log_path).unwrap();
    for i in 0..5u64 {
        log.publish(1, i + 1, "/f/test/msg".to_string(), vec![b'x'; 8])
            .unwrap();
    }
    assert_eq!(log.head(), Offset(5));
    assert_eq!(log.advance_replication_epoch(4).unwrap(), 4);
    assert!(log.advance_replication_epoch(3).is_err());
    // Stale-epoch follower ack (epoch 3 < 4) does not advance watermark:
    assert_eq!(log.record_fenced_replica_ack(3, Offset(4)), Offset(0));
    // Valid-epoch follower ack (epoch 4) advances watermark to min(5, 4) = 4:
    assert_eq!(log.record_fenced_replica_ack(4, Offset(4)), Offset(4));
    assert!(log.is_offset_replicated_committed(Offset(3)));
    assert!(!log.is_offset_replicated_committed(Offset(4)));
    assert!(offset_is_committed(4, 3));
    assert!(!offset_is_committed(4, 4));
    let _ = std::fs::remove_dir_all(&dir);

    // 2. 4-parameter Clean-origin `window_gate_send` + `windowed_send_advance`:
    assert_eq!(astream_broker::proto::window_gate_send(2, 4, 4, 2), 4);
    assert_eq!(astream_broker::proto::window_gate_send(4, 4, 6, 4), 4);
    // With sent=2, ack=1, horizon=4, cand=5 -> clamped to horizon=4:
    assert_eq!(windowed_send_advance(2, 1, 4, 5), 4);
    // When sent == horizon (4 == 4), no further send is allowed:
    assert_eq!(windowed_send_advance(4, 1, 4, 6), 4);

    let mut win = CreditWindow::new(3);
    assert!(can_send_in_window(win.credit_horizon(), win.next_send()));
    assert!(win.try_send());
    assert_eq!(win.next_send(), 1);
    assert_eq!(win.advance_send_to(10), 3);
    assert!(!win.try_send());
    assert_eq!(win.record_ack(2), 2);
    assert_eq!(win.grant_window(3), 5);
    assert!(win.try_send());
    assert_eq!(win.next_send(), 4);

    // 3. Monotone group commit, high-water, compaction floor, and will fencing:
    assert_eq!(group_commit_monotone(10, 7), 10);
    assert_eq!(group_commit_monotone(10, 12), 12);
    assert_eq!(high_water_monotone(5, 9), 9);
    assert_eq!(compact_floor_monotone(8, 3), 8);
    assert_eq!(epoch_advance_monotone(4, 6), 6);
    assert_eq!(replica_ack_monotone(4, 9), 9);
    assert_eq!(committed_watermark(10, 7), 7);
    assert_eq!(credit_horizon_monotone(8, 16), 16);
    assert_eq!(
        astream_broker::broker_bt_advance(1_700_000_001_000, 1_700_000_000_500),
        1_700_000_001_000
    );
    assert_eq!(
        astream_broker::broker_bt_advance(1_700_000_001_000, 1_700_000_002_000),
        1_700_000_002_000
    );
    assert!(will_is_fenced(10, 9));
    assert!(!will_is_fenced(10, 10));
    let _ = BrokerRecord {
        seq: Offset(0),
        producer_id: 1,
        producer_seq: 1,
        subject: "/f/test".to_string(),
        body: Vec::new(),
        commit: None,
    };
}

#[cfg(feature = "cap")]
#[test]
fn clean_origin_capability_attenuation_and_clock_kernels_enforce_tla_invariants() {
    use astream_cap::{
        advance_auth_clock_ms, attenuate_bounded_expiry, attenuate_expiry_min, attenuate_offline,
        effective_bounded_expiry_ms, effective_expiry_ms, expiry_attenuates, grant_expired_at,
        live_expiry_or_zero, macaroon_depth_valid, mint, producer_id_matches,
    };

    assert_eq!(advance_auth_clock_ms(5_000, 4_800), 5_000);
    assert_eq!(advance_auth_clock_ms(5_000, 5_200), 5_200);
    assert_eq!(attenuate_expiry_min(2_000, 1_500), 1_500);
    assert_eq!(live_expiry_or_zero(1_500, 1_000, 0), 1_500);
    assert_eq!(live_expiry_or_zero(1_500, 1_500, 0), 0);
    // 3-parameter attenuate_bounded_expiry:
    // Both > now_ms (1_000) -> min(2_000, 1_500) = 1_500:
    assert_eq!(attenuate_bounded_expiry(1_000, 2_000, 1_500), 1_500);
    // Parent or child expired at now_ms (1_600 >= 1_500) -> collapses to 0:
    assert_eq!(attenuate_bounded_expiry(1_600, 2_000, 1_500), 0);
    assert!(grant_expired_at(1_500, 1_500));
    assert!(!grant_expired_at(1_500, 1_499));
    assert!(producer_id_matches(42, 42));
    assert!(expiry_attenuates(1_500, 2_000));
    assert!(macaroon_depth_valid(3, 8));

    let secret = b"0123456789abcdef0123456789abcdef";
    let root = mint(secret, "/f/local/>").unwrap();
    let c1 = attenuate_offline(
        &root,
        "rw,p=n-0123456789abcdef,exp=2000:/f/local/pub/>",
        500,
    )
    .unwrap();
    let c2 = attenuate_offline(
        &c1,
        "ro,p=n-0123456789abcdef,exp=1500:/f/local/pub/n-0123456789abcdef/>",
        500,
    )
    .unwrap();
    assert_eq!(effective_expiry_ms(&c2.filter), Some(1_500));
    assert_eq!(effective_bounded_expiry_ms(&c2.filter, 1_000), Some(1_500));
    assert_eq!(effective_bounded_expiry_ms(&c2.filter, 1_500), Some(0));
}

#[test]
fn clean_origin_streaming_sha256_kernels_enforce_tla_invariants() {
    use astream_digest::{
        buf_len_is_partial, sha256_clamp_partial_len, sha256_next_buf_len, sha256_partial_take,
        BLOCK_LEN,
    };

    assert!(buf_len_is_partial(0, BLOCK_LEN as u64));
    assert!(buf_len_is_partial(63, BLOCK_LEN as u64));
    assert!(!buf_len_is_partial(64, BLOCK_LEN as u64));
    assert_eq!(sha256_partial_take(44, 15), 15);
    assert_eq!(sha256_partial_take(44, 100), 44);
    assert_eq!(sha256_clamp_partial_len(12, 63), 12);
    assert_eq!(sha256_clamp_partial_len(99, 63), 63);
    assert_eq!(sha256_next_buf_len(0, 100, 36), 36);
    assert_eq!(sha256_next_buf_len(20, 15, 0), 35);
    assert_eq!(sha256_next_buf_len(20, 100, 12), 12);
}

#[test]
fn clean_origin_wire_frame_steps_hash_offset_partition_subject_kernels_enforce_tla_invariants() {
    use astream_wire::{
        crc32_ieee, crc32_ieee_update, crc32_is_ieee_poly, crc32_poly_select,
        crc_table_index_clamp, crc_table_index_in_bounds, filter_depth_contains, fnv1a_64,
        fnv1a_64_is_init, fnv1a_64_is_prime, fnv1a_64_mix_u64, fnv1a_64_mul_prime,
        fnv1a_64_state_matches, fnv1a_64_update, fnv1a_64_xor, frame_clamp_payload_len,
        offset_advance_monotone, offset_precedes_or_eq, partition_in_bounds,
        partition_modulus_clamp, payload_within_cap, segment_depth_advance, step_prefix_advance,
        step_within_bounds, sync_clamp_parent_count, sync_within_capacity, CRC32_IEEE_POLY,
        FNV1A_64_INIT, FNV1A_64_PRIME, MAX_PAYLOAD_LEN,
    };

    assert_eq!(
        frame_clamp_payload_len(MAX_PAYLOAD_LEN as u64 + 99, MAX_PAYLOAD_LEN as u64),
        MAX_PAYLOAD_LEN as u64
    );
    assert!(payload_within_cap(
        MAX_PAYLOAD_LEN as u64,
        MAX_PAYLOAD_LEN as u64
    ));
    assert!(!payload_within_cap(
        MAX_PAYLOAD_LEN as u64 + 1,
        MAX_PAYLOAD_LEN as u64
    ));

    assert_eq!(step_prefix_advance(32, 64), 64);
    assert!(step_within_bounds(64, 128));
    assert!(!step_within_bounds(129, 128));

    assert_eq!(crc_table_index_clamp(300, 255), 255);
    assert!(crc_table_index_in_bounds(255, 255));
    assert!(!crc_table_index_in_bounds(256, 255));
    assert_eq!(crc32_poly_select(0, CRC32_IEEE_POLY), 0);
    assert_eq!(crc32_poly_select(1, CRC32_IEEE_POLY), CRC32_IEEE_POLY);
    assert!(crc32_is_ieee_poly(CRC32_IEEE_POLY));
    assert!(!crc32_is_ieee_poly(0));
    assert!(fnv1a_64_is_init(FNV1A_64_INIT));
    assert!(!fnv1a_64_is_init(0));
    assert!(fnv1a_64_is_prime(FNV1A_64_PRIME));
    assert!(!fnv1a_64_is_prime(0));
    assert!(fnv1a_64_state_matches(FNV1A_64_INIT, FNV1A_64_INIT));
    assert!(!fnv1a_64_state_matches(0, FNV1A_64_INIT));
    assert_eq!(fnv1a_64_xor(FNV1A_64_INIT, 42), FNV1A_64_INIT ^ 42);
    assert_eq!(fnv1a_64_mul_prime(1, FNV1A_64_PRIME), FNV1A_64_PRIME);
    for h in GRID {
        for word in GRID {
            assert_eq!(
                fnv1a_64_mix_u64(h, word),
                (h ^ word).wrapping_mul(FNV1A_64_PRIME),
                "fnv1a_64_mix_u64({h}, {word})"
            );
            assert_eq!(
                fnv1a_64_mix_u64(h, word),
                fnv1a_64_mul_prime(fnv1a_64_xor(h, word), FNV1A_64_PRIME)
            );
        }
    }
    assert_eq!(
        fnv1a_64_mix_u64(FNV1A_64_INIT, 42),
        (FNV1A_64_INIT ^ 42).wrapping_mul(FNV1A_64_PRIME)
    );
    assert_eq!(
        crc32_ieee_update(crc32_ieee(b"1234"), b"56789"),
        crc32_ieee(b"123456789")
    );
    assert_eq!(
        fnv1a_64_update(fnv1a_64(b"1234"), b"56789"),
        fnv1a_64(b"123456789")
    );

    assert_eq!(offset_advance_monotone(10, 25), 25);
    assert!(offset_precedes_or_eq(10, 25));
    assert!(!offset_precedes_or_eq(25, 10));

    assert_eq!(partition_modulus_clamp(0, 1), 1);
    assert_eq!(partition_modulus_clamp(16, 1), 16);
    assert!(partition_in_bounds(15, 16));
    assert!(!partition_in_bounds(16, 16));

    assert_eq!(segment_depth_advance(3, 5), 5);
    assert!(filter_depth_contains(3, 5));
    assert!(!filter_depth_contains(5, 3));

    assert_eq!(sync_clamp_parent_count(3, 8), 3);
    assert_eq!(sync_clamp_parent_count(12, 8), 8);
    assert!(sync_within_capacity(7, 8));
    assert!(!sync_within_capacity(8, 8));

    assert_eq!(astream_broker::at_rest_version_advance(2, 1), 2);
    assert_eq!(astream_broker::at_rest_version_advance(1, 2), 2);
    assert!(astream_broker::at_rest_version_is_bound(2, 2));
    assert!(!astream_broker::at_rest_version_is_bound(1, 2));

    assert_eq!(astream_broker::tail_wake_head_advance(10, 4), 10);
    assert_eq!(astream_broker::tail_wake_head_advance(10, 18), 18);
    assert_eq!(astream_broker::tail_skip_clamp(12, 20), 12);
    assert_eq!(astream_broker::tail_skip_clamp(25, 20), 20);
    assert!(astream_broker::tail_wake_is_caught_up(10, 10));
    assert!(astream_broker::tail_wake_is_caught_up(10, 12));
    assert!(!astream_broker::tail_wake_is_caught_up(12, 10));

    assert_eq!(astream_broker::rate_tokens_clamp(250, 100), 100);
    assert_eq!(astream_broker::rate_tokens_clamp(80, 100), 80);
    assert_eq!(astream_broker::rate_clock_advance(1_000, 950), 1_000);
    assert_eq!(astream_broker::rate_clock_advance(1_000, 1_050), 1_050);
    assert!(astream_broker::rate_tokens_sufficient(1_000, 1_000));
    assert!(!astream_broker::rate_tokens_sufficient(999, 1_000));

    assert_eq!(astream_broker::federation_cursor_advance(10, 4), 10);
    assert_eq!(astream_broker::federation_cursor_advance(10, 19), 19);
    assert_eq!(astream_broker::federation_seq_clamp(42, 100), 42);
    assert_eq!(astream_broker::federation_seq_clamp(500, 100), 100);
    assert!(astream_broker::federation_hop_allowed(0, 1));
    assert!(!astream_broker::federation_hop_allowed(1, 1));
    assert!(astream_broker::federation_route_preferred(10_000, 10_000));
    assert!(!astream_broker::federation_route_preferred(10_000, 10_001));
    assert!(astream_broker::federation_incarnation_fresh(2, 2));
    assert!(!astream_broker::federation_incarnation_fresh(1, 2));

    assert_eq!(astream_broker::failover_epoch_advance(3, 7), 7);
    assert_eq!(astream_broker::failover_quorum_clamp(5, 3), 3);
    assert!(astream_broker::failover_fences_stale(2, 3));
    assert!(astream_broker::failover_lease_expired(2_950, 2_950));
    assert!(!astream_broker::failover_lease_expired(2_949, 2_950));

    assert_eq!(astream_broker::refill_join_cursor_max(5, 12), 12);
    assert_eq!(astream_broker::refill_debt_clamp(80, 50), 50);
    assert!(astream_broker::refill_cursor_at_least_oldest(12, 12));

    assert_eq!(astream_broker::sticky_fence_min_seq(10, 6), 6);
    assert_eq!(astream_broker::sticky_fence_seq_allowed(6, 7), 0);
    assert_eq!(astream_broker::sticky_fence_seq_allowed(6, 6), 1);
    assert_eq!(astream_broker::sticky_fence_admits_code(0, 6, 7), 1);
    assert_eq!(astream_broker::sticky_fence_admits_code(1, 6, 7), 0);
    assert_eq!(astream_broker::sticky_fence_admits_code(1, 6, 6), 1);
    assert!(astream_broker::sticky_fence_table_within_cap(64, 4096));

    assert_eq!(astream_broker::last_view_available_advance(4, 9), 9);
    assert_eq!(astream_broker::last_view_available_advance(9, 4), 9);
    assert_eq!(astream_broker::last_view_prune_clamp(80, 64), 64);
    assert_eq!(astream_broker::last_view_prune_clamp(32, 64), 32);
    assert_eq!(astream_broker::last_view_not_before_avail(5, 4), 0);
    assert_eq!(astream_broker::last_view_not_before_avail(5, 5), 1);
    assert_eq!(astream_broker::last_view_not_above_pub(10, 11), 0);
    assert_eq!(astream_broker::last_view_not_above_pub(10, 10), 1);
    assert_eq!(astream_broker::last_view_window_admits_code(5, 10, 4), 0);
    assert_eq!(astream_broker::last_view_window_admits_code(5, 10, 7), 1);
    assert_eq!(astream_broker::last_view_window_admits_code(5, 10, 11), 0);
    assert!(astream_broker::last_view_prune_within_quantum(64, 64));
    assert!(!astream_broker::last_view_prune_within_quantum(65, 64));

    assert_eq!(astream_cap::ceiling_rule_index_clamp(10, 8), 8);
    assert_eq!(astream_cap::ceiling_mode_subsumes_code(0, 0), 1);
    assert_eq!(astream_cap::ceiling_mode_subsumes_code(1, 0), 1);
    assert_eq!(astream_cap::ceiling_mode_subsumes_code(0, 1), 0);
    assert_eq!(astream_cap::ceiling_mode_subsumes_code(1, 1), 1);
    assert!(astream_cap::ceiling_rule_within_cap(8, 64));

    assert_eq!(astream_agent::foreign_tape_cursor_advance(3, 9), 9);
    assert_eq!(astream_agent::foreign_tape_clamp_records(120, 64), 64);
    assert!(astream_agent::foreign_tape_exhausted(9, 9));
}
