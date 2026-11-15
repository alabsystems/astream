// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic SplitMix64 virtual packet delivery scheduler for `aterm`'s deterministic fabric
//! simulation (`Astream.SimFabric.TlaPrngNetworkSchedule`).
#![allow(
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default
)]

#[cfg(clean_islands)]
#[path = "prng_network_schedule_island.rs"]
mod prng_network_schedule_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_queue_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_tick_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use prng_network_schedule_island::{sim_queue_clamp, sim_tick_advance};

/// Maximum in-flight simulated packets buffered at once.
pub const MAX_SIM_INFLIGHT_PACKETS: u64 = 4_096;

contract_fn! {
    /// Verified monotone delivery timestamp (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sim_clock_ordered_isl`.
    #[must_use]
    pub const fn sim_clock_ordered(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduledPacket {
    pub deliver_at_ms: u64,
    pub tie_seq: u64,
    pub src_node: u32,
    pub dst_node: u32,
    pub payload: Vec<u8>,
}

/// Deterministic SplitMix64 jittered packet queue delivering in `(deliver_at_ms, tie_seq)` order.
#[derive(Debug, Clone)]
pub struct DeterministicNetSchedule {
    state: u64,
    now_ms: u64,
    next_seq: u64,
    max_jitter_ms: u64,
    queue: Vec<ScheduledPacket>,
}

impl DeterministicNetSchedule {
    #[must_use]
    pub const fn new(seed: u64, max_jitter_ms: u64) -> Self {
        Self {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
            now_ms: 0,
            next_seq: 0,
            max_jitter_ms,
            queue: Vec::new(),
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn enqueue(&mut self, src: u32, dst: u32, base_delay_ms: u64, payload: Vec<u8>) -> bool {
        let cap = sim_queue_clamp(MAX_SIM_INFLIGHT_PACKETS, MAX_SIM_INFLIGHT_PACKETS) as usize;
        if self.queue.len() >= cap {
            return false;
        }
        let jitter = if self.max_jitter_ms == 0 {
            0
        } else {
            let modulus = (self.max_jitter_ms & 0xFFFF).saturating_add(1);
            match self.next_u64().checked_rem(modulus) {
                Some(r) => r,
                None => 0,
            }
        };
        let deliver_at = self
            .now_ms
            .saturating_add(base_delay_ms)
            .saturating_add(jitter);
        self.next_seq = self.next_seq.saturating_add(1);
        self.queue.push(ScheduledPacket {
            deliver_at_ms: deliver_at,
            tie_seq: self.next_seq,
            src_node: src,
            dst_node: dst,
            payload,
        });
        true
    }

    pub fn pop_next(&mut self) -> Option<ScheduledPacket> {
        let mut best: Option<ScheduledPacket> = None;
        for pkt in core::mem::take(&mut self.queue) {
            match core::mem::take(&mut best) {
                None => best = Some(pkt),
                Some(cur) => {
                    if (pkt.deliver_at_ms, pkt.tie_seq) < (cur.deliver_at_ms, cur.tie_seq) {
                        self.queue.push(cur);
                        best = Some(pkt);
                    } else {
                        self.queue.push(pkt);
                        best = Some(cur);
                    }
                }
            }
        }
        let Some(pkt) = best else {
            return None;
        };
        let next_clock = sim_tick_advance(self.now_ms, pkt.deliver_at_ms);
        let _ = sim_clock_ordered(next_clock, self.now_ms);
        self.now_ms = next_clock;
        Some(pkt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_schedule_replays_identical_packet_order_from_same_seed() {
        let run = |seed: u64| {
            let mut s = DeterministicNetSchedule::new(seed, 25);
            s.enqueue(1, 2, 10, b"a".to_vec());
            s.enqueue(1, 3, 5, b"b".to_vec());
            s.enqueue(2, 1, 8, b"c".to_vec());
            vec![
                s.pop_next().unwrap(),
                s.pop_next().unwrap(),
                s.pop_next().unwrap(),
            ]
        };
        assert_eq!(run(0xCAFE_BABE), run(0xCAFE_BABE));
    }
}
