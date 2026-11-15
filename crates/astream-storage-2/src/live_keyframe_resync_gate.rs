// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Live terminal delta-chain vs full-keyframe resync gate
//! (`Astream.Live.TlaLiveKeyframeResyncGate`).
//!
//! Ensures late-joining or WAN-reconnecting `aterm` viewers never replay an
//! unbounded chain of terminal diff frames: forces a full keyframe snapshot
//! whenever cumulative delta bytes reach `max_delta_bytes`, delta chain length
//! reaches `max_delta_chain`, or a viewer explicitly requests resync.

#[cfg(clean_islands)]
#[path = "live_keyframe_resync_gate_island.rs"]
mod live_keyframe_resync_gate_island;
#[cfg(clean_islands)]
pub use live_keyframe_resync_gate_island::{delta_chain_clamp, keyframe_gen_advance};

#[cfg(not(clean_islands))]
/// Monotonically advance emitted keyframe generation counter.
#[must_use]
pub const fn keyframe_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Clamp accumulated delta chain length below or at `max_chain`.
#[must_use]
pub const fn delta_chain_clamp(cand_chain: u64, max_chain: u64) -> u64 {
    if cand_chain < max_chain {
        cand_chain
    } else {
        max_chain
    }
}

contract_fn! {
    /// True iff a full keyframe must be emitted instead of appending another delta.
    #[must_use]
    pub const fn needs_keyframe(next_chain: u64,
        max_chain: u64,
        next_bytes: u64,
        max_bytes: u64,) -> bool
    clauses [ensures result == (max_chain <= next_chain || max_bytes <= next_bytes)]
    {
        max_chain <= next_chain || max_bytes <= next_bytes
    }
}

/// Decision emitted for each outbound live terminal frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveFramePlan {
    EmitKeyframe { keyframe_gen: u64 },
    EmitDelta { keyframe_gen: u64, chain_index: u64 },
}

/// Bounded delta-vs-keyframe scheduler for live `aterm` session multicast.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveKeyframeResyncGate {
    max_delta_chain: u64,
    max_delta_bytes: u64,
    cur_chain_len: u64,
    cur_delta_bytes: u64,
    keyframe_gen: u64,
    resync_requested: bool,
}

impl LiveKeyframeResyncGate {
    #[must_use]
    pub const fn new(max_delta_chain: u64, max_delta_bytes: u64) -> Self {
        let chain_cap = if max_delta_chain == 0 {
            1
        } else {
            max_delta_chain
        };
        let byte_cap = if max_delta_bytes == 0 {
            1024
        } else {
            max_delta_bytes
        };
        Self {
            max_delta_chain: chain_cap,
            max_delta_bytes: byte_cap,
            cur_chain_len: 0,
            cur_delta_bytes: 0,
            keyframe_gen: 0,
            resync_requested: true,
        }
    }

    #[must_use]
    pub const fn keyframe_gen(&self) -> u64 {
        self.keyframe_gen
    }

    #[must_use]
    pub const fn cur_chain_len(&self) -> u64 {
        self.cur_chain_len
    }

    #[must_use]
    pub const fn cur_delta_bytes(&self) -> u64 {
        self.cur_delta_bytes
    }

    /// Mark that a late-joining viewer or gap-detected subscriber requested a keyframe.
    pub fn request_resync(&mut self) {
        self.resync_requested = true;
    }

    /// Decide whether to emit a full keyframe or an incremental delta of `candidate_delta_bytes`.
    pub fn plan_frame(&mut self, candidate_delta_bytes: u64) -> LiveFramePlan {
        let next_chain = self.cur_chain_len.saturating_add(1);
        let next_bytes = self.cur_delta_bytes.saturating_add(candidate_delta_bytes);
        if self.resync_requested
            || self.keyframe_gen == 0
            || needs_keyframe(
                next_chain,
                self.max_delta_chain,
                next_bytes,
                self.max_delta_bytes,
            )
        {
            let cand_gen = self.keyframe_gen.saturating_add(1);
            self.keyframe_gen = keyframe_gen_advance(self.keyframe_gen, cand_gen);
            self.cur_chain_len = 0;
            self.cur_delta_bytes = 0;
            self.resync_requested = false;
            LiveFramePlan::EmitKeyframe {
                keyframe_gen: self.keyframe_gen,
            }
        } else {
            self.cur_chain_len = delta_chain_clamp(next_chain, self.max_delta_chain);
            self.cur_delta_bytes = next_bytes;
            LiveFramePlan::EmitDelta {
                keyframe_gen: self.keyframe_gen,
                chain_index: self.cur_chain_len,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn forces_initial_periodic_and_byte_budget_keyframes() {
        let mut gate = LiveKeyframeResyncGate::new(3, 1000);
        // Initial frame is always a keyframe:
        assert_eq!(
            gate.plan_frame(120),
            LiveFramePlan::EmitKeyframe { keyframe_gen: 1 }
        );
        // Up to 2 deltas (`next_chain < 3` and `next_bytes < 1000`):
        assert_eq!(
            gate.plan_frame(300),
            LiveFramePlan::EmitDelta {
                keyframe_gen: 1,
                chain_index: 1,
            }
        );
        assert_eq!(
            gate.plan_frame(300),
            LiveFramePlan::EmitDelta {
                keyframe_gen: 1,
                chain_index: 2,
            }
        );
        // 3rd delta hits `max_delta_chain == 3` -> rotates keyframe_gen to 2!
        assert_eq!(
            gate.plan_frame(100),
            LiveFramePlan::EmitKeyframe { keyframe_gen: 2 }
        );
        // Oversized delta (`1200 >= 1000`) immediately forces keyframe 3:
        assert_eq!(
            gate.plan_frame(1200),
            LiveFramePlan::EmitKeyframe { keyframe_gen: 3 }
        );
    }
}
