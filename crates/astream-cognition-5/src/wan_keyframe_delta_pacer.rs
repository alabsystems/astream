// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! High-RTT WAN live-terminal delta vs keyframe bandwidth pacer
//! (`Astream.Live.TlaWanKeyframeDeltaPacer`).
//!
//! Paces `astream-live` screen updates across high-latency WAN links: sends compact row-delta
//! frames while `deltas_since_keyframe < max_delta_run` and `delta_bytes < full_bytes`, forces a
//! self-contained keyframe on reconnect or after `max_delta_run`, and advances `frame_seq`
//! monotonically.

#[cfg(clean_islands)]
#[path = "wan_keyframe_delta_pacer_island.rs"]
mod wan_keyframe_delta_pacer_island;
#[cfg(clean_islands)]
pub use wan_keyframe_delta_pacer_island::{live_delta_run_clamp_b117, live_frame_seq_advance_b117};

#[cfg(not(clean_islands))]
/// Clamp consecutive delta-frame run count to `max_delta_run`.
#[must_use]
pub const fn live_delta_run_clamp_b117(cand_run: u64, max_delta_run: u64) -> u64 {
    if cand_run < max_delta_run {
        cand_run
    } else {
        max_delta_run
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `frame_seq`.
#[must_use]
pub const fn live_frame_seq_advance_b117(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff another delta frame is allowed before a mandatory keyframe refresh.
    #[must_use]
    pub const fn live_can_emit_delta_b117(deltas_since_keyframe: u64, max_delta_run: u64) -> bool
    clauses [ensures result == (deltas_since_keyframe < max_delta_run)]
    {
        deltas_since_keyframe < max_delta_run
    }
}

/// Frame emission kind chosen by `WanKeyframeDeltaPacer`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveFrameSelection {
    EmitKeyframe {
        frame_seq: u64,
        bytes: u64,
    },
    EmitDelta {
        frame_seq: u64,
        bytes: u64,
        deltas_since_keyframe: u64,
    },
    DropNoBandwidthCredit,
}

/// WAN live-screen keyframe vs delta pacer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WanKeyframeDeltaPacer {
    has_keyframe_anchor: bool,
    deltas_since_keyframe: u64,
    max_delta_run: u64,
    credit_bytes: u64,
    max_credit_bytes: u64,
    frame_seq: u64,
}

impl WanKeyframeDeltaPacer {
    #[must_use]
    pub const fn new(max_delta_run: u64, max_credit_bytes: u64) -> Self {
        let dr = if max_delta_run == 0 {
            32
        } else {
            max_delta_run
        };
        let cb = if max_credit_bytes == 0 {
            128 * 1024
        } else {
            max_credit_bytes
        };
        Self {
            has_keyframe_anchor: false,
            deltas_since_keyframe: 0,
            max_delta_run: dr,
            credit_bytes: cb,
            max_credit_bytes: cb,
            frame_seq: 0,
        }
    }

    /// Replenish WAN pacing credit upon receiver ACK.
    pub fn replenish_credit(&mut self, acked_bytes: u64) {
        let proposed = self.credit_bytes.saturating_add(acked_bytes);
        self.credit_bytes = live_delta_run_clamp_b117(proposed, self.max_credit_bytes);
    }

    /// Force next frame to be a full keyframe (e.g., new subscriber join or packet gap).
    pub fn request_keyframe_resync(&mut self) {
        self.has_keyframe_anchor = false;
    }

    /// Choose keyframe vs delta given `keyframe_bytes` and `delta_bytes`.
    pub fn select_frame(&mut self, keyframe_bytes: u64, delta_bytes: u64) -> LiveFrameSelection {
        let can_delta = self.has_keyframe_anchor
            && live_can_emit_delta_b117(self.deltas_since_keyframe, self.max_delta_run)
            && delta_bytes < keyframe_bytes;

        if can_delta {
            if self.credit_bytes < delta_bytes {
                return LiveFrameSelection::DropNoBandwidthCredit;
            }
            self.credit_bytes = self.credit_bytes.saturating_sub(delta_bytes);
            let cand_run = self.deltas_since_keyframe.saturating_add(1);
            self.deltas_since_keyframe = live_delta_run_clamp_b117(cand_run, self.max_delta_run);
            let next_seq = self.frame_seq.saturating_add(1);
            self.frame_seq = live_frame_seq_advance_b117(self.frame_seq, next_seq);
            LiveFrameSelection::EmitDelta {
                frame_seq: self.frame_seq,
                bytes: delta_bytes,
                deltas_since_keyframe: self.deltas_since_keyframe,
            }
        } else {
            if self.credit_bytes < keyframe_bytes {
                return LiveFrameSelection::DropNoBandwidthCredit;
            }
            self.credit_bytes = self.credit_bytes.saturating_sub(keyframe_bytes);
            self.has_keyframe_anchor = true;
            self.deltas_since_keyframe = 0;
            let next_seq = self.frame_seq.saturating_add(1);
            self.frame_seq = live_frame_seq_advance_b117(self.frame_seq, next_seq);
            LiveFrameSelection::EmitKeyframe {
                frame_seq: self.frame_seq,
                bytes: keyframe_bytes,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emits_initial_keyframe_then_deltas_up_to_run_limit() {
        let mut p = WanKeyframeDeltaPacer::new(2, 65_536);
        assert_eq!(
            p.select_frame(4_000, 400),
            LiveFrameSelection::EmitKeyframe {
                frame_seq: 1,
                bytes: 4_000
            }
        );
        assert_eq!(
            p.select_frame(4_000, 400),
            LiveFrameSelection::EmitDelta {
                frame_seq: 2,
                bytes: 400,
                deltas_since_keyframe: 1
            }
        );
        assert_eq!(
            p.select_frame(4_000, 400),
            LiveFrameSelection::EmitDelta {
                frame_seq: 3,
                bytes: 400,
                deltas_since_keyframe: 2
            }
        );
        assert_eq!(
            p.select_frame(4_000, 400),
            LiveFrameSelection::EmitKeyframe {
                frame_seq: 4,
                bytes: 4_000
            }
        );
    }
}
