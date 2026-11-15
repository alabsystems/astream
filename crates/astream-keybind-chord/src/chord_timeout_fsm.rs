// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-key leader-chord state machine (`Ctrl+B`, `Cmd+K`) flushing buffered prefix keys to the
//! child PTY if the second stroke does not arrive before the chord deadline
//! (`Astream.KeyChord.TlaChordTimeoutFsm`).

#[cfg(clean_islands)]
#[path = "chord_timeout_fsm_island.rs"]
mod chord_timeout_fsm_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_len_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_chord_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use chord_timeout_fsm_island::{kc_chord_advance, kc_len_clamp};

/// Maximum buffered chord stroke depth (`4`).
pub const MAX_CHORD_DEPTH: u64 = 4;

contract_fn! {
    /// Verified chord-timeout predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kc_chord_expired_isl`.
    #[must_use]
    pub const fn kc_chord_expired(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct LeaderChordFsm {
    pending_strokes: u64,
    deadline_ms: u64,
    timeout_ms: u64,
    resolved_chords: u64,
}

impl LeaderChordFsm {
    #[must_use]
    pub const fn new(timeout_ms: u64) -> Self {
        Self {
            pending_strokes: 0,
            deadline_ms: 0,
            timeout_ms: if timeout_ms == 0 { 500 } else { timeout_ms },
            resolved_chords: 0,
        }
    }

    pub fn arm_leader(&mut self, now_ms: u64) {
        self.pending_strokes =
            kc_len_clamp(self.pending_strokes.saturating_add(1), MAX_CHORD_DEPTH);
        self.deadline_ms = now_ms.saturating_add(self.timeout_ms);
    }

    pub fn flush_if_expired(&mut self, now_ms: u64) -> u64 {
        if self.pending_strokes == 0 {
            return 0;
        }
        if kc_chord_expired(now_ms, self.deadline_ms) {
            let flushed = self.pending_strokes;
            self.pending_strokes = 0;
            self.resolved_chords =
                kc_chord_advance(self.resolved_chords, self.resolved_chords.saturating_add(1));
            flushed
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_leader_stroke_before_deadline_and_flushes_after_timeout() {
        let mut fsm = LeaderChordFsm::new(400);
        fsm.arm_leader(1_000);
        assert_eq!(fsm.flush_if_expired(1_250), 0);
        assert_eq!(fsm.flush_if_expired(1_400), 1);
    }
}
