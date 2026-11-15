// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Tentative speculative-echo underline span tracker clearing unconfirmed cell styling as causal
//! server `Out` acknowledgements advance `confirmed_seq` (`Astream.SpecEcho.TlaUnderlineTentativeSpan`).

#[cfg(clean_islands)]
#[path = "underline_tentative_span_island.rs"]
mod underline_tentative_span_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_span_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_ack_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use underline_tentative_span_island::{se_ack_advance, se_span_clamp};

/// Maximum tentative speculative cells highlighted simultaneously (`256`).
pub const MAX_TENTATIVE_CELLS: u64 = 256;

contract_fn! {
    /// Verified zero-pending-tentative check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `se_all_confirmed_isl`.
    #[must_use]
    pub const fn se_all_confirmed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TentativeUnderlineTracker {
    latest_sent_seq: u64,
    confirmed_seq: u64,
}

impl TentativeUnderlineTracker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            latest_sent_seq: 0,
            confirmed_seq: 0,
        }
    }

    pub fn record_speculative_stroke(&mut self, seq: u64) -> u64 {
        if seq > self.latest_sent_seq {
            self.latest_sent_seq = seq;
        }
        se_span_clamp(
            self.latest_sent_seq.saturating_sub(self.confirmed_seq),
            MAX_TENTATIVE_CELLS,
        )
    }

    pub fn acknowledge_seq(&mut self, ack_seq: u64) -> bool {
        self.confirmed_seq = se_ack_advance(self.confirmed_seq, ack_seq);
        se_all_confirmed(self.confirmed_seq, self.latest_sent_seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_unconfirmed_strokes_and_clears_underline_when_caught_up() {
        let mut t = TentativeUnderlineTracker::new();
        assert_eq!(t.record_speculative_stroke(3), 3);
        assert!(!t.acknowledge_seq(2));
        assert!(t.acknowledge_seq(3));
    }
}
