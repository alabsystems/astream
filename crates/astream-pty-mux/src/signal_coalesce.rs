// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone foreground process-group signal escalation ladder (`SIGINT -> SIGTERM -> SIGHUP -> SIGKILL`)
//! (`Astream.PtyMux.TlaSignalCoalesce`).

#[cfg(clean_islands)]
#[path = "signal_coalesce_island.rs"]
mod signal_coalesce_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sig_stage_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sig_escalate_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use signal_coalesce_island::{sig_escalate_advance, sig_stage_clamp};

/// Terminal stage `3` = `SIGKILL` (`9`).
pub const MAX_SIGNAL_STAGE: u64 = 3;

contract_fn! {
    /// Verified grace-window expiry (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sig_grace_elapsed_isl`.
    #[must_use]
    pub const fn sig_grace_elapsed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PosixStopSignal {
    SigInt,
    SigTerm,
    SigHup,
    SigKill,
}

/// Escalating process-group terminator avoiding duplicate signal storms within `grace_ms`.
#[derive(Debug, Clone)]
pub struct SignalEscalationLadder {
    grace_ms: u64,
    stage: u64,
    next_escalate_ms: u64,
    started: bool,
}

impl SignalEscalationLadder {
    #[must_use]
    pub const fn new(grace_ms: u64) -> Self {
        Self {
            grace_ms: if grace_ms == 0 { 250 } else { grace_ms },
            stage: 0,
            next_escalate_ms: 0,
            started: false,
        }
    }

    pub fn poll_signal(&mut self, now_ms: u64) -> Option<PosixStopSignal> {
        if !self.started {
            self.started = true;
            self.stage = 0;
            self.next_escalate_ms = now_ms.saturating_add(self.grace_ms);
            return Some(PosixStopSignal::SigInt);
        }
        if !sig_grace_elapsed(now_ms, self.next_escalate_ms) || self.stage >= MAX_SIGNAL_STAGE {
            return None;
        }
        let next = sig_stage_clamp(self.stage.saturating_add(1), MAX_SIGNAL_STAGE);
        self.stage = sig_escalate_advance(self.stage, next);
        self.next_escalate_ms = now_ms.saturating_add(self.grace_ms);
        match self.stage {
            1 => Some(PosixStopSignal::SigTerm),
            2 => Some(PosixStopSignal::SigHup),
            _ => Some(PosixStopSignal::SigKill),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signal_ladder_coalesces_within_grace_and_escalates_to_sigkill() {
        let mut s = SignalEscalationLadder::new(500);
        assert_eq!(s.poll_signal(1_000), Some(PosixStopSignal::SigInt));
        assert_eq!(s.poll_signal(1_200), None);
        assert_eq!(s.poll_signal(1_500), Some(PosixStopSignal::SigTerm));
        assert_eq!(s.poll_signal(2_000), Some(PosixStopSignal::SigHup));
        assert_eq!(s.poll_signal(2_500), Some(PosixStopSignal::SigKill));
        assert_eq!(s.poll_signal(3_500), None);
    }
}
