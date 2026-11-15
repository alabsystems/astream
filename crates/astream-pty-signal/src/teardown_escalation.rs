// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ordered PTY session signal escalation (`SIGHUP` -> grace -> `SIGTERM` -> grace -> `SIGKILL`)
//! reaping whole process groups cleanly when an `aterm` tab closes (`Astream.PtySig.TlaTeardownEscalation`).

#[cfg(clean_islands)]
#[path = "teardown_escalation_island.rs"]
mod teardown_escalation_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_stage_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_reap_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use teardown_escalation_island::{pty_reap_advance, pty_stage_clamp};

/// Highest signal stage (`0 = Live`, `1 = SentHup`, `2 = SentTerm`, `3 = SentKill`).
pub const MAX_REAP_STAGE: u64 = 3;

contract_fn! {
    /// Verified grace-deadline expiry check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_reap_due_isl`.
    #[must_use]
    pub const fn pty_reap_due(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReapSignal {
    WaitGrace,
    SendSighup,
    SendSigterm,
    SendSigkill,
}

#[derive(Debug, Clone)]
pub struct PtyReaper {
    stage: u64,
    grace_ms: u64,
    next_deadline_ms: u64,
}

impl PtyReaper {
    #[must_use]
    pub const fn new(grace_ms: u64) -> Self {
        Self {
            stage: 0,
            grace_ms: if grace_ms == 0 { 250 } else { grace_ms },
            next_deadline_ms: 0,
        }
    }

    pub fn poll_signal(&mut self, now_ms: u64) -> ReapSignal {
        if self.stage == 0 {
            self.stage = pty_stage_clamp(1, MAX_REAP_STAGE);
            self.next_deadline_ms = now_ms.saturating_add(self.grace_ms);
            return ReapSignal::SendSighup;
        }
        if !pty_reap_due(now_ms, self.next_deadline_ms) {
            return ReapSignal::WaitGrace;
        }
        let next = pty_stage_clamp(self.stage.saturating_add(1), MAX_REAP_STAGE);
        self.stage = pty_reap_advance(self.stage, next);
        self.next_deadline_ms = now_ms.saturating_add(self.grace_ms);
        match self.stage {
            2 => ReapSignal::SendSigterm,
            _ => ReapSignal::SendSigkill,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escalates_from_sighup_to_sigterm_to_sigkill_across_grace_windows() {
        let mut r = PtyReaper::new(200);
        assert_eq!(r.poll_signal(1_000), ReapSignal::SendSighup);
        assert_eq!(r.poll_signal(1_100), ReapSignal::WaitGrace);
        assert_eq!(r.poll_signal(1_200), ReapSignal::SendSigterm);
        assert_eq!(r.poll_signal(1_400), ReapSignal::SendSigkill);
    }
}
