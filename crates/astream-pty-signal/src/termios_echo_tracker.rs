// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY `termios` `ECHO` / `ICANON` mode observer disabling `astream-term::predict` speculative
//! keystroke echo whenever `sudo` or `ssh` turns off local echo for password entry
//! (`Astream.PtySig.TlaTermiosEchoTracker`).

#[cfg(clean_islands)]
#[path = "termios_echo_tracker_island.rs"]
mod termios_echo_tracker_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_mode_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_echo_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use termios_echo_tracker_island::{pty_echo_advance, pty_mode_clamp};

/// Mode bitmask cap (`3`: bit 0 = `ECHO`, bit 1 = `ICANON`).
pub const MAX_ECHO_MASK: u64 = 3;

contract_fn! {
    /// Verified local-prediction safety check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_predict_allowed_isl`.
    #[must_use]
    pub const fn pty_predict_allowed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TermiosEchoGate {
    echo_enabled: bool,
    samples: u64,
}

impl TermiosEchoGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            echo_enabled: true,
            samples: 0,
        }
    }

    pub fn observe_lflag(&mut self, echo_on: bool, icanon_on: bool) -> bool {
        let mask = (if echo_on { 1u64 } else { 0u64 }) | (if icanon_on { 2u64 } else { 0u64 });
        let _ = pty_mode_clamp(mask, MAX_ECHO_MASK);
        self.echo_enabled = echo_on;
        self.samples = pty_echo_advance(self.samples, self.samples.saturating_add(1));
        pty_predict_allowed(if self.echo_enabled { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_local_echo_prediction_during_no_echo_password_prompt() {
        let mut g = TermiosEchoGate::new();
        assert!(!g.observe_lflag(false, true));
        assert!(g.observe_lflag(true, false));
    }
}
