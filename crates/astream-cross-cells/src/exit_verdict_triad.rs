// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Three-state verification script exit-code classifier (`0 = Pass`, `1 = Refused`, `2 =
//! CouldNotRun` — shared by `scripts/verify-ready.sh` and `scripts/stock-check.sh` so `exit 2` is
//! never mistaken for `0`; `Astream.CrossCell.TlaExitVerdictTriad`).

#[cfg(clean_islands)]
#[path = "exit_verdict_triad_island.rs"]
mod exit_verdict_triad_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_code_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_vrd_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use exit_verdict_triad_island::{cc_code_clamp, cc_vrd_advance};

/// Maximum POSIX exit code (`255`).
pub const MAX_EXIT_STATUS: u64 = 255;

contract_fn! {
    /// Verified zero-exit pass predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_verdict_is_pass_isl`.
    #[must_use]
    pub const fn cc_verdict_is_pass(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateVerdict {
    Pass,
    Refused,
    CouldNotRun,
}

#[derive(Debug, Clone, Default)]
pub struct VerdictClassifier {
    classified: u64,
}

impl VerdictClassifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { classified: 0 }
    }

    pub fn from_exit_code(&mut self, raw_code: u64) -> GateVerdict {
        let code = cc_code_clamp(raw_code, MAX_EXIT_STATUS);
        self.classified = cc_vrd_advance(self.classified, self.classified.saturating_add(1));
        if cc_verdict_is_pass(0, code) {
            GateVerdict::Pass
        } else if code == 1 {
            GateVerdict::Refused
        } else {
            GateVerdict::CouldNotRun
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_pass_refused_and_could_not_run_exit_codes() {
        let mut c = VerdictClassifier::new();
        assert_eq!(c.from_exit_code(0), GateVerdict::Pass);
        assert_eq!(c.from_exit_code(1), GateVerdict::Refused);
        assert_eq!(c.from_exit_code(2), GateVerdict::CouldNotRun);
    }
}
