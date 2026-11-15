// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Z3 `stop_causes["wall-backstop"] == 0` & `contract_panics == 0` report watchdog enforcing
//! `publish/README.md` (`TAKEN 2026-10-20`) qualification gates (`Astream.SmtGov.TlaRlimitWatchdog`).

#[cfg(clean_islands)]
#[path = "rlimit_watchdog_island.rs"]
mod rlimit_watchdog_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_ms_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_proved_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use rlimit_watchdog_island::{smt_ms_clamp, smt_proved_advance};

/// Per-target verification wall-time soft alert (`300_000` ms == 5 min).
pub const MAX_TARGET_SOLVE_MS: u64 = 300_000;

contract_fn! {
    /// Verified zero-backstop check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `smt_no_backstop_isl`.
    #[must_use]
    pub const fn smt_no_backstop(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Validates `report.json` solver stop-causes and completeness flags.
#[derive(Debug, Clone, Default)]
pub struct SolverBackstopWatchdog {
    cumulative_proved: u64,
}

impl SolverBackstopWatchdog {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            cumulative_proved: 0,
        }
    }

    pub fn check_report(
        &mut self,
        proved: u64,
        wall_backstop: u64,
        contract_panics: u64,
        coverage_complete: bool,
        elapsed_ms: u64,
    ) -> Result<u64, &'static str> {
        let _ = smt_ms_clamp(elapsed_ms, MAX_TARGET_SOLVE_MS);
        if !coverage_complete {
            return Err("coverage_complete == false in Trust verification report");
        }
        let bad = wall_backstop.saturating_add(contract_panics);
        if !smt_no_backstop(0, bad) {
            return Err("wall-backstop > 0 or contract_panics > 0 in Trust verification report");
        }
        self.cumulative_proved = smt_proved_advance(
            self.cumulative_proved,
            self.cumulative_proved.saturating_add(proved),
        );
        Ok(self.cumulative_proved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn watchdog_accepts_complete_zero_backstop_report_and_refuses_wall_backstop() {
        let mut w = SolverBackstopWatchdog::new();
        assert_eq!(w.check_report(420, 0, 0, true, 12_000).unwrap(), 420);
        assert!(w.check_report(420, 1, 0, true, 12_000).is_err());
        assert!(w.check_report(420, 0, 0, false, 12_000).is_err());
    }
}
