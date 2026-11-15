// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `astream-wire` & `astream-digest` headline substrate gate enforcing `unknown == 0` on both and
//! `runtime_checked <= 110` on `astream-wire` (`evidence/verify/trust-wire.md`,
//! `Astream.SmtGov.TlaWireZeroUnknownGate`).

#[cfg(clean_islands)]
#[path = "wire_zero_unknown_gate_island.rs"]
mod wire_zero_unknown_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_rt_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_wire_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use wire_zero_unknown_gate_island::{smt_rt_clamp, smt_wire_advance};

/// Pinned `runtime_checked` ceiling for `astream-wire` (`110`).
pub const WIRE_RUNTIME_CHECKED_CAP: u64 = 110;

contract_fn! {
    /// Verified substrate qualification (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `smt_wire_qualified_isl`.
    #[must_use]
    pub const fn smt_wire_qualified(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Enforces the stricter zero-unknown / bounded-runtime-check bar on `astream-wire` & `astream-digest`.
#[derive(Debug, Clone, Default)]
pub struct SubstrateZeroUnknownGate {
    runs: u64,
}

impl SubstrateZeroUnknownGate {
    #[must_use]
    pub const fn new() -> Self {
        Self { runs: 0 }
    }

    pub fn check_substrate(
        &mut self,
        wire_unknown: u64,
        wire_runtime_checked: u64,
        digest_unknown: u64,
    ) -> Result<(), &'static str> {
        self.runs = smt_wire_advance(self.runs, self.runs.saturating_add(1));
        if wire_unknown != 0 || digest_unknown != 0 {
            return Err("substrate regression: unknown > 0 in astream-wire or astream-digest");
        }
        let rt = smt_rt_clamp(
            wire_runtime_checked,
            WIRE_RUNTIME_CHECKED_CAP.saturating_add(1),
        );
        if !smt_wire_qualified(WIRE_RUNTIME_CHECKED_CAP, rt) {
            return Err("astream-wire runtime_checked exceeded 110 ceiling");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substrate_gate_enforces_zero_unknown_and_110_runtime_checked_cap() {
        let mut g = SubstrateZeroUnknownGate::new();
        assert!(g.check_substrate(0, 84, 0).is_ok());
        assert!(g.check_substrate(1, 84, 0).is_err());
        assert!(g.check_substrate(0, 111, 0).is_err());
    }
}
