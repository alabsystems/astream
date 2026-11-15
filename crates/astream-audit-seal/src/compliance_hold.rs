// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WORM legal/incident retention hold clamping `retain_before` below pinned `[start_off, end_off)`
//! ranges (`Astream.Audit.TlaComplianceHold`).

#[cfg(clean_islands)]
#[path = "compliance_hold_island.rs"]
mod compliance_hold_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hold_ranges_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hold_floor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use compliance_hold_island::{hold_floor_advance, hold_ranges_clamp};

/// Maximum concurrent WORM incident holds on one log.
pub const MAX_COMPLIANCE_HOLDS: u64 = 128;

contract_fn! {
    /// Verified hold ceiling check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `hold_retains_above_isl`.
    #[must_use]
    pub const fn hold_retains_above(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WormHoldPin {
    pub hold_id: String,
    pub start_offset: u64,
    pub expires_bt_ms: u64,
}

/// Clamps retention cuts so active WORM holds are never truncated!
#[derive(Debug, Clone, Default)]
pub struct ComplianceHoldTable {
    committed_floor: u64,
    pins: Vec<WormHoldPin>,
}

impl ComplianceHoldTable {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            committed_floor: 0,
            pins: Vec::new(),
        }
    }

    pub fn place_hold(&mut self, pin: WormHoldPin) -> Result<(), &'static str> {
        if pin.hold_id.is_empty() || pin.expires_bt_ms == 0 {
            return Err("invalid compliance hold id or zero expiry");
        }
        let cap = hold_ranges_clamp(MAX_COMPLIANCE_HOLDS, MAX_COMPLIANCE_HOLDS) as usize;
        for existing in &mut self.pins {
            if existing.hold_id == pin.hold_id {
                if !hold_retains_above(pin.start_offset, self.committed_floor) {
                    return Err("cannot place hold below already-evicted retention floor");
                }
                if pin.start_offset < existing.start_offset {
                    existing.start_offset = pin.start_offset;
                }
                if pin.expires_bt_ms > existing.expires_bt_ms {
                    existing.expires_bt_ms = pin.expires_bt_ms;
                }
                return Ok(());
            }
        }
        if self.pins.len() >= cap {
            return Err("compliance hold table full");
        }
        if !hold_retains_above(pin.start_offset, self.committed_floor) {
            return Err("cannot place hold below already-evicted retention floor");
        }
        self.pins.push(pin);
        Ok(())
    }

    /// Computes the maximum safe `retain_before` cut (`<= proposed_cut`) at `now_bt_ms`.
    pub fn clamp_retention_cut(&mut self, proposed_cut: u64, now_bt_ms: u64) -> u64 {
        let mut active_pins = Vec::new();
        let mut safe_cut = proposed_cut;
        let old_pins = core::mem::take(&mut self.pins);
        for p in old_pins {
            if now_bt_ms < p.expires_bt_ms {
                if p.start_offset < safe_cut {
                    safe_cut = p.start_offset;
                }
                active_pins.push(p);
            }
        }
        self.pins = active_pins;
        self.committed_floor = hold_floor_advance(self.committed_floor, safe_cut);
        self.committed_floor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worm_hold_blocks_retention_cut_until_hold_expiry() {
        let mut t = ComplianceHoldTable::new();
        t.place_hold(WormHoldPin {
            hold_id: "inc-42".to_owned(),
            start_offset: 120,
            expires_bt_ms: 5_000,
        })
        .unwrap();
        assert_eq!(t.clamp_retention_cut(500, 3_000), 120);
        assert_eq!(t.clamp_retention_cut(500, 5_000), 500);
    }
}
