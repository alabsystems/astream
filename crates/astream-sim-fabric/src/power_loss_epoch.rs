// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Simulated block-device `F_BARRIERFSYNC` prefix-epoch cutter modeling durable, barrier-issued,
//! and volatile write epochs (`broker.crash-sim.prefix-law`, `Astream.SimFabric.TlaPowerLossEpoch`).

#[cfg(clean_islands)]
#[path = "power_loss_epoch_island.rs"]
mod power_loss_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_blocks_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_barrier_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use power_loss_epoch_island::{sim_barrier_advance, sim_blocks_clamp};

/// Maximum barrier epochs queued before full flush (`256`).
pub const MAX_ISSUED_BARRIER_EPOCHS: u64 = 256;

contract_fn! {
    /// Verified durable prefix (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sim_prefix_durable_isl`.
    #[must_use]
    pub const fn sim_prefix_durable(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Models `durable` bytes + ordered `F_BARRIERFSYNC` epochs on a simulated storage volume.
#[derive(Debug, Clone, Default)]
pub struct BarrierEpochModel {
    durable_bytes: Vec<u8>,
    issued_epochs: Vec<Vec<u8>>,
    volatile_tail: Vec<u8>,
    barriers_issued: u64,
}

impl BarrierEpochModel {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            durable_bytes: Vec::new(),
            issued_epochs: Vec::new(),
            volatile_tail: Vec::new(),
            barriers_issued: 0,
        }
    }

    pub fn append_volatile(&mut self, bytes: &[u8]) {
        self.volatile_tail.extend_from_slice(bytes);
    }

    pub fn barrier_fsync(&mut self) {
        let cap = sim_blocks_clamp(MAX_ISSUED_BARRIER_EPOCHS, MAX_ISSUED_BARRIER_EPOCHS) as usize;
        if !self.volatile_tail.is_empty() && self.issued_epochs.len() < cap {
            let chunk = core::mem::take(&mut self.volatile_tail);
            self.issued_epochs.push(chunk);
            self.barriers_issued =
                sim_barrier_advance(self.barriers_issued, self.barriers_issued.saturating_add(1));
        }
    }

    pub fn full_fsync(&mut self) {
        self.barrier_fsync();
        for ep in core::mem::take(&mut self.issued_epochs) {
            self.durable_bytes.extend_from_slice(&ep);
        }
    }

    /// Synthesizes a power-loss image keeping `durable_bytes` plus `0..keep_epochs` barrier epochs.
    #[must_use]
    pub fn crash_image(&self, keep_epochs: usize) -> Vec<u8> {
        let mut img = self.durable_bytes.clone();
        let mut idx = 0usize;
        while idx < self.issued_epochs.len() && idx < keep_epochs {
            if let Some(ep) = self.issued_epochs.get(idx) {
                img.extend_from_slice(ep);
            }
            idx = idx.saturating_add(1);
        }
        let _ = sim_prefix_durable(img.len() as u64, self.durable_bytes.len() as u64);
        img
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn barrier_epoch_model_preserves_full_fsync_and_strict_prefix_of_barrier_epochs() {
        let mut dev = BarrierEpochModel::new();
        dev.append_volatile(b"B0:");
        dev.full_fsync();
        dev.append_volatile(b"B1:");
        dev.barrier_fsync();
        dev.append_volatile(b"B2:");
        dev.barrier_fsync();
        assert_eq!(dev.crash_image(0), b"B0:");
        assert_eq!(dev.crash_image(1), b"B0:B1:");
        assert_eq!(dev.crash_image(2), b"B0:B1:B2:");
    }
}
