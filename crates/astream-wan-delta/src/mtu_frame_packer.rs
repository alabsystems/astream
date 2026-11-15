// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Path-MTU (`<= 1200` B QUIC/VPN safe) coalescing packer batching small `ScreenOp` deltas
//! without exceeding one network packet (`Astream.WanDelta.TlaMtuFramePacker`).

#[cfg(clean_islands)]
#[path = "mtu_frame_packer_island.rs"]
mod mtu_frame_packer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mtu_payload_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mtu_flushed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use mtu_frame_packer_island::{mtu_flushed_advance, mtu_payload_clamp};

/// Conservative IPv6/WireGuard/QUIC payload ceiling (`1200` bytes).
pub const SAFE_WAN_MTU_BYTES: u64 = 1_200;

contract_fn! {
    /// Verified MTU fit check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mtu_within_budget_isl`.
    #[must_use]
    pub const fn mtu_within_budget(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Coalesces length-prefixed sub-records into MTU-bounded packets.
#[derive(Debug, Clone)]
pub struct MtuCoalescingPacker {
    mtu_cap: usize,
    current: Vec<u8>,
    packets_flushed: u64,
}

impl MtuCoalescingPacker {
    #[must_use]
    pub const fn new(mtu_cap: u64) -> Self {
        let c = mtu_payload_clamp(mtu_cap, SAFE_WAN_MTU_BYTES) as usize;
        Self {
            mtu_cap: if c < 16 { 16 } else { c },
            current: Vec::new(),
            packets_flushed: 0,
        }
    }

    /// Appends `item`; if adding `2 + item.len()` would exceed `mtu_cap`, flushes and returns
    /// the completed packet first!
    pub fn push_record(&mut self, item: &[u8]) -> Result<Option<Vec<u8>>, &'static str> {
        let framed_len = item.len().saturating_add(2);
        if !mtu_within_budget(self.mtu_cap as u64, framed_len as u64) {
            return Err("single record exceeds path MTU budget");
        }
        let mut flushed = None;
        let cand_len = self.current.len().saturating_add(framed_len);
        if !self.current.is_empty() && !mtu_within_budget(self.mtu_cap as u64, cand_len as u64) {
            flushed = self.flush();
        }
        self.current
            .extend_from_slice(&(item.len() as u16).to_le_bytes());
        self.current.extend_from_slice(item);
        Ok(flushed)
    }

    pub fn flush(&mut self) -> Option<Vec<u8>> {
        if self.current.is_empty() {
            return None;
        }
        self.packets_flushed =
            mtu_flushed_advance(self.packets_flushed, self.packets_flushed.saturating_add(1));
        Some(core::mem::take(&mut self.current))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mtu_packer_coalesces_small_deltas_and_flushes_at_exact_mtu_ceiling() {
        let mut p = MtuCoalescingPacker::new(20);
        assert!(p.push_record(b"hello").unwrap().is_none()); // 7B
        assert!(p.push_record(b"world").unwrap().is_none()); // 14B
        let pkt1 = p.push_record(b"third!").unwrap().unwrap(); // 14 + 8 = 22 > 20 -> flushes 14B!
        assert_eq!(pkt1.len(), 14);
        assert_eq!(p.flush().unwrap().len(), 8);
    }
}
