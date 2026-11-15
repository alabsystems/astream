// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `SealedStream` record-aligned relay chunk sizer packing whole ciphertext records (`<= 64` KiB)
//! into socket writes without mid-record fragmentation (`Astream.Tunnel.TlaSpliceZeroCopyMeter`).

#[cfg(clean_islands)]
#[path = "splice_zero_copy_meter_island.rs"]
mod splice_zero_copy_meter_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_chunk_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_spliced_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use splice_zero_copy_meter_island::{tun_chunk_clamp, tun_spliced_advance};

/// Maximum single relay splice batch (`65_536` bytes).
pub const MAX_SPLICE_BATCH_BYTES: u64 = 65_536;

contract_fn! {
    /// Verified non-empty aligned batch (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tun_record_aligned_isl`.
    #[must_use]
    pub const fn tun_record_aligned(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes the largest whole-record byte prefix fitting inside `socket_sndbuf_bytes`.
#[derive(Debug, Clone, Default)]
pub struct RecordAlignedSplicer {
    total_spliced: u64,
}

impl RecordAlignedSplicer {
    #[must_use]
    pub const fn new() -> Self {
        Self { total_spliced: 0 }
    }

    pub fn plan_batch(&mut self, record_lengths: &[u32], socket_sndbuf_bytes: u64) -> usize {
        let budget = tun_chunk_clamp(socket_sndbuf_bytes, MAX_SPLICE_BATCH_BYTES);
        let mut batch_bytes = 0u64;
        for &rlen in record_lengths {
            if rlen == 0 {
                break;
            }
            let next = batch_bytes.saturating_add(u64::from(rlen));
            if next > budget {
                break;
            }
            batch_bytes = next;
        }
        if tun_record_aligned(batch_bytes, 1) {
            self.total_spliced = tun_spliced_advance(
                self.total_spliced,
                self.total_spliced.saturating_add(batch_bytes),
            );
        }
        batch_bytes as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splicer_packs_whole_records_without_splitting_trailing_ciphertext_frame() {
        let mut s = RecordAlignedSplicer::new();
        assert_eq!(s.plan_batch(&[4_096, 4_096, 4_096], 10_000), 8_192);
    }
}
