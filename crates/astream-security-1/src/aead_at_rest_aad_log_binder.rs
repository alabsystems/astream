// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! At-rest encrypted log Associated Authenticated Data (`AAD`) log-identity & offset binder
//! (`AUDIT-2026-09.md`; `Astream.Aead.TlaAtRestAadLogBinder`).
//!
//! Eliminates cross-log and cross-offset ciphertext transplantation under a shared at-rest key:
//! constructs a canonical 32-byte little-endian AAD tag `(log_id_hi, log_id_lo, lineage_epoch,
//! record_offset)` and enforces monotone append offset progression via
//! [`aad_sealed_offset_advance_b122`] and exact lineage matching via [`aad_lineage_matches_b122`].

#[cfg(clean_islands)]
#[path = "aead_at_rest_aad_log_binder_island.rs"]
mod aead_at_rest_aad_log_binder_island;
#[cfg(clean_islands)]
pub use aead_at_rest_aad_log_binder_island::{
    aad_header_len_clamp_b122, aad_sealed_offset_advance_b122,
};

#[cfg(not(clean_islands))]
/// Clamp AAD descriptor length to `max_len`.
#[must_use]
pub const fn aad_header_len_clamp_b122(cand_len: u64, max_len: u64) -> u64 {
    if cand_len < max_len {
        cand_len
    } else {
        max_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the highest sealed log offset.
#[must_use]
pub const fn aad_sealed_offset_advance_b122(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

contract_fn! {
    /// True iff `expected_epoch` matches `actual_epoch`.
    #[must_use]
    pub const fn aad_lineage_matches_b122(expected_epoch: u64, actual_epoch: u64) -> bool
    clauses [ensures result == (expected_epoch == actual_epoch)]
    {
        expected_epoch == actual_epoch
    }
}

/// Fixed 32-byte canonical AAD binding `(log_id_hi, log_id_lo, lineage_epoch, record_offset)`.
pub const AT_REST_LOG_AAD_LEN: usize = 32;

/// Encode `(log_id_hi, log_id_lo, lineage_epoch, record_offset)` into a 32-byte AAD array.
#[must_use]
pub const fn encode_log_record_aad(
    log_id_hi: u64,
    log_id_lo: u64,
    lineage_epoch: u64,
    record_offset: u64,
) -> [u8; AT_REST_LOG_AAD_LEN] {
    let b0 = log_id_hi.to_le_bytes();
    let b1 = log_id_lo.to_le_bytes();
    let b2 = lineage_epoch.to_le_bytes();
    let b3 = record_offset.to_le_bytes();
    [
        b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7], b1[0], b1[1], b1[2], b1[3], b1[4],
        b1[5], b1[6], b1[7], b2[0], b2[1], b2[2], b2[3], b2[4], b2[5], b2[6], b2[7], b3[0], b3[1],
        b3[2], b3[3], b3[4], b3[5], b3[6], b3[7],
    ]
}

/// Stateful per-log AAD binder preventing cross-log and cross-offset ciphertext splice attacks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtRestAadLogBinder {
    log_id_hi: u64,
    log_id_lo: u64,
    lineage_epoch: u64,
    has_sealed_any: bool,
    highest_sealed_offset: u64,
    aad_len_bytes: u64,
}

impl AtRestAadLogBinder {
    #[must_use]
    pub const fn new(log_id_hi: u64, log_id_lo: u64, lineage_epoch: u64) -> Self {
        let len = aad_header_len_clamp_b122(AT_REST_LOG_AAD_LEN as u64, AT_REST_LOG_AAD_LEN as u64);
        Self {
            log_id_hi,
            log_id_lo,
            lineage_epoch,
            has_sealed_any: false,
            highest_sealed_offset: 0,
            aad_len_bytes: len,
        }
    }

    #[must_use]
    pub const fn aad_len_bytes(&self) -> u64 {
        self.aad_len_bytes
    }

    /// Derive the 32-byte AAD for sealing `record_offset`, refusing non-monotonic offsets.
    pub fn seal_aad_for_offset(&mut self, record_offset: u64) -> Option<[u8; AT_REST_LOG_AAD_LEN]> {
        if self.has_sealed_any && record_offset <= self.highest_sealed_offset {
            return None;
        }
        self.has_sealed_any = true;
        self.highest_sealed_offset =
            aad_sealed_offset_advance_b122(self.highest_sealed_offset, record_offset);
        Some(encode_log_record_aad(
            self.log_id_hi,
            self.log_id_lo,
            self.lineage_epoch,
            record_offset,
        ))
    }

    /// Verify that a presented `(cand_hi, cand_lo, cand_epoch, record_offset)` matches this log's
    /// identity and lineage and produce the exact expected 32-byte AAD for AEAD open.
    #[must_use]
    pub const fn open_aad_if_bound(
        &self,
        cand_hi: u64,
        cand_lo: u64,
        cand_epoch: u64,
        record_offset: u64,
    ) -> Option<[u8; AT_REST_LOG_AAD_LEN]> {
        if cand_hi != self.log_id_hi || cand_lo != self.log_id_lo {
            return None;
        }
        if !aad_lineage_matches_b122(self.lineage_epoch, cand_epoch) {
            return None;
        }
        Some(encode_log_record_aad(
            self.log_id_hi,
            self.log_id_lo,
            self.lineage_epoch,
            record_offset,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_aad_to_log_lineage_and_monotone_offset() {
        let mut binder = AtRestAadLogBinder::new(0xCAFE_0001, 0xBEEF_0002, 7);
        assert_eq!(binder.aad_len_bytes(), 32);

        let aad0 = binder.seal_aad_for_offset(0).expect("offset 0");
        let aad1 = binder.seal_aad_for_offset(1).expect("offset 1");
        assert_ne!(aad0, aad1);
        // Duplicate or regressed offset refused fail-closed!
        assert!(binder.seal_aad_for_offset(1).is_none());
        assert!(binder.seal_aad_for_offset(0).is_none());

        // Different log_id or lineage_epoch refused on open!
        assert!(binder
            .open_aad_if_bound(0xDEAD, 0xBEEF_0002, 7, 1)
            .is_none());
        assert!(binder
            .open_aad_if_bound(0xCAFE_0001, 0xBEEF_0002, 6, 1)
            .is_none());
        assert_eq!(
            binder.open_aad_if_bound(0xCAFE_0001, 0xBEEF_0002, 7, 1),
            Some(aad1)
        );
    }
}
