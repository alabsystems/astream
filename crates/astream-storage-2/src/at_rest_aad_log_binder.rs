// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! At-rest encryption AAD log-identity + monotonic-offset binder
//! (`Astream.Broker.TlaAtRestAadLogBinder`).
//!
//! Closes the cross-log / cross-offset ciphertext transplant gap by binding
//! `(log_epoch, log_id_tag, record_offset)` into a canonical 24-byte stack AAD
//! block (`[epoch_be8 || log_id_be8 || offset_be8]`) and enforcing monotonic
//! `sealed_offset` and `min_epoch` floors before sealing or opening records.

#[cfg(clean_islands)]
#[path = "at_rest_aad_log_binder_island.rs"]
mod at_rest_aad_log_binder_island;
#[cfg(clean_islands)]
pub use at_rest_aad_log_binder_island::{aad_epoch_advance, aad_offset_advance};

/// Fixed 24-byte AAD block (`8 + 8 + 8`).
pub const AT_REST_AAD_LEN: usize = 24;

#[cfg(not(clean_islands))]
/// Monotonically advance sealed offset watermark.
#[must_use]
pub const fn aad_offset_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance minimum accepted log epoch floor.
#[must_use]
pub const fn aad_epoch_advance(min_epoch: u64, cand_epoch: u64) -> u64 {
    if min_epoch < cand_epoch {
        cand_epoch
    } else {
        min_epoch
    }
}

contract_fn! {
    /// True iff `record_epoch >= min_epoch`.
    #[must_use]
    pub const fn aad_epoch_valid(record_epoch: u64, min_epoch: u64) -> bool
    clauses [ensures result == (min_epoch <= record_epoch)]
    {
        min_epoch <= record_epoch
    }
}

/// Refusal reasons when constructing or verifying log-bound at-rest AAD.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtRestAadError {
    ZeroLogId,
    StaleLogEpoch { got: u64, min_epoch: u64 },
    LogIdMismatch { expected: u64, got: u64 },
    NonMonotonicOffset { record_offset: u64, sealed_hwm: u64 },
}

/// Pure stack AAD binder binding at-rest ciphertexts to `(log_epoch, log_id_tag, offset)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtRestAadLogBinder {
    log_id_tag: u64,
    min_epoch: u64,
    sealed_hwm: u64,
    has_sealed: bool,
}

impl AtRestAadLogBinder {
    /// Construct a binder pinned to `log_id_tag` and `min_epoch`.
    pub const fn new(log_id_tag: u64, min_epoch: u64) -> Result<Self, AtRestAadError> {
        if log_id_tag == 0 {
            return Err(AtRestAadError::ZeroLogId);
        }
        Ok(Self {
            log_id_tag,
            min_epoch,
            sealed_hwm: 0,
            has_sealed: false,
        })
    }

    #[must_use]
    pub const fn log_id_tag(&self) -> u64 {
        self.log_id_tag
    }

    #[must_use]
    pub const fn min_epoch(&self) -> u64 {
        self.min_epoch
    }

    #[must_use]
    pub const fn sealed_hwm(&self) -> u64 {
        self.sealed_hwm
    }

    /// Ratchet the minimum accepted log epoch forward on failover promotion.
    pub fn ratchet_epoch(&mut self, next_epoch: u64) {
        self.min_epoch = aad_epoch_advance(self.min_epoch, next_epoch);
    }

    /// Encode canonical 24-byte AAD `[epoch_be8 || log_id_be8 || offset_be8]` for sealing.
    pub fn seal_aad(
        &mut self,
        record_epoch: u64,
        record_offset: u64,
    ) -> Result<[u8; AT_REST_AAD_LEN], AtRestAadError> {
        if !aad_epoch_valid(record_epoch, self.min_epoch) {
            return Err(AtRestAadError::StaleLogEpoch {
                got: record_epoch,
                min_epoch: self.min_epoch,
            });
        }
        if self.has_sealed && record_offset <= self.sealed_hwm {
            return Err(AtRestAadError::NonMonotonicOffset {
                record_offset,
                sealed_hwm: self.sealed_hwm,
            });
        }
        self.min_epoch = aad_epoch_advance(self.min_epoch, record_epoch);
        self.sealed_hwm = aad_offset_advance(self.sealed_hwm, record_offset);
        self.has_sealed = true;
        Ok(encode_aad_words(
            record_epoch,
            self.log_id_tag,
            record_offset,
        ))
    }

    /// Verify a 24-byte AAD header against expected log identity, epoch floor, and offset.
    pub const fn verify_open_aad(
        &self,
        aad: &[u8; AT_REST_AAD_LEN],
        expected_offset: u64,
    ) -> Result<u64, AtRestAadError> {
        let rec_epoch = u64::from_be_bytes([
            aad[0], aad[1], aad[2], aad[3], aad[4], aad[5], aad[6], aad[7],
        ]);
        let rec_log_id = u64::from_be_bytes([
            aad[8], aad[9], aad[10], aad[11], aad[12], aad[13], aad[14], aad[15],
        ]);
        let rec_off = u64::from_be_bytes([
            aad[16], aad[17], aad[18], aad[19], aad[20], aad[21], aad[22], aad[23],
        ]);
        if rec_log_id != self.log_id_tag {
            return Err(AtRestAadError::LogIdMismatch {
                expected: self.log_id_tag,
                got: rec_log_id,
            });
        }
        if !aad_epoch_valid(rec_epoch, self.min_epoch) {
            return Err(AtRestAadError::StaleLogEpoch {
                got: rec_epoch,
                min_epoch: self.min_epoch,
            });
        }
        if rec_off != expected_offset {
            return Err(AtRestAadError::NonMonotonicOffset {
                record_offset: rec_off,
                sealed_hwm: expected_offset,
            });
        }
        Ok(rec_epoch)
    }
}

const fn encode_aad_words(epoch: u64, log_id: u64, offset: u64) -> [u8; AT_REST_AAD_LEN] {
    let e = epoch.to_be_bytes();
    let l = log_id.to_be_bytes();
    let o = offset.to_be_bytes();
    [
        e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], l[0], l[1], l[2], l[3], l[4], l[5], l[6],
        l[7], o[0], o[1], o[2], o[3], o[4], o[5], o[6], o[7],
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_cross_log_stale_epoch_and_reordered_offset_transplants() {
        let mut binder = AtRestAadLogBinder::new(0xA7E2_0001_CAFE_BEEF, 3).unwrap();
        let aad0 = binder.seal_aad(3, 0).unwrap();
        let aad1 = binder.seal_aad(4, 1).unwrap();
        assert_eq!(binder.min_epoch(), 4);
        assert_eq!(binder.sealed_hwm(), 1);

        // Stale epoch 3 is rejected once ratcheted to 4:
        assert_eq!(
            binder.verify_open_aad(&aad0, 0),
            Err(AtRestAadError::StaleLogEpoch {
                got: 3,
                min_epoch: 4,
            })
        );
        assert_eq!(binder.verify_open_aad(&aad1, 1), Ok(4));
        // Cross-offset transplant rejected:
        assert_eq!(
            binder.verify_open_aad(&aad1, 2),
            Err(AtRestAadError::NonMonotonicOffset {
                record_offset: 1,
                sealed_hwm: 2,
            })
        );
        // Non-monotonic seal rejected:
        assert_eq!(
            binder.seal_aad(4, 1),
            Err(AtRestAadError::NonMonotonicOffset {
                record_offset: 1,
                sealed_hwm: 1,
            })
        );
    }
}
