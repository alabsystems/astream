// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Forward-secure HMAC-SHA256 key-epoch ratchet wiping prior epoch secrets on rotation so a
//! post-compromise key disclosure cannot forge audit MACs from earlier epochs
//! (`astream_digest::hmac_sha256_wiping`, `Astream.Audit.TlaRatchetKeyEpoch`).

use astream_digest::{ct_eq, hmac_sha256_wiping};

#[cfg(clean_islands)]
#[path = "ratchet_key_epoch_island.rs"]
mod ratchet_key_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ratchet_step_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn w14_ratchet_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ratchet_key_epoch_island::{ratchet_step_clamp, w14_ratchet_epoch_advance};

/// Maximum single-call forward ratchet jump (`1024` epochs).
pub const MAX_RATCHET_STEPS_PER_CALL: u64 = 1_024;

contract_fn! {
    /// Verified epoch monotonicity (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ratchet_epoch_at_least_isl`.
    #[must_use]
    pub const fn ratchet_epoch_at_least(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Forward-secure MAC key ratchet wiping old keys in `Drop` and on every step.
pub struct ForwardSecureKeyRatchet {
    epoch: u64,
    chain_key: [u8; 32],
}

impl Drop for ForwardSecureKeyRatchet {
    fn drop(&mut self) {
        self.chain_key.fill(0);
        core::hint::black_box(&self.chain_key);
    }
}

#[inline(never)]
fn ratchet_hmac_2(key: &[u8; 32], a: &[u8], b: &[u8]) -> [u8; 32] {
    hmac_sha256_wiping(key, &[a, b])
}

impl ForwardSecureKeyRatchet {
    #[must_use]
    pub const fn new(root_seed: [u8; 32]) -> Self {
        Self {
            epoch: 0,
            chain_key: root_seed,
        }
    }

    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Ratchets forward by `steps` (`clamped <= MAX_RATCHET_STEPS_PER_CALL`), overwriting the
    /// previous chain key irreversibly on each step.
    pub fn ratchet_by(&mut self, steps: u64) -> u64 {
        let bounded = ratchet_step_clamp(steps, MAX_RATCHET_STEPS_PER_CALL);
        let mut s = 0u64;
        while s < bounded {
            let next_ep = self.epoch.saturating_add(1);
            let next_ck = ratchet_hmac_2(
                &self.chain_key,
                b"ASTREAM-RATCHET-NEXT-V1\0",
                &next_ep.to_le_bytes(),
            );
            self.chain_key.fill(0);
            core::hint::black_box(&self.chain_key);
            self.chain_key = next_ck;
            self.epoch = w14_ratchet_epoch_advance(self.epoch, next_ep);
            s = s.saturating_add(1);
        }
        self.epoch
    }

    /// Computes a domain-separated audit record MAC under the current epoch's derived message key.
    #[must_use]
    pub fn seal_record_mac(&self, record_offset: u64, body: &[u8]) -> [u8; 32] {
        let msg_key = ratchet_hmac_2(
            &self.chain_key,
            b"ASTREAM-RATCHET-MSG-V1\0",
            &self.epoch.to_le_bytes(),
        );
        let tag = ratchet_hmac_2(&msg_key, &record_offset.to_le_bytes(), body);
        let mut wipe = msg_key;
        wipe.fill(0);
        core::hint::black_box(&wipe);
        tag
    }

    #[must_use]
    pub fn verify_current_mac(
        &self,
        min_epoch: u64,
        record_offset: u64,
        body: &[u8],
        tag: &[u8; 32],
    ) -> bool {
        if !ratchet_epoch_at_least(self.epoch, min_epoch) {
            return false;
        }
        let expected = self.seal_record_mac(record_offset, body);
        ct_eq(&expected, tag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn forward_ratchet_matches_twin_at_same_epoch_and_invalidates_prior_epoch_keys() {
        let mut signer = ForwardSecureKeyRatchet::new([0x11; 32]);
        let mut verifier = ForwardSecureKeyRatchet::new([0x11; 32]);
        let mac0 = signer.seal_record_mac(10, b"audit-event-0");
        assert!(verifier.verify_current_mac(0, 10, b"audit-event-0", &mac0));

        assert_eq!(signer.ratchet_by(3), 3);
        let mac3 = signer.seal_record_mac(11, b"audit-event-3");
        assert!(!verifier.verify_current_mac(0, 11, b"audit-event-3", &mac3));
        assert_eq!(verifier.ratchet_by(3), 3);
        assert!(verifier.verify_current_mac(3, 11, b"audit-event-3", &mac3));
    }
}
