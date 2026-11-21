// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OpenSSH user/host certificate validity chain verifier, for identity bound to an external
//! authority (an SSH agent, OIDC) rather than a locally pinned host key, bounding validity spans
//! and advancing monotonic certificate serials (`Astream.ExtAuth.TlaSshCertValidity`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "ssh_cert_validity_island.rs"]
mod ssh_cert_validity_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_cert_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_serial_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ssh_cert_validity_island::{ext_cert_clamp, ext_serial_advance};

/// Maximum certificate validity window (`86_400_000` ms = 24 hours).
pub const MAX_CERT_VALIDITY_MS: u64 = 86_400_000;

contract_fn! {
    /// Verified active certificate horizon (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_cert_active_isl`.
    #[must_use]
    pub const fn ext_cert_active(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct SshCertVerifier {
    ca_fingerprint: [u8; 32],
    highest_serial: u64,
    max_validity_ms: u64,
    ca_valid: bool,
}

impl SshCertVerifier {
    #[must_use]
    pub fn new(ca_pubkey: &[u8], max_validity_ms: u64) -> Self {
        Self {
            ca_fingerprint: Sha256::digest_slice(ca_pubkey),
            highest_serial: 0,
            max_validity_ms: ext_cert_clamp(max_validity_ms, MAX_CERT_VALIDITY_MS),
            ca_valid: !ca_pubkey.is_empty(),
        }
    }

    pub fn verify_window(
        &mut self,
        presented_ca_pubkey: &[u8],
        serial: u64,
        valid_after_ms: u64,
        valid_before_ms: u64,
        now_ms: u64,
    ) -> bool {
        if !self.ca_valid
            || presented_ca_pubkey.is_empty()
            || serial == 0
            || valid_after_ms >= valid_before_ms
        {
            return false;
        }
        let presented_fp = Sha256::digest_slice(presented_ca_pubkey);
        if !ct_eq(&presented_fp, &self.ca_fingerprint) {
            return false;
        }
        if !ext_cert_active(now_ms, valid_after_ms) || !ext_cert_active(valid_before_ms, now_ms) {
            return false;
        }
        let span = valid_before_ms.saturating_sub(valid_after_ms);
        if !ext_cert_active(self.max_validity_ms, span) {
            return false;
        }
        self.highest_serial = ext_serial_advance(self.highest_serial, serial);
        true
    }

    #[must_use]
    pub const fn highest_serial(&self) -> u64 {
        self.highest_serial
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_ca_fingerprint_and_bounded_cert_lifetime() {
        let mut v = SshCertVerifier::new(b"ssh-ed25519-ca-root", 3_600_000);
        assert!(v.verify_window(b"ssh-ed25519-ca-root", 7, 1_000, 3_600_500, 2_000));
        assert!(!v.verify_window(b"wrong-ca", 8, 1_000, 2_000, 1_500));
        assert!(!v.verify_window(b"ssh-ed25519-ca-root", 9, 1_000, 9_000_000, 2_000));
        assert_eq!(v.highest_serial(), 7);
    }
}
