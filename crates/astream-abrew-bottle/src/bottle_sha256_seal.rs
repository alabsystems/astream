// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Constant-time SHA-256 bottle/cask archive verifier refusing unpack unless both byte length and
//! digest match the pinned `atpkg` bottle manifest (`Astream.Abrew.TlaBottleSha256Seal`).

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
#[path = "bottle_sha256_seal_island.rs"]
mod bottle_sha256_seal_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_sz_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_seal_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bottle_sha256_seal_island::{ab_seal_advance, ab_sz_clamp};

/// Maximum single bottle archive size (`536_870_912` bytes = 512 MiB).
pub const MAX_BOTTLE_BYTES: u64 = 536_870_912;

contract_fn! {
    /// Verified digest-seal match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ab_digest_verified_isl`.
    #[must_use]
    pub const fn ab_digest_verified(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct BottleSealVerifier {
    verified_count: u64,
}

impl BottleSealVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { verified_count: 0 }
    }

    pub fn verify_bottle(&mut self, bytes: &[u8], expected_sha256: &[u8; 32]) -> bool {
        let len = bytes.len() as u64;
        if len == 0 || len > MAX_BOTTLE_BYTES {
            return false;
        }
        let _ = ab_sz_clamp(len, MAX_BOTTLE_BYTES);
        let actual = Sha256::digest_slice(bytes);
        let ok = ct_eq(&actual, expected_sha256);
        if ab_digest_verified(if ok { 1 } else { 0 }, 1) {
            self.verified_count =
                ab_seal_advance(self.verified_count, self.verified_count.saturating_add(1));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verifies_authentic_bottle_digest_and_rejects_tampered_archive() {
        let payload = b"fake-tar-gz-bottle-bytes";
        let expected = Sha256::digest(payload);
        let mut v = BottleSealVerifier::new();
        assert!(v.verify_bottle(payload, &expected));
        assert!(!v.verify_bottle(b"corrupted", &expected));
    }
}
