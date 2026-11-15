// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg` / `abrew` content-addressed bottle SHA-256 and exact byte-length verifier before
//! unpacking into the managed prefix (`aterm help abrew`, `Astream.Abrew.TlaBottleShaVerify`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "bottle_sha_verify_island.rs"]
mod bottle_sha_verify_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_bottle_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_verified_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bottle_sha_verify_island::{pkg_bottle_clamp, pkg_verified_advance};

/// Maximum single bottle archive size (`512` MiB).
pub const MAX_BOTTLE_ARCHIVE_BYTES: u64 = 512 * 1024 * 1024;

contract_fn! {
    /// Verified size check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_size_matches_isl`.
    #[must_use]
    pub const fn pkg_size_matches(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Verifies bottle payload against manifest `(expected_size, expected_sha256)` in constant time.
#[derive(Debug, Clone, Default)]
pub struct BottleArchiveVerifier {
    verified_count: u64,
}

impl BottleArchiveVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { verified_count: 0 }
    }

    pub fn verify_bottle(
        &mut self,
        archive: &[u8],
        expected_size: u64,
        expected_sha256: &[u8; 32],
    ) -> Result<u64, &'static str> {
        let cap = pkg_bottle_clamp(MAX_BOTTLE_ARCHIVE_BYTES, MAX_BOTTLE_ARCHIVE_BYTES);
        let actual = archive.len() as u64;
        if expected_size == 0 || actual != expected_size || !pkg_size_matches(cap, actual) {
            return Err("bottle size mismatch or exceeds archive cap");
        }
        let digest = Sha256::digest_slice(archive);
        if !ct_eq(&digest, expected_sha256) {
            return Err("bottle SHA-256 digest mismatch");
        }
        self.verified_count =
            pkg_verified_advance(self.verified_count, self.verified_count.saturating_add(1));
        Ok(self.verified_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bottle_verifier_accepts_pinned_digest_and_rejects_corrupt_archive() {
        let mut h = Sha256::new();
        h.update(b"bottle-tar-gz");
        let pin = h.finalize();
        let mut v = BottleArchiveVerifier::new();
        assert_eq!(v.verify_bottle(b"bottle-tar-gz", 13, &pin).unwrap(), 1);
        assert!(v.verify_bottle(b"bottle-tar-gx", 13, &pin).is_err());
    }
}
