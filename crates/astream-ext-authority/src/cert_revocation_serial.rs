// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotonic CRL / KRL revoked-certificate serial set (`Astream.ExtAuth.TlaCertRevocationSerial`)
//! rejecting downgraded revocation lists and revoked serials in O(log N) binary search.

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

#[cfg(clean_islands)]
#[path = "cert_revocation_serial_island.rs"]
mod cert_revocation_serial_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_rev_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_crl_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cert_revocation_serial_island::{ext_crl_advance, ext_rev_clamp};

/// Maximum revoked serials per KRL snapshot (`65_536`).
pub const MAX_REVOKED_SERIALS: u64 = 65_536;

contract_fn! {
    /// Verified fresh CRL sequence (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_not_revoked_isl`.
    #[must_use]
    pub const fn ext_not_revoked(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct CertRevocationSet {
    revoked_serials: BTreeMap<u64, ()>,
    crl_number: u64,
}

impl CertRevocationSet {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            revoked_serials: BTreeMap::new(),
            crl_number: 0,
        }
    }

    pub fn install_krl(&mut self, crl_number: u64, serials: &[u64]) -> bool {
        if (serials.len() as u64) > MAX_REVOKED_SERIALS {
            return false;
        }
        let Some(min_crl) = self.crl_number.checked_add(1) else {
            return false;
        };
        if !ext_not_revoked(crl_number, min_crl) {
            return false;
        }
        let _ = ext_rev_clamp(serials.len() as u64, MAX_REVOKED_SERIALS);
        let mut next = BTreeMap::new();
        for &serial in serials {
            next.insert(serial, ());
        }
        self.revoked_serials = next;
        self.crl_number = ext_crl_advance(self.crl_number, crl_number);
        true
    }

    #[must_use]
    pub fn is_allowed(&self, serial: u64) -> bool {
        !self.revoked_serials.contains_key(&serial)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_crl_rollback_and_blocks_revoked_serials() {
        let mut s = CertRevocationSet::new();
        assert!(s.install_krl(10, &[42, 7, 19]));
        assert!(!s.install_krl(9, &[7]));
        assert!(!s.is_allowed(19));
        assert!(s.is_allowed(20));
    }
}
