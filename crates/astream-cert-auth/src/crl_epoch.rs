// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone-revision certificate-serial and principal revocation list (`CRL`) ledger
//! (`cap.expiry-enforced`, `Astream.CertAuth.TlaCrlEpoch`).

use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "crl_epoch_island.rs"]
mod crl_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn crl_entries_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn crl_revision_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use crl_epoch_island::{crl_entries_clamp, crl_revision_advance};

/// Maximum revoked certificate serials tracked in memory.
pub const MAX_CRL_SERIAL_ENTRIES: u64 = 4096;

contract_fn! {
    /// Verified revision monotonicity check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `crl_revoked_at_or_before_isl`.
    #[must_use]
    pub const fn crl_revoked_at_or_before(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Fail-closed, rollback-resistant CRL ledger (`SIGHUP` reload safe).
#[derive(Debug, Clone, Default)]
pub struct CertRevocationLedger {
    revision: u64,
    serials: BTreeSet<u64>,
    principals: BTreeSet<String>,
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

#[allow(clippy::question_mark)]
fn parse_u64_dec(s: &str) -> Option<u64> {
    if s.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in s.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = match acc.checked_mul(10) {
            Some(v) => v,
            None => return None,
        };
        acc = match acc.checked_add((b - b'0') as u64) {
            Some(v) => v,
            None => return None,
        };
    }
    Some(acc)
}

impl CertRevocationLedger {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            revision: 0,
            serials: BTreeSet::new(),
            principals: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.serials.len().saturating_add(self.principals.len())
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.serials.is_empty() && self.principals.is_empty()
    }

    /// Parses a multi-line CRL file (`rev=<u64>`, `serial=<u64>`, `principal=<token>`), refusing
    /// any file whose `rev=` is below `self.revision` (anti-rollback!) or that omits `rev=`.
    pub fn reload_from_text(&mut self, text: &str) -> Result<u64, &'static str> {
        let mut file_rev: Option<u64> = None;
        let mut new_serials = BTreeSet::new();
        let mut new_principals = BTreeSet::new();
        let max_s = crl_entries_clamp(MAX_CRL_SERIAL_ENTRIES, MAX_CRL_SERIAL_ENTRIES) as usize;

        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(r) = line.strip_prefix("rev=") {
                if file_rev.is_some() {
                    return Err("duplicate rev= header in CRL");
                }
                let parsed = match parse_u64_dec(r) {
                    Some(v) => v,
                    None => return Err("bad rev="),
                };
                file_rev = Some(parsed);
            } else if let Some(s) = line.strip_prefix("serial=") {
                let parsed = match parse_u64_dec(s) {
                    Some(v) => v,
                    None => return Err("bad serial="),
                };
                if !new_serials.contains(&parsed) && new_serials.len() >= max_s {
                    return Err("CRL serial entries exceed cap");
                }
                new_serials.insert(parsed);
            } else if let Some(p) = line.strip_prefix("principal=") {
                if p.is_empty() {
                    return Err("empty principal= in CRL");
                }
                if !new_principals.contains(p) && new_principals.len() >= max_s {
                    return Err("CRL principal entries exceed cap");
                }
                new_principals.insert(clone_str(p));
            } else {
                return Err("unknown CRL directive");
            }
        }
        let rev = match file_rev {
            Some(r) => r,
            None => return Err("missing rev= header in CRL"),
        };
        if !crl_revoked_at_or_before(rev, self.revision) {
            return Err("CRL rollback refused: file rev below active revision");
        }
        let mut merged_serials = self.serials.clone();
        for s in new_serials {
            if !merged_serials.contains(&s) && merged_serials.len() >= max_s {
                return Err("CRL serial entries exceed cap");
            }
            merged_serials.insert(s);
        }
        let mut merged_principals = self.principals.clone();
        for p in new_principals {
            if !merged_principals.contains(&p) && merged_principals.len() >= max_s {
                return Err("CRL principal entries exceed cap");
            }
            merged_principals.insert(p);
        }
        // Union with existing revocations so an accidental omission in same/next rev never un-revokes!
        self.serials = merged_serials;
        self.principals = merged_principals;
        self.revision = crl_revision_advance(self.revision, rev);
        Ok(self.revision)
    }

    #[must_use]
    pub fn is_revoked(&self, serial: u64, principal: &str) -> bool {
        self.serials.contains(&serial) || self.principals.contains(principal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crl_reload_enforces_monotone_revision_and_blocks_rollback() {
        let mut crl = CertRevocationLedger::new();
        crl.reload_from_text("# CRL v1\nrev=5\nserial=42\nprincipal=n-0123456789abcdef\n")
            .unwrap();
        assert!(crl.is_revoked(42, "h-ok"));
        assert!(crl.is_revoked(99, "n-0123456789abcdef"));
        assert!(!crl.is_revoked(99, "h-ok"));
        // Stale rev=4 file is refused!
        assert!(crl.reload_from_text("rev=4\nserial=100\n").is_err());
    }
}
