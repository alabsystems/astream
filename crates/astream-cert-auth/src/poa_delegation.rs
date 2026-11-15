// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Short-lived Proof-of-Authority (`PoA`) offline Macaroon capability attenuation ceiling
//! (`ROADMAP.md` lines 12-14, `Astream.CertAuth.TlaPoaDelegation`).

use astream_cap::{attenuate_offline, can_attenuate, Capability, Grant};

#[cfg(clean_islands)]
#[path = "poa_delegation_island.rs"]
mod poa_delegation_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn poa_ttl_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn poa_chain_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use poa_delegation_island::{poa_chain_advance, poa_ttl_clamp};

/// Maximum TTL (`1` hour in ms) permitted on an attenuated sub-agent PoA capability.
pub const MAX_POA_TTL_MS: u64 = 3_600_000;

contract_fn! {
    /// Verified ceiling predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `poa_within_ceiling_isl`.
    #[must_use]
    pub const fn poa_within_ceiling(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Offline PoA sub-session capability minter with mandatory short-lived expiry ceiling.
#[derive(Debug, Clone)]
pub struct PoaDelegationChain {
    max_ttl_ms: u64,
    minted_count: u64,
}

impl Default for PoaDelegationChain {
    fn default() -> Self {
        Self::new()
    }
}

fn push_u64_dec(out: &mut String, mut val: u64) {
    if val == 0 {
        out.push('0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while val > 0 && len < digits.len() {
        let rem = (val % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add(rem);
        }
        len = len.saturating_add(1);
        val /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&b) = digits.get(len) {
            out.push(b as char);
        }
    }
}

impl PoaDelegationChain {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_ttl_ms: MAX_POA_TTL_MS,
            minted_count: 0,
        }
    }

    #[must_use]
    pub const fn minted_count(&self) -> u64 {
        self.minted_count
    }

    /// Offline-attenuates `parent_cap` (no broker mint secret needed!) into a narrower child
    /// grant expiring at `now_ms + clamp(req_ttl_ms, max_ttl_ms)`.
    pub fn delegate_poa(
        &mut self,
        parent_cap: &Capability,
        mode_ro_only: bool,
        principal: &str,
        narrow_filter: &str,
        now_ms: u64,
        req_ttl_ms: u64,
    ) -> Result<Capability, &'static str> {
        let parent_grant = match Grant::parse(&parent_cap.filter) {
            Ok(g) => g,
            Err(_) => return Err("bad parent grant"),
        };
        let clamped_ttl = poa_ttl_clamp(req_ttl_ms, self.max_ttl_ms);
        if clamped_ttl == 0 {
            return Err("zero PoA ttl");
        }
        let mut exp_ms = match now_ms.checked_add(clamped_ttl) {
            Some(v) => v,
            None => return Err("PoA expiry timestamp overflow"),
        };
        if let Some(p_exp) = parent_grant.expires_at {
            let min_parent_exp = match now_ms.checked_add(1) {
                Some(v) => v,
                None => return Err("parent capability already expired"),
            };
            if !poa_within_ceiling(p_exp, min_parent_exp) {
                return Err("parent capability already expired");
            }
            if exp_ms > p_exp {
                exp_ms = p_exp;
            }
        }
        let mode = if mode_ro_only { "ro" } else { "rw" };
        let mut child_spec = String::new();
        child_spec.push_str(mode);
        child_spec.push_str(",p=");
        child_spec.push_str(principal);
        child_spec.push_str(",exp=");
        push_u64_dec(&mut child_spec, exp_ms);
        child_spec.push(':');
        child_spec.push_str(narrow_filter);
        if Grant::parse(&child_spec).is_err() {
            return Err("invalid child PoA grant");
        }
        if can_attenuate(&parent_cap.filter, &child_spec).is_err() {
            return Err("PoA child grant escalates parent authority");
        }
        let child_cap = match attenuate_offline(parent_cap, &child_spec, now_ms) {
            Ok(c) => c,
            Err(_) => return Err("offline Macaroon attenuation refused"),
        };
        let next_count = match self.minted_count.checked_add(1) {
            Some(n) => n,
            None => return Err("PoA delegation counter overflow"),
        };
        self.minted_count = poa_chain_advance(self.minted_count, next_count);
        Ok(child_cap)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_cap::{mint, verify};

    #[test]
    fn offline_poa_delegation_clamps_ttl_narrows_scope_and_verifies_under_broker_secret() {
        let secret = b"0123456789abcdef0123456789abcdef";
        let parent = mint(secret, "rw,p=h-alice:/f/alpha/>").unwrap();
        let mut poa = PoaDelegationChain::new();

        let child = poa
            .delegate_poa(
                &parent,
                true,
                "h-alice",
                "/f/alpha/pub/n1/>",
                10_000,
                99_999_999,
            )
            .unwrap();
        assert!(verify(secret, &child));
        let cg = Grant::parse(&child.filter).unwrap();
        assert_eq!(cg.expires_at, Some(10_000 + MAX_POA_TTL_MS));

        // Attempting to change bound principal h-alice -> h-bob fails closed!
        assert!(poa
            .delegate_poa(&parent, true, "h-bob", "/f/alpha/pub/n1/>", 10_000, 5_000)
            .is_err());
    }
}
