// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Strict tunnel ALPN protocol negotiator (`astream/1`, `astream-fed/1`) refusing protocol
//! downgrade or unrecognized wire offerings (`Astream.Tunnel.TlaAlpnProtoSelect`).
#![allow(clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "alpn_proto_select_island.rs"]
mod alpn_proto_select_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_protos_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_neg_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use alpn_proto_select_island::{tun_neg_advance, tun_protos_clamp};

/// Maximum ALPN protocol tokens inspected per client hello (`16`).
pub const MAX_ALPN_OFFERS: u64 = 16;

contract_fn! {
    /// Verified minimum protocol version (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tun_version_supported_isl`.
    #[must_use]
    pub const fn tun_version_supported(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Selects the highest mutually supported `astream/<ver>` ALPN token at or above `min_version`.
#[derive(Debug, Clone)]
pub struct AlpnNegotiator {
    min_version: u64,
    negotiations: u64,
}

fn parse_ascii_u64(s: &str) -> Option<u64> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    let mut idx = 0usize;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if !b.is_ascii_digit() {
            return None;
        }
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(u64::from(b.saturating_sub(b'0'))) else {
            return None;
        };
        acc = next;
        idx = idx.saturating_add(1);
    }
    Some(acc)
}

impl AlpnNegotiator {
    #[must_use]
    pub const fn new(min_version: u64) -> Self {
        Self {
            min_version,
            negotiations: 0,
        }
    }

    pub fn select<'a>(&mut self, client_offers: &[&'a str]) -> Result<&'a str, &'static str> {
        self.negotiations = tun_neg_advance(self.negotiations, self.negotiations.saturating_add(1));
        if (client_offers.len() as u64) > MAX_ALPN_OFFERS {
            return Err("ALPN offer count exceeds ceiling");
        }
        let lim = tun_protos_clamp(client_offers.len() as u64, MAX_ALPN_OFFERS) as usize;
        let mut best: Option<(u64, &'a str)> = None;
        let mut idx = 0usize;
        while idx < lim {
            if let Some(&offer) = client_offers.get(idx) {
                if let Some(ver_s) = offer.strip_prefix("astream/") {
                    if let Some(ver) = parse_ascii_u64(ver_s) {
                        let better = match best {
                            Some((b_ver, _)) => ver > b_ver,
                            None => true,
                        };
                        if tun_version_supported(ver, self.min_version) && better {
                            best = Some((ver, offer));
                        }
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        match best {
            Some((_, tok)) => Ok(tok),
            None => Err("ALPN mismatch: no supported astream/<version> offered"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alpn_negotiator_picks_highest_supported_version_and_refuses_downgrade() {
        let mut n = AlpnNegotiator::new(1);
        assert_eq!(
            n.select(&["http/1.1", "astream/1", "astream/2"]).unwrap(),
            "astream/2"
        );
        assert!(n.select(&["astream/0", "http/1.1"]).is_err());
    }
}
