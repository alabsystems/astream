// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Short-lived HMAC-SHA256 NAT-traversal relay admission ticket binding `(fleet_id, node_id,
//! expires_at_ms)` (`Astream.Tunnel.TlaDerpRelayTicket`).

use astream_digest::{ct_eq, hmac_sha256_parts};

#[cfg(clean_islands)]
#[path = "derp_relay_ticket_island.rs"]
mod derp_relay_ticket_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_ttl_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_mint_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use derp_relay_ticket_island::{tun_mint_advance, tun_ttl_clamp};

/// Maximum relay ticket lifetime (`300_000` ms == 5 minutes).
pub const MAX_RELAY_TICKET_TTL_MS: u64 = 300_000;

contract_fn! {
    /// Verified ticket freshness (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tun_ticket_live_isl`.
    #[must_use]
    pub const fn tun_ticket_live(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatRelayTicket {
    pub fleet_id: String,
    pub node_id: String,
    pub expires_at_ms: u64,
    pub serial: u64,
    pub mac: [u8; 32],
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

#[inline(never)]
fn relay_mac(secret: &[u8; 32], fleet: &str, node: &str, exp_ms: u64, serial: u64) -> [u8; 32] {
    let fleet_len = (fleet.len() as u64).to_le_bytes();
    let node_len = (node.len() as u64).to_le_bytes();
    let exp_le = exp_ms.to_le_bytes();
    let ser_le = serial.to_le_bytes();
    hmac_sha256_parts(
        secret,
        &[
            b"ASTREAM-RELAY-TICKET-V1\0",
            &fleet_len,
            fleet.as_bytes(),
            &node_len,
            node.as_bytes(),
            &exp_le,
            &ser_le,
        ],
    )
}

/// Mints and verifies stateless HMAC-SHA256 relay admission tickets.
#[derive(Debug, Clone)]
pub struct RelayTicketAuthority {
    secret: [u8; 32],
    serial: u64,
}

impl RelayTicketAuthority {
    #[must_use]
    pub const fn new(secret: [u8; 32]) -> Self {
        Self { secret, serial: 0 }
    }

    pub fn mint(&mut self, fleet: &str, node: &str, now_ms: u64, ttl_ms: u64) -> NatRelayTicket {
        let clamped_ttl = tun_ttl_clamp(ttl_ms, MAX_RELAY_TICKET_TTL_MS);
        let exp = now_ms.saturating_add(clamped_ttl);
        self.serial = tun_mint_advance(self.serial, self.serial.saturating_add(1));
        let mac = relay_mac(&self.secret, fleet, node, exp, self.serial);
        NatRelayTicket {
            fleet_id: copy_str(fleet),
            node_id: copy_str(node),
            expires_at_ms: exp,
            serial: self.serial,
            mac,
        }
    }

    #[must_use]
    pub fn verify(&self, ticket: &NatRelayTicket, now_ms: u64) -> bool {
        if ticket.fleet_id.is_empty()
            || ticket.node_id.is_empty()
            || ct_eq(&self.secret, &[0u8; 32])
            || !tun_ticket_live(ticket.expires_at_ms, now_ms)
        {
            return false;
        }
        let calc = relay_mac(
            &self.secret,
            &ticket.fleet_id,
            &ticket.node_id,
            ticket.expires_at_ms,
            ticket.serial,
        );
        ct_eq(&calc, &ticket.mac)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relay_authority_accepts_live_authentic_ticket_and_rejects_expired_or_forged() {
        let mut auth = RelayTicketAuthority::new([0x5Au8; 32]);
        let mut t = auth.mint("prod", "n-west-1", 10_000, 60_000);
        assert!(auth.verify(&t, 40_000));
        assert!(!auth.verify(&t, 70_001));
        t.node_id = "n-east-9".to_owned();
        assert!(!auth.verify(&t, 40_000));
    }
}
