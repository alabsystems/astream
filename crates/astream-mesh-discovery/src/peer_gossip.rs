// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SWIM-style incarnation peer membership protocol and suspect-to-dead promotion
//! (`Astream.Mesh.TlaPeerGossip`).
//!
//! Resolves concurrent gossip updates deterministically without synchronized wall clocks:
//! - Higher `incarnation` strictly wins (`gossip_inc_advance`).
//! - At equal `incarnation`, severity orders `Alive(0) < Suspect(1) < Dead(2)`, so a peer
//!   refutes a false suspicion by incrementing its own `incarnation` and broadcasting `Alive`.
//! - Suspect peers not refuted within `suspect_timeout_ms` promote to `Dead`.

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "peer_gossip_island.rs"]
mod peer_gossip_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gossip_peers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gossip_inc_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use peer_gossip_island::{gossip_inc_advance, gossip_peers_clamp};

/// Maximum peers tracked in one regional gossip table.
pub const MAX_GOSSIP_PEERS: u64 = 256;

contract_fn! {
    /// Verified liveness check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gossip_peer_alive_isl`.
    #[must_use]
    pub const fn gossip_peer_alive(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// SWIM peer health state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SwimHealth {
    Alive,
    Suspect { since_mono_ms: u64 },
    Dead,
}

impl SwimHealth {
    #[must_use]
    const fn severity_rank(self) -> u64 {
        match self {
            Self::Alive => 0,
            Self::Suspect { .. } => 1,
            Self::Dead => 2,
        }
    }
}

/// Membership row for a discovered mesh peer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GossipPeerEntry {
    pub node_id: String,
    pub endpoint: String,
    pub incarnation: u64,
    pub health: SwimHealth,
}

/// Deterministic SWIM gossip table.
#[derive(Debug, Clone)]
pub struct PeerGossipTable {
    max_peers: u64,
    suspect_timeout_ms: u64,
    highest_inc: u64,
    peers: BTreeMap<String, GossipPeerEntry>,
}

impl Default for PeerGossipTable {
    fn default() -> Self {
        Self::new()
    }
}

impl PeerGossipTable {
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(MAX_GOSSIP_PEERS, 5_000)
    }

    #[must_use]
    pub fn with_config(max_peers: u64, suspect_timeout_ms: u64) -> Self {
        let cap = gossip_peers_clamp(max_peers, MAX_GOSSIP_PEERS);
        Self {
            max_peers: if cap == 0 { 1 } else { cap },
            suspect_timeout_ms,
            highest_inc: 0,
            peers: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.peers.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.peers.is_empty()
    }

    /// Applies an incoming gossip rumor; returns `true` iff the rumor superseded local state.
    pub fn merge_rumor(&mut self, incoming: GossipPeerEntry) -> bool {
        if incoming.node_id.is_empty() || incoming.endpoint.is_empty() {
            return false;
        }
        if let Some(cur) = self.peers.get(&incoming.node_id) {
            if incoming.incarnation < cur.incarnation {
                return false;
            }
            if incoming.incarnation == cur.incarnation
                && incoming.health.severity_rank() <= cur.health.severity_rank()
            {
                return false;
            }
        } else if (self.peers.len() as u64) >= self.max_peers {
            return false;
        }
        self.highest_inc = gossip_inc_advance(self.highest_inc, incoming.incarnation);
        self.peers.insert(incoming.node_id.clone(), incoming);
        true
    }

    /// Promotes `Suspect` peers whose suspicion age `>= suspect_timeout_ms` to `Dead`.
    pub fn reap_expired_suspects(&mut self, now_mono_ms: u64) -> usize {
        let mut promoted = 0usize;
        let timeout = self.suspect_timeout_ms;
        for entry in self.peers.values_mut() {
            if let SwimHealth::Suspect { since_mono_ms } = entry.health {
                let deadline = since_mono_ms.saturating_add(timeout);
                if gossip_peer_alive(now_mono_ms, deadline) {
                    entry.health = SwimHealth::Dead;
                    promoted = promoted.saturating_add(1);
                }
            }
        }
        promoted
    }

    /// Returns sorted endpoints of all currently `Alive` peers.
    #[must_use]
    pub fn alive_endpoints(&self) -> Vec<String> {
        let mut out = Vec::new();
        for p in self.peers.values() {
            if matches!(p.health, SwimHealth::Alive) {
                out.push(p.endpoint.clone());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn swim_gossip_honors_incarnation_refutation_and_suspect_timeout_promotion() {
        let mut tbl = PeerGossipTable::with_config(16, 1_000);
        assert!(tbl.merge_rumor(GossipPeerEntry {
            node_id: "n-east-1".to_owned(),
            endpoint: "10.0.1.5:7000".to_owned(),
            incarnation: 1,
            health: SwimHealth::Alive,
        }));
        // Same incarnation Suspect supersedes Alive.
        assert!(tbl.merge_rumor(GossipPeerEntry {
            node_id: "n-east-1".to_owned(),
            endpoint: "10.0.1.5:7000".to_owned(),
            incarnation: 1,
            health: SwimHealth::Suspect { since_mono_ms: 500 },
        }));
        assert!(tbl.alive_endpoints().is_empty());

        // Same incarnation Alive CANNOT refute Suspect; incarnation 2 Alive DOES refute!
        assert!(!tbl.merge_rumor(GossipPeerEntry {
            node_id: "n-east-1".to_owned(),
            endpoint: "10.0.1.5:7000".to_owned(),
            incarnation: 1,
            health: SwimHealth::Alive,
        }));
        assert!(tbl.merge_rumor(GossipPeerEntry {
            node_id: "n-east-1".to_owned(),
            endpoint: "10.0.1.5:7000".to_owned(),
            incarnation: 2,
            health: SwimHealth::Alive,
        }));
        assert_eq!(tbl.alive_endpoints(), vec!["10.0.1.5:7000".to_owned()]);

        // Suspect past timeout promotes to Dead.
        assert!(tbl.merge_rumor(GossipPeerEntry {
            node_id: "n-east-1".to_owned(),
            endpoint: "10.0.1.5:7000".to_owned(),
            incarnation: 2,
            health: SwimHealth::Suspect {
                since_mono_ms: 2_000
            },
        }));
        assert_eq!(tbl.reap_expired_suspects(2_999), 0);
        assert_eq!(tbl.reap_expired_suspects(3_000), 1);
    }
}
