// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-region dynamic federation peer discovery & loop-free RTT route selector
//! (federation across brokers;
//! `Astream.Broker.TlaPeerDiscoveryRegionRouter`).
//!
//! Extends declarative `FederationBridge` with dynamic peer gossip membership and bounded-hop
//! multi-region route selection:
//! - Enforces a strict federation hop ceiling (`hop_count <= max_hops`) so regional relays can
//!   never form unbounded forwarding loops,
//! - Selects the lowest-RTT live peer whose heartbeat age is within `max_peer_age_ms` and whose
//!   `peer_id != local_broker_id`,
//! - Advances cluster discovery `config_epoch` monotonically on membership announcements.

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
#[path = "peer_discovery_region_router_island.rs"]
mod peer_discovery_region_router_island;
#[cfg(clean_islands)]
pub use peer_discovery_region_router_island::{
    region_config_epoch_advance_b127, region_hop_clamp_b127,
};

#[cfg(not(clean_islands))]
/// Clamp a federated forwarding hop count to `max_hops`.
#[must_use]
pub const fn region_hop_clamp_b127(cand_hops: u64, max_hops: u64) -> u64 {
    if cand_hops < max_hops {
        cand_hops
    } else {
        max_hops
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the dynamic peer-discovery membership `config_epoch`.
#[must_use]
pub const fn region_config_epoch_advance_b127(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `next_hops <= max_hops && peer_id != local_broker_id` (loop-free & hop-bounded).
    #[must_use]
    pub const fn region_route_loop_free_b127(
        next_hops: u64,
        max_hops: u64,
        peer_id: u64,
        local_broker_id: u64,
    ) -> bool
    clauses [ensures result == (next_hops <= max_hops && peer_id != local_broker_id)]
    {
        next_hops <= max_hops && peer_id != local_broker_id
    }
}

pub const MAX_DISCOVERED_PEERS: usize = 8;

/// Dynamic peer record learned from regional federation gossip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiscoveredRegionPeer {
    pub peer_id: u64,
    pub region_tag: u32,
    pub rtt_ms: u64,
    pub last_seen_ms: u64,
}

/// Route selection outcome for a cross-region federation forward.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionRouteDecision {
    SelectedPeer {
        peer_id: u64,
        rtt_ms: u64,
        next_hops: u64,
        config_epoch: u64,
    },
    RefusedHopCeilingReached {
        current_hops: u64,
        max_hops: u64,
    },
    NoHealthyPeerForRegion {
        target_region: u32,
    },
}

/// Bounded dynamic peer-discovery table & lowest-RTT region router.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PeerDiscoveryRegionRouter {
    local_broker_id: u64,
    max_hops: u64,
    max_peer_age_ms: u64,
    config_epoch: u64,
    peers: [Option<DiscoveredRegionPeer>; MAX_DISCOVERED_PEERS],
}

impl PeerDiscoveryRegionRouter {
    #[must_use]
    pub const fn new(local_broker_id: u64, max_hops: u64, max_peer_age_ms: u64) -> Self {
        Self {
            local_broker_id,
            max_hops,
            max_peer_age_ms,
            config_epoch: 0,
            peers: [None; MAX_DISCOVERED_PEERS],
        }
    }

    #[must_use]
    pub const fn config_epoch(&self) -> u64 {
        self.config_epoch
    }

    /// Upsert a discovered peer announcement and advance `config_epoch` monotonically.
    pub fn upsert_peer(&mut self, announced_epoch: u64, peer: DiscoveredRegionPeer) -> bool {
        if peer.peer_id == 0 || peer.peer_id == self.local_broker_id {
            return false;
        }
        self.config_epoch = region_config_epoch_advance_b127(self.config_epoch, announced_epoch);
        let mut empty_slot: Option<usize> = None;
        let mut idx = 0usize;
        while idx < MAX_DISCOVERED_PEERS {
            match self.peers.get_mut(idx) {
                Some(slot_ref @ Some(_)) => {
                    if let Some(existing) = *slot_ref {
                        if existing.peer_id == peer.peer_id {
                            *slot_ref = Some(peer);
                            return true;
                        }
                    }
                }
                Some(None) if empty_slot.is_none() => {
                    empty_slot = Some(idx);
                }
                _ => {}
            }
            idx = idx.saturating_add(1);
        }
        if let Some(slot) = empty_slot {
            if let Some(dst) = self.peers.get_mut(slot) {
                *dst = Some(peer);
                return true;
            }
        }
        false
    }

    /// Select the lowest-RTT live peer in `target_region` at `now_ms` for a frame with `current_hops`.
    #[must_use]
    pub fn select_route(
        &self,
        target_region: u32,
        current_hops: u64,
        now_ms: u64,
    ) -> RegionRouteDecision {
        let next_hops = current_hops.saturating_add(1);
        if next_hops > self.max_hops {
            return RegionRouteDecision::RefusedHopCeilingReached {
                current_hops,
                max_hops: self.max_hops,
            };
        }
        let clamped_hops = region_hop_clamp_b127(next_hops, self.max_hops);
        let mut best: Option<DiscoveredRegionPeer> = None;
        let mut idx = 0usize;
        while idx < MAX_DISCOVERED_PEERS {
            if let Some(&Some(p)) = self.peers.get(idx) {
                let age = now_ms.saturating_sub(p.last_seen_ms);
                if p.region_tag == target_region
                    && age <= self.max_peer_age_ms
                    && region_route_loop_free_b127(
                        clamped_hops,
                        self.max_hops,
                        p.peer_id,
                        self.local_broker_id,
                    )
                {
                    let take = match best {
                        None => true,
                        Some(cur) => {
                            p.rtt_ms < cur.rtt_ms
                                || (p.rtt_ms == cur.rtt_ms && p.peer_id < cur.peer_id)
                        }
                    };
                    if take {
                        best = Some(p);
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        match best {
            Some(chosen) => RegionRouteDecision::SelectedPeer {
                peer_id: chosen.peer_id,
                rtt_ms: chosen.rtt_ms,
                next_hops: clamped_hops,
                config_epoch: self.config_epoch,
            },
            None => RegionRouteDecision::NoHealthyPeerForRegion { target_region },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn picks_lowest_rtt_live_peer_skips_stale_or_self_and_enforces_hop_ceiling() {
        let mut router = PeerDiscoveryRegionRouter::new(100, 3, 5_000);

        // Self-loop announcement ignored.
        assert!(!router.upsert_peer(
            1,
            DiscoveredRegionPeer {
                peer_id: 100,
                region_tag: 7,
                rtt_ms: 1,
                last_seen_ms: 10_000,
            }
        ));

        assert!(router.upsert_peer(
            2,
            DiscoveredRegionPeer {
                peer_id: 201,
                region_tag: 7,
                rtt_ms: 48,
                last_seen_ms: 9_000,
            }
        ));
        assert!(router.upsert_peer(
            3,
            DiscoveredRegionPeer {
                peer_id: 202,
                region_tag: 7,
                rtt_ms: 14,
                last_seen_ms: 9_500,
            }
        ));
        // Stale peer (last_seen_ms = 1_000, age = 9_000 > 5_000) with lower RTT 4ms must be skipped!
        assert!(router.upsert_peer(
            4,
            DiscoveredRegionPeer {
                peer_id: 203,
                region_tag: 7,
                rtt_ms: 4,
                last_seen_ms: 1_000,
            }
        ));

        assert_eq!(
            router.select_route(7, 1, 10_000),
            RegionRouteDecision::SelectedPeer {
                peer_id: 202,
                rtt_ms: 14,
                next_hops: 2,
                config_epoch: 4,
            }
        );

        // Hop ceiling 3 reached -> refused loop-safe!
        assert_eq!(
            router.select_route(7, 3, 10_000),
            RegionRouteDecision::RefusedHopCeilingReached {
                current_hops: 3,
                max_hops: 3,
            }
        );
    }
}
