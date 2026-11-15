// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! TOFU session-ID (`sid`) -> `node_id` pin table & fail-closed ambiguity latch
//! (`docs/DESIGN-aterm-fabric.md` §8.1 T15 line 2201;
//! `Astream.Agent.TlaTofuSidPinAmbiguityGuard`).
//!
//! Prevents `sid` hijack mis-routing when a rogue node advertises a victim session's `sid`:
//! - First sight of `(sid, node_a)` records a TOFU pin at `sight_seq` within the `PINS_KEEP = 4_096`
//!   first-sight window,
//! - Any sight of `(sid, node_b)` with `node_b != node_a` while the pin is active latches `Ambiguous`,
//! - Once `Ambiguous` (or when an explicit `@s-<sid>@n-<target>` disagrees with `Pinned(node_a)`),
//!   routing fails closed (`RefusedAmbiguous`: `off=- reason=ambiguous`, never mis-routing to either
//!   claimant!) until `PINS_KEEP` newer first-sights evict the pin or the operator clears `<state>/pins`.

#[cfg(clean_islands)]
#[path = "tofu_sid_pin_ambiguity_guard_island.rs"]
mod tofu_sid_pin_ambiguity_guard_island;
#[cfg(clean_islands)]
pub use tofu_sid_pin_ambiguity_guard_island::{pins_keep_clamp_b134, sight_clock_advance_b134};

/// Bounded TOFU first-sight table capacity (`PINS_KEEP = 4_096`).
pub const PINS_KEEP: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Clamp active TOFU pin count to `pins_cap` (`PINS_KEEP`).
#[must_use]
pub const fn pins_keep_clamp_b134(cand_pins: u64, pins_cap: u64) -> u64 {
    if cand_pins < pins_cap {
        cand_pins
    } else {
        pins_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance first-sight sequence clock.
#[must_use]
pub const fn sight_clock_advance_b134(cur_sight: u64, cand_sight: u64) -> u64 {
    if cur_sight < cand_sight {
        cand_sight
    } else {
        cur_sight
    }
}

contract_fn! {
    /// True iff `!is_ambiguous && (explicit_node_matches_pin || !has_explicit_node)`.
    #[must_use]
    pub const fn tofu_route_unambiguous_b134(
        is_ambiguous: bool,
        has_explicit_node: bool,
        explicit_node_matches_pin: bool,
    ) -> bool
    clauses [ensures result == (!is_ambiguous && (explicit_node_matches_pin || !has_explicit_node))]
    {
        !is_ambiguous && (explicit_node_matches_pin || !has_explicit_node)
    }
}

/// Pin state for a tracked `sid`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SidPinStatus {
    /// Never seen or evicted after `PINS_KEEP` newer first-sights.
    Unpinned,
    /// Unambiguously pinned to `node_id` at `first_sight_seq`.
    Pinned { node_id: u64, first_sight_seq: u64 },
    /// Conflicting node advertised the same `sid` — latched fail-closed until evicted/reset!
    Ambiguous { first_sight_seq: u64 },
}

/// Routing decision for a bare `@s-<sid>` or explicit `@s-<sid>@n-<node>` post (§8.1 T15).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TofuRouteDecision {
    /// Safe to route to `target_node_id`.
    RouteToNode(u64),
    /// Fail closed: `off=- reason=ambiguous` (`ERR ambiguous` on `post --wait`, never mis-routed!).
    RefusedAmbiguous,
    /// Unknown `sid` with no explicit node and no presence sight yet.
    UnresolvedUnknownSid,
}

/// Sender-side TOFU `sid` pin guard for a tracked session id + global `PINS_KEEP` window clock.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TofuSidPinGuard {
    pins_cap: u64,
    active_pins: u64,
    sight_seq: u64,
    tracked_status: SidPinStatus,
}

impl TofuSidPinGuard {
    #[must_use]
    pub const fn new(pins_cap: u64) -> Self {
        let cap = if pins_cap == 0 { PINS_KEEP } else { pins_cap };
        Self {
            pins_cap: cap,
            active_pins: 0,
            sight_seq: 0,
            tracked_status: SidPinStatus::Unpinned,
        }
    }

    #[must_use]
    pub const fn active_pins(&self) -> u64 {
        pins_keep_clamp_b134(self.active_pins, self.pins_cap)
    }

    #[must_use]
    pub const fn status(&self) -> SidPinStatus {
        self.tracked_status
    }

    fn evict_if_aged_out(&mut self) {
        let first_seq = match self.tracked_status {
            SidPinStatus::Unpinned => return,
            SidPinStatus::Pinned {
                first_sight_seq, ..
            }
            | SidPinStatus::Ambiguous { first_sight_seq } => first_sight_seq,
        };
        if self.sight_seq.saturating_sub(first_seq) >= self.pins_cap {
            self.tracked_status = SidPinStatus::Unpinned;
        }
    }

    /// Observe presence advertisement `(tracked_sid, advertising_node_id)`.
    pub fn observe_tracked_sid(&mut self, advertising_node_id: u64) -> SidPinStatus {
        self.evict_if_aged_out();
        match self.tracked_status {
            SidPinStatus::Unpinned => {
                let next_seq =
                    sight_clock_advance_b134(self.sight_seq, self.sight_seq.saturating_add(1));
                self.sight_seq = next_seq;
                self.active_pins =
                    pins_keep_clamp_b134(self.active_pins.saturating_add(1), self.pins_cap);
                let st = SidPinStatus::Pinned {
                    node_id: advertising_node_id,
                    first_sight_seq: next_seq,
                };
                self.tracked_status = st;
                st
            }
            SidPinStatus::Pinned {
                node_id,
                first_sight_seq,
            } => {
                if node_id == advertising_node_id {
                    self.tracked_status
                } else {
                    let st = SidPinStatus::Ambiguous { first_sight_seq };
                    self.tracked_status = st;
                    st
                }
            }
            SidPinStatus::Ambiguous { .. } => self.tracked_status,
        }
    }

    /// Record `count` newer first-sights of OTHER distinct `sid`s (`PINS_KEEP` FIFO eviction).
    pub fn record_other_first_sights(&mut self, count: u64) {
        if count == 0 {
            return;
        }
        self.sight_seq =
            sight_clock_advance_b134(self.sight_seq, self.sight_seq.saturating_add(count));
        self.active_pins =
            pins_keep_clamp_b134(self.active_pins.saturating_add(count), self.pins_cap);
        self.evict_if_aged_out();
    }

    /// Operator deletion of `<state>/pins` resets all TOFU pins.
    pub fn reset_pins_file(&mut self) {
        self.active_pins = 0;
        self.tracked_status = SidPinStatus::Unpinned;
    }

    /// Resolve routing for bare `@s-<sid>` (`None`) or explicit `@s-<sid>@n-<node>` (`Some(node)`).
    pub fn resolve_route(&mut self, explicit_node: Option<u64>) -> TofuRouteDecision {
        self.evict_if_aged_out();
        match self.tracked_status {
            SidPinStatus::Unpinned => match explicit_node {
                Some(n) => TofuRouteDecision::RouteToNode(n),
                None => TofuRouteDecision::UnresolvedUnknownSid,
            },
            SidPinStatus::Pinned { node_id, .. } => {
                let (has_exp, matches) = match explicit_node {
                    Some(exp) => (true, exp == node_id),
                    None => (false, false),
                };
                if tofu_route_unambiguous_b134(false, has_exp, matches) {
                    TofuRouteDecision::RouteToNode(node_id)
                } else {
                    // §8.1 T15: even explicit `@s-<sid>@n-<real>` is refused if pinned to another node!
                    TofuRouteDecision::RefusedAmbiguous
                }
            }
            SidPinStatus::Ambiguous { .. } => {
                let _ = tofu_route_unambiguous_b134(true, explicit_node.is_some(), false);
                TofuRouteDecision::RefusedAmbiguous
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rogue_claimant_latches_ambiguous_until_pins_keep_evicts_or_reset() {
        let mut g = TofuSidPinGuard::new(4);
        assert!(matches!(
            g.observe_tracked_sid(10),
            SidPinStatus::Pinned { node_id: 10, .. }
        ));
        assert_eq!(g.resolve_route(None), TofuRouteDecision::RouteToNode(10));
        // Explicit route to a DIFFERENT node while pinned to 10 refuses `RefusedAmbiguous` (§8.1 T15)!
        assert_eq!(
            g.resolve_route(Some(20)),
            TofuRouteDecision::RefusedAmbiguous
        );
        // Rogue node 20 advertises the same sid -> latches `Ambiguous`!
        assert!(matches!(
            g.observe_tracked_sid(20),
            SidPinStatus::Ambiguous { .. }
        ));
        // Both bare and explicit routes fail closed:
        assert_eq!(g.resolve_route(None), TofuRouteDecision::RefusedAmbiguous);
        assert_eq!(
            g.resolve_route(Some(10)),
            TofuRouteDecision::RefusedAmbiguous
        );
        assert_eq!(
            g.resolve_route(Some(20)),
            TofuRouteDecision::RefusedAmbiguous
        );
        // 4 newer first-sights (`PINS_KEEP = 4`) evict the stale conflict, allowing fresh TOFU pin:
        g.record_other_first_sights(4);
        assert_eq!(g.status(), SidPinStatus::Unpinned);
        assert!(matches!(
            g.observe_tracked_sid(10),
            SidPinStatus::Pinned { node_id: 10, .. }
        ));
        assert_eq!(
            g.resolve_route(Some(10)),
            TofuRouteDecision::RouteToNode(10)
        );
    }
}
