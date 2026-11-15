// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bridge barrier auto-answer (`busy`/`absent`) & retained `ack` face router
//! (`docs/DESIGN-aterm-fabric.md` §5.3, §5.4, §15; `Astream.Broker.TlaBridgeBarrierAutoAckRouter`).
//!
//! Resolves the two §5.4 / §15 **DESIGNED** rows while preserving §5.3's subject-budget safety:
//! 1. Routes a session's `post kind=ack re=<B>` onto the retained `pub/<owner>/ack/<B>` face when
//!    the producer's distinct-subject budget has headroom below `per_barrier_subject_cap`, and
//!    automatically falls back to the single retained `pub/<node>/node/ack` (`re=<B>`) face once
//!    at or above `per_barrier_subject_cap` so barriers can never exhaust `MAX_SUBJECTS_PER_PRODUCER`.
//! 2. Synthesizes bridge `busy` / `absent` / `held` / `ready` auto-answers for fleet `barrier`
//!    records only while the bridge's `Scope::Bridge` verb lane is live (`verb_lane_live == true`),
//!    and rejects any `ack` whose offset would precede the barrier offset `B` (§4.2).

#[cfg(clean_islands)]
#[path = "bridge_barrier_auto_ack_router_island.rs"]
mod bridge_barrier_auto_ack_router_island;
#[cfg(clean_islands)]
pub use bridge_barrier_auto_ack_router_island::{
    barrier_ack_offset_advance_b124, barrier_subject_spend_clamp_b124,
};

#[cfg(not(clean_islands))]
/// Clamp distinct subjects spent on per-barrier `ack/<B>` faces to `subject_cap`.
#[must_use]
pub const fn barrier_subject_spend_clamp_b124(cand_spent: u64, subject_cap: u64) -> u64 {
    if cand_spent < subject_cap {
        cand_spent
    } else {
        subject_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance highest answered barrier offset.
#[must_use]
pub const fn barrier_ack_offset_advance_b124(cur_barrier: u64, cand_barrier: u64) -> u64 {
    if cur_barrier < cand_barrier {
        cand_barrier
    } else {
        cur_barrier
    }
}

contract_fn! {
    /// True iff `ack_offset >= barrier_offset` (§4.2: readers ignore an `ack/<B>` whose own offset is `< B`).
    #[must_use]
    pub const fn barrier_ack_causal_valid_b124(barrier_offset: u64, ack_offset: u64) -> bool
    clauses [ensures result == (barrier_offset <= ack_offset)]
    {
        barrier_offset <= ack_offset
    }
}

/// Member state reported on a retained barrier ack row (§4.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierAckState {
    Ready,
    Busy,
    Refused,
    Absent,
    Held,
}

/// Retained destination face chosen by the router.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierAckFace {
    /// Per-(member, barrier) retained face `/f/<F>/pub/<owner>/ack/<B>` (§5.4).
    PerBarrierOwnerFace { barrier_offset: u64 },
    /// Budget-preserving single retained node face `/f/<F>/pub/<node>/node/ack` with `re=<B>` (§5.3).
    SharedNodeAckFace { re_barrier_offset: u64 },
}

/// Routing outcome for a session `post kind=ack re=<B>` or a fleet `barrier` auto-answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierRouteDecision {
    Routed {
        face: BarrierAckFace,
        state: BarrierAckState,
        spent_subjects: u64,
    },
    RefusedVerbLaneLost,
    RefusedAckPredatesBarrier {
        barrier_offset: u64,
        candidate_offset: u64,
    },
}

/// Stateful bridge barrier auto-ack & retained-face router.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BridgeBarrierAutoAckRouter {
    verb_lane_live: bool,
    spent_subjects: u64,
    per_barrier_subject_cap: u64,
    highest_barrier_offset: u64,
}

impl BridgeBarrierAutoAckRouter {
    #[must_use]
    pub const fn new(per_barrier_subject_cap: u64) -> Self {
        Self {
            verb_lane_live: true,
            spent_subjects: 0,
            per_barrier_subject_cap,
            highest_barrier_offset: 0,
        }
    }

    pub fn set_verb_lane_live(&mut self, live: bool) {
        self.verb_lane_live = live;
    }

    #[must_use]
    pub const fn spent_subjects(&self) -> u64 {
        self.spent_subjects
    }

    #[must_use]
    pub const fn highest_barrier_offset(&self) -> u64 {
        self.highest_barrier_offset
    }

    /// Route either an explicit session barrier ack or a bridge auto-synthesized `busy`/`absent` ack.
    pub fn route_barrier_ack(
        &mut self,
        barrier_offset: u64,
        candidate_write_offset: u64,
        state: BarrierAckState,
    ) -> BarrierRouteDecision {
        if !self.verb_lane_live {
            return BarrierRouteDecision::RefusedVerbLaneLost;
        }
        if !barrier_ack_causal_valid_b124(barrier_offset, candidate_write_offset) {
            return BarrierRouteDecision::RefusedAckPredatesBarrier {
                barrier_offset,
                candidate_offset: candidate_write_offset,
            };
        }
        self.highest_barrier_offset =
            barrier_ack_offset_advance_b124(self.highest_barrier_offset, barrier_offset);
        let face = if self.spent_subjects < self.per_barrier_subject_cap {
            self.spent_subjects = barrier_subject_spend_clamp_b124(
                self.spent_subjects.saturating_add(1),
                self.per_barrier_subject_cap,
            );
            BarrierAckFace::PerBarrierOwnerFace { barrier_offset }
        } else {
            BarrierAckFace::SharedNodeAckFace {
                re_barrier_offset: barrier_offset,
            }
        };
        BarrierRouteDecision::Routed {
            face,
            state,
            spent_subjects: self.spent_subjects,
        }
    }

    /// Reclaim one per-barrier `ack/<B>` subject after conditional `Client::retire` succeeds.
    pub fn on_barrier_ack_retired(&mut self) {
        self.spent_subjects = self.spent_subjects.saturating_sub(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn routes_per_barrier_until_budget_cap_then_falls_back_and_suppresses_when_verb_lane_lost() {
        let mut router = BridgeBarrierAutoAckRouter::new(2);

        // Causal check: ack offset < barrier offset is rejected.
        assert_eq!(
            router.route_barrier_ack(50, 49, BarrierAckState::Ready),
            BarrierRouteDecision::RefusedAckPredatesBarrier {
                barrier_offset: 50,
                candidate_offset: 49,
            }
        );

        assert_eq!(
            router.route_barrier_ack(50, 51, BarrierAckState::Busy),
            BarrierRouteDecision::Routed {
                face: BarrierAckFace::PerBarrierOwnerFace { barrier_offset: 50 },
                state: BarrierAckState::Busy,
                spent_subjects: 1,
            }
        );
        assert_eq!(
            router.route_barrier_ack(60, 62, BarrierAckState::Absent),
            BarrierRouteDecision::Routed {
                face: BarrierAckFace::PerBarrierOwnerFace { barrier_offset: 60 },
                state: BarrierAckState::Absent,
                spent_subjects: 2,
            }
        );
        // Budget at cap -> falls back to shared node ack face (`re=75`) without spending more subjects!
        assert_eq!(
            router.route_barrier_ack(75, 80, BarrierAckState::Ready),
            BarrierRouteDecision::Routed {
                face: BarrierAckFace::SharedNodeAckFace {
                    re_barrier_offset: 75
                },
                state: BarrierAckState::Ready,
                spent_subjects: 2,
            }
        );
        assert_eq!(router.highest_barrier_offset(), 75);

        // Lost verb lane -> refuses to emit fabricated acks (§15 line 4029).
        router.set_verb_lane_live(false);
        assert_eq!(
            router.route_barrier_ack(90, 91, BarrierAckState::Held),
            BarrierRouteDecision::RefusedVerbLaneLost
        );
    }
}
