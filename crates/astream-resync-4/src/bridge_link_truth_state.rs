// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Heartbeat-free endpoint `fabric=absent|stalled|connected` link-truth & `post --wait` fast-fail
//! (`docs/REQUIREMENTS-fabric-operations-2026-09-14.md` §2 lines 407–409,
//! `docs/DESIGN-aterm-fabric.md` §7 & §11.2; `Astream.Host.TlaBridgeLinkTruthState`).
//!
//! Ensures `fabric=` reports truth without synthetic bus heartbeats:
//! - The bridge reports its broker LINK state over the inherited control fd (`DialFailed`,
//!   `ConnectionLost`, `LinkUp { ack_rtt_ms }`),
//! - The endpoint reports `FabricTruth::Connected` ONLY while both the bridge fd is attached AND
//!   its broker link is up,
//! - While a bridge is attached with its broker link down, the endpoint reports
//!   `FabricTruth::Stalled` and fails `post --wait` fast (`PostWaitDecision::FailFastStalledFabric`)
//!   instead of hanging until a user timeout!

#[cfg(clean_islands)]
#[path = "bridge_link_truth_state_island.rs"]
mod bridge_link_truth_state_island;
#[cfg(clean_islands)]
pub use bridge_link_truth_state_island::{bridge_ack_rtt_clamp_b139, bridge_link_gen_advance_b139};

/// Upper bound on reported broker ack round-trip latency (`60_000` ms).
pub const MAX_REPORTED_ACK_RTT_MS: u64 = 60_000;

#[cfg(not(clean_islands))]
/// Clamp reported ack round-trip latency (`ms`) to `rtt_cap_ms`.
#[must_use]
pub const fn bridge_ack_rtt_clamp_b139(cand_rtt_ms: u64, rtt_cap_ms: u64) -> u64 {
    if cand_rtt_ms < rtt_cap_ms {
        cand_rtt_ms
    } else {
        rtt_cap_ms
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the bridge link-state generation counter.
#[must_use]
pub const fn bridge_link_gen_advance_b139(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// `post --wait` may block for a receipt ONLY when both the bridge fd is attached
    /// and its broker link is actively up (`fabric=connected`).
    #[must_use]
    pub const fn post_wait_admissible_b139(bridge_attached: bool, broker_link_up: bool) -> bool
    clauses [ensures result == (bridge_attached && broker_link_up)]
    {
        bridge_attached && broker_link_up
    }
}

/// Reason a bridge's broker link entered `stalled`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StalledCause {
    AwaitingInitialDial,
    DialFailed,
    ConnectionLost,
}

/// Endpoint-observable `fabric=` status reported without synthetic bus heartbeats.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FabricTruth {
    Absent,
    Stalled {
        cause: StalledCause,
        link_gen: u64,
        last_ack_rtt_ms: u64,
    },
    Connected {
        link_gen: u64,
        last_ack_rtt_ms: u64,
    },
}

/// Admission result for an operator/agent `post --wait` request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostWaitDecision {
    AdmitWaitConnected { link_gen: u64 },
    FailFastFabricAbsent,
    FailFastStalledFabric { cause: StalledCause, link_gen: u64 },
}

/// Endpoint state machine tracking bridge attachment and broker link reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EndpointFabricLinkState {
    bridge_attached: bool,
    broker_link_up: bool,
    stalled_cause: StalledCause,
    link_gen: u64,
    last_ack_rtt_ms: u64,
}

impl EndpointFabricLinkState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bridge_attached: false,
            broker_link_up: false,
            stalled_cause: StalledCause::AwaitingInitialDial,
            link_gen: 0,
            last_ack_rtt_ms: 0,
        }
    }

    pub fn attach_bridge(&mut self, cand_gen: u64) {
        self.link_gen = bridge_link_gen_advance_b139(self.link_gen, cand_gen);
        self.bridge_attached = true;
        self.broker_link_up = false;
        self.stalled_cause = StalledCause::AwaitingInitialDial;
    }

    pub fn detach_bridge(&mut self, cand_gen: u64) {
        self.link_gen = bridge_link_gen_advance_b139(self.link_gen, cand_gen);
        self.bridge_attached = false;
        self.broker_link_up = false;
    }

    pub fn report_link_up(&mut self, cand_gen: u64, raw_ack_rtt_ms: u64) {
        if !self.bridge_attached {
            return;
        }
        self.link_gen = bridge_link_gen_advance_b139(self.link_gen, cand_gen);
        self.last_ack_rtt_ms = bridge_ack_rtt_clamp_b139(raw_ack_rtt_ms, MAX_REPORTED_ACK_RTT_MS);
        self.broker_link_up = true;
    }

    pub fn report_link_down(&mut self, cand_gen: u64, cause: StalledCause) {
        if !self.bridge_attached {
            return;
        }
        self.link_gen = bridge_link_gen_advance_b139(self.link_gen, cand_gen);
        self.broker_link_up = false;
        self.stalled_cause = cause;
    }

    #[must_use]
    pub const fn fabric_truth(&self) -> FabricTruth {
        if !self.bridge_attached {
            FabricTruth::Absent
        } else if self.broker_link_up {
            FabricTruth::Connected {
                link_gen: self.link_gen,
                last_ack_rtt_ms: bridge_ack_rtt_clamp_b139(
                    self.last_ack_rtt_ms,
                    MAX_REPORTED_ACK_RTT_MS,
                ),
            }
        } else {
            FabricTruth::Stalled {
                cause: self.stalled_cause,
                link_gen: self.link_gen,
                last_ack_rtt_ms: bridge_ack_rtt_clamp_b139(
                    self.last_ack_rtt_ms,
                    MAX_REPORTED_ACK_RTT_MS,
                ),
            }
        }
    }

    #[must_use]
    pub const fn admit_post_wait(&self) -> PostWaitDecision {
        if post_wait_admissible_b139(self.bridge_attached, self.broker_link_up) {
            PostWaitDecision::AdmitWaitConnected {
                link_gen: self.link_gen,
            }
        } else if !self.bridge_attached {
            PostWaitDecision::FailFastFabricAbsent
        } else {
            PostWaitDecision::FailFastStalledFabric {
                cause: self.stalled_cause,
                link_gen: self.link_gen,
            }
        }
    }
}

impl Default for EndpointFabricLinkState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn endpoint_reports_stalled_and_fails_post_wait_fast_when_bridge_link_drops() {
        let mut s = EndpointFabricLinkState::new();
        assert_eq!(s.fabric_truth(), FabricTruth::Absent);
        assert_eq!(s.admit_post_wait(), PostWaitDecision::FailFastFabricAbsent);

        s.attach_bridge(1);
        assert_eq!(
            s.admit_post_wait(),
            PostWaitDecision::FailFastStalledFabric {
                cause: StalledCause::AwaitingInitialDial,
                link_gen: 1
            }
        );

        s.report_link_up(2, 4);
        assert_eq!(
            s.fabric_truth(),
            FabricTruth::Connected {
                link_gen: 2,
                last_ack_rtt_ms: 4
            }
        );
        assert_eq!(
            s.admit_post_wait(),
            PostWaitDecision::AdmitWaitConnected { link_gen: 2 }
        );

        s.report_link_down(3, StalledCause::ConnectionLost);
        assert_eq!(
            s.fabric_truth(),
            FabricTruth::Stalled {
                cause: StalledCause::ConnectionLost,
                link_gen: 3,
                last_ack_rtt_ms: 4
            }
        );
        assert_eq!(
            s.admit_post_wait(),
            PostWaitDecision::FailFastStalledFabric {
                cause: StalledCause::ConnectionLost,
                link_gen: 3
            }
        );
    }
}
