// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `V1NodeAck` (`/f/<F>/pub/<node>/node/ack` §5.3) schema & monotone directive-settlement guard
//! (`evidence/manifest.toml` `wire.wake-and-control-acks`;
//! `Astream.Wire.TlaNodeAckControlFaceVerdictGuard`).
//!
//! Enforces `v=1` node control-face acknowledgement ordering:
//! - Requires `schema_version == 1`, `ack_record_offset >= re_directive_offset`, and valid
//!   `NodeAckState` code (`0..=3`: `applied`, `already`, `refused`, `busy`),
//! - Advances `settled_directive_offset` monotonically so out-of-order stale node acks never
//!   roll back an already-settled directive!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "node_ack_control_face_verdict_guard_island.rs"]
mod node_ack_control_face_verdict_guard_island;
#[cfg(clean_islands)]
pub use node_ack_control_face_verdict_guard_island::{
    node_ack_state_clamp_b156, settled_directive_advance_b156,
};

/// Maximum legal `NodeAckState` discriminant (`3`: `0=applied, 1=already, 2=refused, 3=busy`).
pub const MAX_NODE_ACK_STATE_CODE: u64 = 3;

#[cfg(not(clean_islands))]
/// Clamp `NodeAckState` discriminant to `MAX_NODE_ACK_STATE_CODE` (`3`).
#[must_use]
pub const fn node_ack_state_clamp_b156(cand_state: u64, max_state: u64) -> u64 {
    if cand_state < max_state {
        cand_state
    } else {
        max_state
    }
}

#[cfg(not(clean_islands))]
/// Advance highest settled control directive offset monotonically.
#[must_use]
pub const fn settled_directive_advance_b156(cur_settled: u64, cand_directive: u64) -> u64 {
    if cur_settled < cand_directive {
        cand_directive
    } else {
        cur_settled
    }
}

contract_fn! {
    /// True iff `schema_ver == 1`, `state_code <= 3`, and `ack_offset >= re_directive_offset`.
    #[must_use]
    pub const fn v1_node_ack_causal_valid_b156(
        schema_ver: u64,
        state_code: u64,
        re_directive_offset: u64,
        ack_offset: u64,
    ) -> bool
    clauses [ensures result == (schema_ver == 1 && state_code <= 3 && re_directive_offset <= ack_offset)]
    {
        schema_ver == 1
            && state_code <= MAX_NODE_ACK_STATE_CODE
            && re_directive_offset <= ack_offset
    }
}

/// Verdict for a `V1NodeAck` control-face frame.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeAckDecision {
    AcceptedNewDirectiveSettlement {
        re_directive_offset: u64,
        state_code: u64,
        settled_watermark: u64,
    },
    IgnoredStaleDirectiveAck {
        re_directive_offset: u64,
        settled_watermark: u64,
    },
    RefusedMalformedOrPrePublishedNodeAck,
}

/// Per-node `V1NodeAck` control-face settlement guard.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NodeAckSettlementGuard {
    has_settled: bool,
    settled_directive_offset: u64,
}

impl NodeAckSettlementGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            has_settled: false,
            settled_directive_offset: 0,
        }
    }

    /// Validate and fold a `/f/<F>/pub/<node>/node/ack` frame.
    pub fn observe_node_ack(
        &mut self,
        schema_ver: u64,
        state_code: u64,
        re_directive_offset: u64,
        ack_offset: u64,
    ) -> NodeAckDecision {
        if !v1_node_ack_causal_valid_b156(schema_ver, state_code, re_directive_offset, ack_offset) {
            return NodeAckDecision::RefusedMalformedOrPrePublishedNodeAck;
        }
        if self.has_settled && re_directive_offset <= self.settled_directive_offset {
            return NodeAckDecision::IgnoredStaleDirectiveAck {
                re_directive_offset,
                settled_watermark: self.settled_directive_offset,
            };
        }
        self.has_settled = true;
        self.settled_directive_offset =
            settled_directive_advance_b156(self.settled_directive_offset, re_directive_offset);
        NodeAckDecision::AcceptedNewDirectiveSettlement {
            re_directive_offset,
            state_code: node_ack_state_clamp_b156(state_code, MAX_NODE_ACK_STATE_CODE),
            settled_watermark: self.settled_directive_offset,
        }
    }
}

impl Default for NodeAckSettlementGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_pre_published_or_bad_version_node_acks_and_fences_stale_directives() {
        let mut g = NodeAckSettlementGuard::new();
        // Ack at offset 4 claiming to answer directive at offset 9 -> refused!
        assert_eq!(
            g.observe_node_ack(1, 0, 9, 4),
            NodeAckDecision::RefusedMalformedOrPrePublishedNodeAck
        );
        assert_eq!(
            g.observe_node_ack(1, 0, 9, 12),
            NodeAckDecision::AcceptedNewDirectiveSettlement {
                re_directive_offset: 9,
                state_code: 0,
                settled_watermark: 9,
            }
        );
        // Late out-of-order ack for directive 5 -> ignored without rolling back watermark 9!
        assert_eq!(
            g.observe_node_ack(1, 1, 5, 14),
            NodeAckDecision::IgnoredStaleDirectiveAck {
                re_directive_offset: 5,
                settled_watermark: 9,
            }
        );
    }
}
