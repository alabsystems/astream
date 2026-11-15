// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self restart` handoff seal gate, `pid=` vs `supervisor=` validator, `(conv_id, cwd, argv)` resume pin, restart-storm breaker, agent-vs-Mac `NEEDS YOU` classifier, and in-flight task drain. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod agent_not_needs_you;
pub mod handoff_seal_gate;
pub mod inflight_task_drain;
pub mod restart_loop_breaker;
pub mod resume_argv_pin;
pub mod supervisor_vs_agent_pid;

/// Four-byte magic prefix (`"ARST"`) for a 16-byte `astream-self-restart` wire snapshot header.
pub const SELF_RESTART_WIRE_MAGIC: [u8; 4] = *b"ARST";

/// Wire format version for `astream-self-restart` snapshot headers.
pub const SELF_RESTART_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-self-restart` wire snapshot header:
/// `[0..4] = b"ARST"`, `[4] = version (1)`, `[5] = phase_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = agent_pid (BE)`, `[12..16] = handoff_rev (BE)`.
#[must_use]
pub const fn encode_self_restart_wire(
    phase_tag: u8,
    agent_pid: u32,
    handoff_rev: u32,
) -> Option<[u8; 16]> {
    if phase_tag > 3 || agent_pid == 0 {
        return None;
    }
    Some([
        SELF_RESTART_WIRE_MAGIC[0],
        SELF_RESTART_WIRE_MAGIC[1],
        SELF_RESTART_WIRE_MAGIC[2],
        SELF_RESTART_WIRE_MAGIC[3],
        SELF_RESTART_WIRE_VERSION,
        phase_tag,
        0,
        0,
        ((agent_pid >> 24) & 0xFF) as u8,
        ((agent_pid >> 16) & 0xFF) as u8,
        ((agent_pid >> 8) & 0xFF) as u8,
        (agent_pid & 0xFF) as u8,
        ((handoff_rev >> 24) & 0xFF) as u8,
        ((handoff_rev >> 16) & 0xFF) as u8,
        ((handoff_rev >> 8) & 0xFF) as u8,
        (handoff_rev & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-self-restart` wire snapshot header into `(phase_tag, agent_pid, handoff_rev)`.
#[must_use]
pub const fn decode_self_restart_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'R', b'S', b'T', SELF_RESTART_WIRE_VERSION, phase_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let agent_pid = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let handoff_rev = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if phase_tag > 3 || agent_pid == 0 {
        return None;
    }
    Some((phase_tag, agent_pid, handoff_rev))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_restart_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_self_restart_wire(1, 42100, 5) else {
            panic!("valid astream-self-restart wire header should encode");
        };
        assert_eq!(decode_self_restart_wire(&frame), Some((1, 42100, 5)));
        assert_eq!(encode_self_restart_wire(1, 0, 5), None);
        assert_eq!(encode_self_restart_wire(4, 42100, 5), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_self_restart_wire(&bad), None);
    }
}
