// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Seccomp-BPF foreign-process deterministic record/replay (`docs/ROADMAP.md` §4): `SECCOMP_RET_TRACE` 5-syscall pre-filter mask, replay-time syscall no-op neutralization gate, taped return/buffer injector, `PTRACE_TRACEME` single-thread `execve` lineage, short/wrong-kind tape abort latch, and independent SHA-256 oracle parity check. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod oracle_sha256_parity;
pub mod ptrace_execve_lineage;
pub mod seccomp_five_mask;
pub mod syscall_noop_neutralize;
pub mod tape_divergence_abort;
pub mod taped_return_injector;

/// Four-byte magic prefix (`"ASCP"`) for a 16-byte `astream-seccomp-replay` wire snapshot header.
pub const SECCOMP_REPLAY_WIRE_MAGIC: [u8; 4] = *b"ASCP";

/// Wire format version for `astream-seccomp-replay` snapshot headers.
pub const SECCOMP_REPLAY_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-seccomp-replay` wire snapshot header:
/// `[0..4] = b"ASCP"`, `[4] = version (1)`, `[5] = mask_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = tape_idx (BE)`, `[12..16] = injected_bytes (BE)`.
#[must_use]
pub const fn encode_seccomp_replay_wire(
    mask_tag: u8,
    tape_idx: u32,
    injected_bytes: u32,
) -> Option<[u8; 16]> {
    if mask_tag > 3 || tape_idx == 0 {
        return None;
    }
    Some([
        SECCOMP_REPLAY_WIRE_MAGIC[0],
        SECCOMP_REPLAY_WIRE_MAGIC[1],
        SECCOMP_REPLAY_WIRE_MAGIC[2],
        SECCOMP_REPLAY_WIRE_MAGIC[3],
        SECCOMP_REPLAY_WIRE_VERSION,
        mask_tag,
        0,
        0,
        ((tape_idx >> 24) & 0xFF) as u8,
        ((tape_idx >> 16) & 0xFF) as u8,
        ((tape_idx >> 8) & 0xFF) as u8,
        (tape_idx & 0xFF) as u8,
        ((injected_bytes >> 24) & 0xFF) as u8,
        ((injected_bytes >> 16) & 0xFF) as u8,
        ((injected_bytes >> 8) & 0xFF) as u8,
        (injected_bytes & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-seccomp-replay` wire snapshot header into `(mask_tag, tape_idx, injected_bytes)`.
#[must_use]
pub const fn decode_seccomp_replay_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'S', b'C', b'P', SECCOMP_REPLAY_WIRE_VERSION, mask_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let tape_idx = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let injected_bytes =
        ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if mask_tag > 3 || tape_idx == 0 {
        return None;
    }
    Some((mask_tag, tape_idx, injected_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seccomp_replay_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_seccomp_replay_wire(1, 32, 256) else {
            panic!("valid astream-seccomp-replay wire header should encode");
        };
        assert_eq!(decode_seccomp_replay_wire(&frame), Some((1, 32, 256)));
        assert_eq!(encode_seccomp_replay_wire(1, 0, 256), None);
        assert_eq!(encode_seccomp_replay_wire(4, 32, 256), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_seccomp_replay_wire(&bad), None);
    }
}
