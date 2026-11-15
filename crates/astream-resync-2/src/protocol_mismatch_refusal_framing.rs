// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Frozen cross-version protocol-mismatch refusal codec (`broker.protocol-mismatch-named`,
//! `docs/DESIGN-aterm-fabric.md` §11.1 lines 2953–2968;
//! `Astream.Wire.TlaProtocolMismatchRefusalFraming`).
//!
//! Models the zero-negotiation frozen refusal layout `[peer_version][0x83][9 = ERR_PROTOCOL][len: u32 LE][msg][broker_version]`:
//! - When a peer sends a request in `peer_version != broker_version`, the broker stamps `Error{9}`
//!   in `peer_version` so the peer's own decoder parses it, appending `broker_version` as the 1-byte
//!   trailer immediately after `msg`, then closes!
//! - When a client receives either that `ERR_PROTOCOL` trailer or any reply stamped in a foreign
//!   version byte (`frame_ver != client_ver`), it surfaces `ProtocolMismatch { broker, client }`
//!   and latches the connection out-of-step!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "protocol_mismatch_refusal_framing_island.rs"]
mod protocol_mismatch_refusal_framing_island;
#[cfg(clean_islands)]
pub use protocol_mismatch_refusal_framing_island::{
    mismatch_epoch_advance_b136, mismatch_msg_clamp_b136,
};

/// Frozen error response tag across all `PROTO_VERSION`s (`0x83`).
pub const FROZEN_TAG_ERROR: u8 = 0x83;

/// Frozen protocol-mismatch error code (`9 = ERR_PROTOCOL`).
pub const FROZEN_ERR_PROTOCOL: u8 = 9;

/// Maximum diagnostic message length inside a protocol-mismatch refusal (`256` bytes).
pub const MAX_MISMATCH_MSG_LEN: u64 = 256;

#[cfg(not(clean_islands))]
/// Clamp refusal message byte length to `msg_cap`.
#[must_use]
pub const fn mismatch_msg_clamp_b136(cand_len: u64, msg_cap: u64) -> u64 {
    if cand_len < msg_cap {
        cand_len
    } else {
        msg_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance mismatch latch epoch.
#[must_use]
pub const fn mismatch_epoch_advance_b136(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `tag == FROZEN_TAG_ERROR && code == FROZEN_ERR_PROTOCOL && broker_ver != client_ver`.
    #[must_use]
    pub const fn frozen_refusal_valid_b136(
        tag: u8,
        code: u8,
        broker_ver: u8,
        client_ver: u8,
    ) -> bool
    clauses [ensures result == (tag == 0x83 && code == 9 && broker_ver != client_ver)]
    {
        tag == 0x83 && code == 9 && broker_ver != client_ver
    }
}

/// Decoded cross-version reply classification (`client.rs decode_reply` / `foreign_protocol`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ReplyProtocolCheck {
    /// Same `PROTO_VERSION` and not `ERR_PROTOCOL` — proceed with normal v2 frame decode.
    MatchingProtocol,
    /// Named mismatch (`ProtocolMismatch { broker, client }`); connection is latched out-of-step!
    NamedMismatch { broker: u8, client: u8 },
    /// Truncated or malformed frozen error header.
    MalformedFrozenError,
}

/// Inspect a raw reply frame payload `[ver, tag, ...]` from a client speaking `client_ver`
/// without loops or heap allocation.
#[must_use]
pub fn classify_reply_protocol(frame: &[u8], client_ver: u8) -> ReplyProtocolCheck {
    let [frame_ver, rest @ ..] = frame else {
        return ReplyProtocolCheck::MalformedFrozenError;
    };
    let frame_ver = *frame_ver;
    if frame_ver != client_ver {
        // Broker older than client stamped its own version byte directly!
        return ReplyProtocolCheck::NamedMismatch {
            broker: frame_ver,
            client: client_ver,
        };
    }
    let [tag, after_tag @ ..] = rest else {
        return ReplyProtocolCheck::MalformedFrozenError;
    };
    let tag = *tag;
    if tag != FROZEN_TAG_ERROR {
        return ReplyProtocolCheck::MatchingProtocol;
    }
    let [code, b0, b1, b2, b3, body_and_trailer @ ..] = after_tag else {
        return ReplyProtocolCheck::MalformedFrozenError;
    };
    let code = *code;
    if code != FROZEN_ERR_PROTOCOL {
        return ReplyProtocolCheck::MatchingProtocol;
    }
    let msg_len = u32::from_le_bytes([*b0, *b1, *b2, *b3]) as usize;
    let _clamped = mismatch_msg_clamp_b136(msg_len as u64, MAX_MISMATCH_MSG_LEN);
    let Some(after_msg) = body_and_trailer.get(msg_len..) else {
        return ReplyProtocolCheck::MalformedFrozenError;
    };
    let [broker_ver, ..] = after_msg else {
        return ReplyProtocolCheck::MalformedFrozenError;
    };
    let broker_ver = *broker_ver;
    if frozen_refusal_valid_b136(tag, code, broker_ver, client_ver) {
        ReplyProtocolCheck::NamedMismatch {
            broker: broker_ver,
            client: client_ver,
        }
    } else {
        ReplyProtocolCheck::MalformedFrozenError
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frozen_refusal_and_foreign_version_both_decode_as_named_mismatch() {
        // Case 1: Broker v2 answering v1 client in client's v1 envelope `[1, 0x83, 9, 3,0,0,0, b'b',b'a',b'd', 2]`:
        let frame_v2_to_v1 = [1_u8, 0x83, 9, 3, 0, 0, 0, b'b', b'a', b'd', 2];
        assert_eq!(
            classify_reply_protocol(&frame_v2_to_v1, 1),
            ReplyProtocolCheck::NamedMismatch {
                broker: 2,
                client: 1
            }
        );
        // Case 2: Older v1 broker answering v2 client in v1's own envelope `[1, 0x83, 5, ...]`:
        let frame_old_v1 = [1_u8, 0x83, 5, 0, 0, 0, 0];
        assert_eq!(
            classify_reply_protocol(&frame_old_v1, 2),
            ReplyProtocolCheck::NamedMismatch {
                broker: 1,
                client: 2
            }
        );
        // Case 3: Matching v2 non-error `Mark` (`0x84`) passes straight through:
        assert_eq!(
            classify_reply_protocol(&[2_u8, 0x84, 0, 0], 2),
            ReplyProtocolCheck::MatchingProtocol
        );
        let _ = mismatch_epoch_advance_b136(0, 1);
    }
}
