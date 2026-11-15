// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Directional 96-bit AEAD stream-frame nonce sequence & rekey-epoch ratchet.
//!
//! Encodes directional stream nonces `[dir_tag ^ epoch_le(4) || seq_le(8)]` (`12` bytes)
//! with a strict per-epoch frame cap (`nonce_seq_has_room`) so ChaCha20-Poly1305 / AES-GCM
//! stream sealers fail closed before counter exhaustion unless the caller explicitly
//! ratchets `(epoch, key)` strictly upward via [`StreamNonceRatchet::advance_epoch`].
//! Backed by Clean TLA+ island `Astream.Aead.TlaStreamNonceRatchet` with zero closures
//! (`0 mandated`).

#[cfg(clean_islands)]
#[path = "aead_nonce_ratchet_island.rs"]
mod aead_nonce_ratchet_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn nonce_epoch_advance(cur_epoch: u64, proposed_epoch: u64) -> u64 {
    if cur_epoch < proposed_epoch {
        proposed_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn nonce_seq_clamp(proposed_seq: u64, epoch_cap: u64) -> u64 {
    if proposed_seq < epoch_cap {
        proposed_seq
    } else {
        epoch_cap
    }
}
#[cfg(clean_islands)]
pub use aead_nonce_ratchet_island::{nonce_epoch_advance, nonce_seq_clamp};

contract_fn! {
    /// Kernel-certified check that the current epoch still has room to issue another
    /// unique frame nonce (`seq < epoch_cap`), linked via `clean-kernel-defeq` to
    /// `nonce_seq_has_room_isl`.
    #[must_use]
    pub const fn nonce_seq_has_room(seq: u64, epoch_cap: u64) -> bool
    clauses [ensures result == (seq < epoch_cap)]
    {
        seq < epoch_cap
    }
}

/// Default maximum frames sealed under a single directional key epoch (`2^32 - 1`).
pub const DEFAULT_EPOCH_FRAME_CAP: u64 = (1u64 << 32) - 1;

/// Directional role domain separator mixed into byte `3` MSB of the 96-bit nonce so
/// initiator->responder and responder->initiator streams never share a nonce even if
/// misconfigured with identical keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamDirection {
    /// Client / initiator -> server / responder (`0x00`).
    InitiatorToResponder,
    /// Server / responder -> client / initiator (`0x80`).
    ResponderToInitiator,
}

impl StreamDirection {
    const fn domain_bit(self) -> u8 {
        match self {
            Self::InitiatorToResponder => 0x00,
            Self::ResponderToInitiator => 0x80,
        }
    }
}

/// Error returned by [`StreamNonceRatchet`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonceRatchetError {
    /// Current epoch reached `epoch_cap`; caller must rekey and call `advance_epoch`.
    EpochExhausted { epoch: u32, epoch_cap: u64 },
    /// Proposed rekey epoch is not strictly greater than the current epoch, or exceeds 31-bit wire range.
    NonMonotoneEpoch { current: u32, proposed: u64 },
    /// Incoming frame carried unexpected `(epoch, seq)` (out-of-order, replay, or wrong epoch).
    SequenceMismatch {
        expected_epoch: u32,
        expected_seq: u64,
        got_epoch: u32,
        got_seq: u64,
    },
}

/// Encode `(direction, epoch_31bit, seq)` into a canonical 96-bit (`12`-byte) AEAD nonce.
#[must_use]
pub const fn encode_stream_nonce(direction: StreamDirection, epoch: u32, seq: u64) -> [u8; 12] {
    let ep = epoch & 0x7FFF_FFFF;
    let s = seq;
    [
        ep as u8,
        (ep >> 8) as u8,
        (ep >> 16) as u8,
        ((ep >> 24) as u8) | direction.domain_bit(),
        s as u8,
        (s >> 8) as u8,
        (s >> 16) as u8,
        (s >> 24) as u8,
        (s >> 32) as u8,
        (s >> 40) as u8,
        (s >> 48) as u8,
        (s >> 56) as u8,
    ]
}

/// Decode a 96-bit (`12`-byte) stream nonce back into `(direction, epoch, seq)`.
#[must_use]
pub const fn decode_stream_nonce(raw: &[u8; 12]) -> (StreamDirection, u32, u64) {
    let &[r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11] = raw;
    let dir = if (r3 & 0x80) != 0 {
        StreamDirection::ResponderToInitiator
    } else {
        StreamDirection::InitiatorToResponder
    };
    let epoch =
        (r0 as u32) | ((r1 as u32) << 8) | ((r2 as u32) << 16) | (((r3 & 0x7F) as u32) << 24);
    let seq = (r4 as u64)
        | ((r5 as u64) << 8)
        | ((r6 as u64) << 16)
        | ((r7 as u64) << 24)
        | ((r8 as u64) << 32)
        | ((r9 as u64) << 40)
        | ((r10 as u64) << 48)
        | ((r11 as u64) << 56);
    (dir, epoch, seq)
}

/// Stateful directional nonce generator / lockstep verifier for encrypted frame streams.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StreamNonceRatchet {
    direction: StreamDirection,
    prev_epoch: u32,
    cur_epoch: u32,
    frame_seq: u64,
    epoch_cap: u64,
}

impl StreamNonceRatchet {
    /// Maximum 31-bit epoch value (`0x7FFF_FFFF`), reserving bit 31 for [`StreamDirection`].
    pub const MAX_EPOCH: u32 = 0x7FFF_FFFF;

    /// Construct a new directional ratchet at `epoch = 0, seq = 0`.
    #[must_use]
    pub const fn new(direction: StreamDirection, epoch_cap: u64) -> Self {
        let cap = if epoch_cap == 0 { 1 } else { epoch_cap };
        Self {
            direction,
            prev_epoch: 0,
            cur_epoch: 0,
            frame_seq: 0,
            epoch_cap: cap,
        }
    }

    /// Current key epoch (`0..=MAX_EPOCH`).
    #[must_use]
    pub const fn epoch(&self) -> u32 {
        self.cur_epoch
    }

    /// Next frame sequence number within the current epoch (`0..=epoch_cap`).
    #[must_use]
    pub const fn next_seq(&self) -> u64 {
        self.frame_seq
    }

    /// True when the current epoch has exhausted `epoch_cap` and requires `advance_epoch`.
    #[must_use]
    pub const fn needs_rekey(&self) -> bool {
        !nonce_seq_has_room(self.frame_seq, self.epoch_cap)
    }

    /// Issue the next unique `(epoch, seq, nonce)` for outbound frame encryption,
    /// advancing `frame_seq` by `1` or failing closed with [`NonceRatchetError::EpochExhausted`].
    pub fn next_outbound_nonce(&mut self) -> Result<(u32, u64, [u8; 12]), NonceRatchetError> {
        if !nonce_seq_has_room(self.frame_seq, self.epoch_cap) {
            return Err(NonceRatchetError::EpochExhausted {
                epoch: self.cur_epoch,
                epoch_cap: self.epoch_cap,
            });
        }
        let seq = self.frame_seq;
        let nonce = encode_stream_nonce(self.direction, self.cur_epoch, seq);
        let advanced = nonce_seq_clamp(seq.saturating_add(1), self.epoch_cap);
        self.frame_seq = advanced;
        Ok((self.cur_epoch, seq, nonce))
    }

    /// Verify an inbound `(got_epoch, got_seq)` in strict lockstep before/after AEAD open,
    /// deriving the expected 96-bit nonce and advancing `frame_seq` on match.
    pub fn accept_inbound(
        &mut self,
        got_epoch: u32,
        got_seq: u64,
    ) -> Result<[u8; 12], NonceRatchetError> {
        if got_epoch != self.cur_epoch || got_seq != self.frame_seq {
            return Err(NonceRatchetError::SequenceMismatch {
                expected_epoch: self.cur_epoch,
                expected_seq: self.frame_seq,
                got_epoch,
                got_seq,
            });
        }
        if !nonce_seq_has_room(self.frame_seq, self.epoch_cap) {
            return Err(NonceRatchetError::EpochExhausted {
                epoch: self.cur_epoch,
                epoch_cap: self.epoch_cap,
            });
        }
        let nonce = encode_stream_nonce(self.direction, self.cur_epoch, got_seq);
        self.frame_seq = nonce_seq_clamp(self.frame_seq.saturating_add(1), self.epoch_cap);
        Ok(nonce)
    }

    /// Ratchet strictly forward to `proposed_epoch > cur_epoch` (`<= MAX_EPOCH`) and reset `frame_seq = 0`.
    pub fn advance_epoch(&mut self, proposed_epoch: u32) -> Result<u32, NonceRatchetError> {
        if proposed_epoch <= self.cur_epoch || proposed_epoch > Self::MAX_EPOCH {
            return Err(NonceRatchetError::NonMonotoneEpoch {
                current: self.cur_epoch,
                proposed: proposed_epoch as u64,
            });
        }
        let next_ep = nonce_epoch_advance(self.cur_epoch as u64, proposed_epoch as u64) as u32;
        self.prev_epoch = self.cur_epoch;
        self.cur_epoch = next_ep;
        self.frame_seq = 0;
        Ok(self.cur_epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directional_nonces_exhaust_cleanly_reject_replays_and_ratchet_epochs() {
        let mut tx = StreamNonceRatchet::new(StreamDirection::InitiatorToResponder, 2);
        let mut rx = StreamNonceRatchet::new(StreamDirection::InitiatorToResponder, 2);
        let mut rev = StreamNonceRatchet::new(StreamDirection::ResponderToInitiator, 2);

        let (ep0, s0, n0) = tx.next_outbound_nonce().unwrap();
        let (_, _, rev_n0) = rev.next_outbound_nonce().unwrap();
        assert_ne!(
            n0, rev_n0,
            "opposite directions must never collide on nonce"
        );
        assert_eq!(rx.accept_inbound(ep0, s0).unwrap(), n0);
        assert_eq!(
            rx.accept_inbound(ep0, s0),
            Err(NonceRatchetError::SequenceMismatch {
                expected_epoch: 0,
                expected_seq: 1,
                got_epoch: 0,
                got_seq: 0,
            })
        );

        let (ep1, s1, n1) = tx.next_outbound_nonce().unwrap();
        assert_eq!(rx.accept_inbound(ep1, s1).unwrap(), n1);
        assert!(tx.needs_rekey());
        assert_eq!(
            tx.next_outbound_nonce(),
            Err(NonceRatchetError::EpochExhausted {
                epoch: 0,
                epoch_cap: 2,
            })
        );

        assert_eq!(
            tx.advance_epoch(0),
            Err(NonceRatchetError::NonMonotoneEpoch {
                current: 0,
                proposed: 0,
            })
        );
        assert_eq!(tx.advance_epoch(1).unwrap(), 1);
        assert_eq!(rx.advance_epoch(1).unwrap(), 1);
        let (ep2, s2, n2) = tx.next_outbound_nonce().unwrap();
        assert_eq!((ep2, s2), (1, 0));
        assert_eq!(rx.accept_inbound(ep2, s2).unwrap(), n2);
        assert_eq!(
            decode_stream_nonce(&n2),
            (StreamDirection::InitiatorToResponder, 1, 0)
        );
    }
}
