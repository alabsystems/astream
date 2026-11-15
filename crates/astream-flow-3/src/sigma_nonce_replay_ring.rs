//! Mutual Ed25519 SIGMA handshake challenge-nonce replay ring.

#[cfg(clean_islands)]
#[path = "sigma_nonce_replay_ring_island.rs"]
mod sigma_nonce_replay_ring_island;
#[cfg(clean_islands)]
pub use sigma_nonce_replay_ring_island::{sigma_epoch_ms_advance, sigma_replay_slot_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sigma_replay_slot_clamp(slot: u64) -> u64 {
    if slot < 512 {
        slot
    } else {
        512
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sigma_epoch_ms_advance(prev_ms: u64, sample_ms: u64) -> u64 {
    if prev_ms < sample_ms {
        sample_ms
    } else {
        prev_ms
    }
}

contract_fn! {
    #[must_use]
    pub const fn sigma_stamp_fresh(elapsed_ms: u64, ttl_ms: u64) -> bool
    clauses [ensures result == ((elapsed_ms < ttl_ms))]
    {
        elapsed_ms < ttl_ms
    }
}

pub const MAX_SIGMA_REPLAY_SLOTS: usize = 512;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NonceSlot {
    nonce_tag: [u8; 32],
    seen_at_ms: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SigmaReplayVerdict {
    FreshAccepted,
    ReplayedHandshakeNonce,
}

#[derive(Debug, Clone)]
pub struct SigmaNonceReplayRing {
    slots: Vec<NonceSlot>,
    write_cursor: usize,
    now_ms: u64,
    ttl_ms: u64,
}

impl SigmaNonceReplayRing {
    #[must_use]
    pub const fn new(ttl_ms: u64) -> Self {
        Self {
            slots: Vec::new(),
            write_cursor: 0,
            now_ms: 0,
            ttl_ms: if ttl_ms == 0 { 1 } else { ttl_ms },
        }
    }

    #[must_use]
    pub const fn now_ms(&self) -> u64 {
        self.now_ms
    }

    #[must_use]
    pub const fn ttl_ms(&self) -> u64 {
        self.ttl_ms
    }

    #[must_use]
    pub const fn write_cursor(&self) -> usize {
        self.write_cursor
    }

    pub fn admit_nonce(&mut self, nonce_tag: [u8; 32], sample_ms: u64) -> SigmaReplayVerdict {
        self.now_ms = sigma_epoch_ms_advance(self.now_ms, sample_ms);
        let mut rest: &[NonceSlot] = self.slots.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            let elapsed = self.now_ms.saturating_sub(slot.seen_at_ms);
            if sigma_stamp_fresh(elapsed, self.ttl_ms) && slot.nonce_tag == nonce_tag {
                return SigmaReplayVerdict::ReplayedHandshakeNonce;
            }
            rest = tail;
        }
        let clamped_cur = sigma_replay_slot_clamp(self.write_cursor as u64) as usize;
        let idx = if clamped_cur < MAX_SIGMA_REPLAY_SLOTS {
            clamped_cur
        } else {
            0
        };
        let entry = NonceSlot {
            nonce_tag,
            seen_at_ms: self.now_ms,
        };
        if self.slots.len() < MAX_SIGMA_REPLAY_SLOTS {
            self.slots.push(entry);
        } else if let Some(slot) = self.slots.get_mut(idx) {
            *slot = entry;
        }
        let next_cur = idx.saturating_add(1);
        self.write_cursor = if next_cur < MAX_SIGMA_REPLAY_SLOTS {
            next_cur
        } else {
            0
        };
        SigmaReplayVerdict::FreshAccepted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_replayed_sigma_nonce_within_ttl_and_accepts_after_expiry() {
        let mut ring = SigmaNonceReplayRing::new(30_000);
        assert_eq!(ring.ttl_ms(), 30_000);
        let nonce = [0xA5u8; 32];
        assert_eq!(
            ring.admit_nonce(nonce, 1_000),
            SigmaReplayVerdict::FreshAccepted
        );
        assert_eq!(ring.write_cursor(), 1);
        assert_eq!(
            ring.admit_nonce(nonce, 15_000),
            SigmaReplayVerdict::ReplayedHandshakeNonce
        );
        assert_eq!(
            ring.admit_nonce(nonce, 31_000),
            SigmaReplayVerdict::FreshAccepted
        );
        assert_eq!(ring.now_ms(), 31_000);
        assert_eq!(sigma_replay_slot_clamp(999), 512);
    }
}
