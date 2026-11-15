//! Pre-authentication handshake concurrency slot gate (`MAX_PREAUTH_PEERS = 64`).

#[cfg(clean_islands)]
#[path = "handshake_preauth_slot_gate_island.rs"]
mod handshake_preauth_slot_gate_island;
#[cfg(clean_islands)]
pub use handshake_preauth_slot_gate_island::{preauth_active_clamp, preauth_rejected_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn preauth_active_clamp(active: u64) -> u64 {
    if active < 64 {
        active
    } else {
        64
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn preauth_rejected_advance(prev_rej: u64, next_rej: u64) -> u64 {
    if prev_rej < next_rej {
        next_rej
    } else {
        prev_rej
    }
}

contract_fn! {
    #[must_use]
    pub const fn preauth_slot_available(active: u64) -> bool
    clauses [ensures result == ((active < 64))]
    {
        active < 64
    }
}

pub const MAX_PREAUTH_PEERS: u64 = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HandshakePreauthSlotGate {
    active: u64,
    rejected_total: u64,
}

impl HandshakePreauthSlotGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active: 0,
            rejected_total: 0,
        }
    }

    #[must_use]
    pub const fn active(&self) -> u64 {
        self.active
    }

    #[must_use]
    pub const fn rejected_total(&self) -> u64 {
        self.rejected_total
    }

    pub fn try_acquire(&mut self) -> bool {
        if preauth_slot_available(self.active) {
            self.active = preauth_active_clamp(self.active.saturating_add(1));
            true
        } else {
            let next_rej = self.rejected_total.saturating_add(1);
            self.rejected_total = preauth_rejected_advance(self.rejected_total, next_rej);
            false
        }
    }

    pub fn release(&mut self) {
        if self.active > 0 {
            self.active = preauth_active_clamp(self.active - 1);
        }
    }
}

impl Default for HandshakePreauthSlotGate {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_up_to_sixty_four_and_drops_sixty_fifth_until_slot_frees() {
        let mut g = HandshakePreauthSlotGate::new();
        for _ in 0..MAX_PREAUTH_PEERS {
            assert!(g.try_acquire());
        }
        assert_eq!(g.active(), 64);
        assert!(!g.try_acquire());
        assert_eq!(g.rejected_total(), 1);
        g.release();
        assert!(g.try_acquire());
    }
}
