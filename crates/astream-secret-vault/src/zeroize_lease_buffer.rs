// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ephemeral secret-lease buffer tracker zeroing in-RAM bearer bytes immediately on detach or TTL
//! expiry and advancing a monotone scrub epoch (`Astream.SecVault.TlaZeroizeLeaseBuffer`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "zeroize_lease_buffer_island.rs"]
mod zeroize_lease_buffer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_len_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_scrub_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use zeroize_lease_buffer_island::{sv_len_clamp, sv_scrub_advance};

/// Fixed secret-slot capacity (`64` bytes).
pub const SECRET_SLOT_CAP: usize = 64;

contract_fn! {
    /// Verified zeroized-byte check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sv_lease_scrubbed_isl`.
    #[must_use]
    pub const fn sv_lease_scrubbed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct EphemeralSecretSlot {
    buf: [u8; SECRET_SLOT_CAP],
    active_len: u64,
    scrub_epoch: u64,
}

impl Default for EphemeralSecretSlot {
    fn default() -> Self {
        Self::new()
    }
}

impl EphemeralSecretSlot {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            buf: [0u8; SECRET_SLOT_CAP],
            active_len: 0,
            scrub_epoch: 0,
        }
    }

    pub fn try_load(&mut self, secret: &[u8]) -> bool {
        self.scrub();
        if secret.is_empty() || secret.len() > SECRET_SLOT_CAP {
            return false;
        }
        let n = sv_len_clamp(secret.len() as u64, SECRET_SLOT_CAP as u64);
        let mut i = 0usize;
        while i < secret.len() {
            if let (Some(dst), Some(&src)) = (self.buf.get_mut(i), secret.get(i)) {
                *dst = src;
            }
            i = i.saturating_add(1);
        }
        self.active_len = n;
        true
    }

    pub fn load(&mut self, secret: &[u8]) {
        let _ = self.try_load(secret);
    }

    pub fn scrub(&mut self) -> bool {
        let mut idx = 0usize;
        while idx < SECRET_SLOT_CAP {
            if let Some(dst) = self.buf.get_mut(idx) {
                *dst = 0;
            }
            idx = idx.saturating_add(1);
        }
        self.active_len = 0;
        self.scrub_epoch = sv_scrub_advance(self.scrub_epoch, self.scrub_epoch.saturating_add(1));
        let mut nonzero = 0u64;
        for &b in &self.buf {
            if b != 0 {
                nonzero = nonzero.saturating_add(1);
            }
        }
        sv_lease_scrubbed(0, nonzero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scrubs_loaded_secret_bytes_back_to_all_zeros() {
        let mut slot = EphemeralSecretSlot::new();
        slot.load(b"ephemeral-hmac-key");
        assert_eq!(slot.active_len, 18);
        assert!(slot.scrub());
        assert_eq!(slot.active_len, 0);
    }
}
