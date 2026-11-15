// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty keyboard protocol (`CSI codepoint ; modifiers u`) 1-indexed modifier bitmask decoder
//! (`1 + bitmask` -> `Shift | Alt | Ctrl | Super`; `Astream.KeyChord.TlaCsiUModifierMask`).

#[cfg(clean_islands)]
#[path = "csi_u_modifier_mask_island.rs"]
mod csi_u_modifier_mask_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_mod_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_key_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use csi_u_modifier_mask_island::{kc_key_advance, kc_mod_clamp};

/// Four-modifier mask cap (`0x0F`: `Shift=1`, `Alt=2`, `Ctrl=4`, `Super=8`).
pub const MAX_KITTY_MOD_MASK: u64 = 15;

contract_fn! {
    /// Verified modifier-mask bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kc_mods_valid_isl`.
    #[must_use]
    pub const fn kc_mods_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct CsiUDecoder {
    keys_decoded: u64,
}

impl CsiUDecoder {
    #[must_use]
    pub const fn new() -> Self {
        Self { keys_decoded: 0 }
    }

    /// Converts Kitty's 1-based wire `modifiers_param` (`0` or `1` -> `0`, `5` -> `4 = Ctrl`)
    /// into a bounded 4-bit mask.
    pub fn decode_modifiers(&mut self, wire_param: u64) -> u64 {
        let raw_mask = wire_param.saturating_sub(1) & MAX_KITTY_MOD_MASK;
        let clamped = kc_mod_clamp(raw_mask, MAX_KITTY_MOD_MASK);
        self.keys_decoded = kc_key_advance(self.keys_decoded, self.keys_decoded.saturating_add(1));
        let _ = kc_mods_valid(MAX_KITTY_MOD_MASK, clamped);
        clamped
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_one_indexed_kitty_csi_u_modifier_parameter() {
        let mut d = CsiUDecoder::new();
        assert_eq!(d.decode_modifiers(1), 0);
        assert_eq!(d.decode_modifiers(5), 4); // Ctrl
        assert_eq!(d.decode_modifiers(6), 5); // Ctrl + Shift
    }
}
