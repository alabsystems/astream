// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty graphics protocol (`APC G`) per-tab RGBA pixel-memory quota and LRU eviction counter
//! preventing inline image placements from exhausting Metal/RAM budgets (`Astream.OscProto.TlaKittyImageQuota`).

#[cfg(clean_islands)]
#[path = "kitty_image_quota_island.rs"]
mod kitty_image_quota_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_px_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_img_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use kitty_image_quota_island::{osc_img_advance, osc_px_clamp};

/// Hard per-tab Kitty graphics ceiling (`67_108_864` bytes = 64 MiB).
pub const MAX_KITTY_VRAM_BYTES: u64 = 67_108_864;

contract_fn! {
    /// Verified image-memory fit predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `osc_vram_fits_isl`.
    #[must_use]
    pub const fn osc_vram_fits(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct KittyImageBudget {
    cap_bytes: u64,
    used_bytes: u64,
    uploads: u64,
}

impl KittyImageBudget {
    #[must_use]
    pub const fn new(cap_bytes: u64) -> Self {
        Self {
            cap_bytes: osc_px_clamp(cap_bytes, MAX_KITTY_VRAM_BYTES),
            used_bytes: 0,
            uploads: 0,
        }
    }

    pub fn try_upload_rgba(&mut self, width: u64, height: u64) -> bool {
        let Some(px) = width.checked_mul(height) else {
            return false;
        };
        let Some(bytes) = px.checked_mul(4) else {
            return false;
        };
        if bytes == 0 || !osc_vram_fits(self.cap_bytes, bytes) {
            return false;
        }
        let Some(next_used) = self.used_bytes.checked_add(bytes) else {
            return false;
        };
        if !osc_vram_fits(self.cap_bytes, next_used) {
            return false;
        }
        self.used_bytes = next_used;
        self.uploads = osc_img_advance(self.uploads, self.uploads.saturating_add(1));
        true
    }

    pub fn evict_bytes(&mut self, freed: u64) {
        self.used_bytes = self.used_bytes.saturating_sub(freed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_rgba_vram_budget_until_lru_evicts_older_images() {
        let mut q = KittyImageBudget::new(64 * 1024);
        assert!(q.try_upload_rgba(64, 64)); // 16 KiB
        assert!(!q.try_upload_rgba(128, 128)); // 64 KiB + 16 KiB > 64 KiB
        q.evict_bytes(16 * 1024);
        assert!(q.try_upload_rgba(128, 128));
    }
}
