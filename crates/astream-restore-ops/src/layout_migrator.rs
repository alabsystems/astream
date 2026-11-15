// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Forward-compatible crash-restore `LAYOUT_VERSION` (`N-1 ..= N`) header negotiator
//! (`aterm` `vendor/README-astream.md`, `Astream.Restore.TlaLayoutMigrator`).

use astream_wire::crc32_ieee;

#[cfg(clean_islands)]
#[path = "layout_migrator_island.rs"]
mod layout_migrator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn layout_span_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn layout_ver_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use layout_migrator_island::{layout_span_clamp, layout_ver_advance};

/// Magic header for `aterm` crash-restore region descriptors (`ARST`).
pub const RESTORE_REGION_MAGIC: [u8; 4] = *b"ARST";
/// Maximum region byte length (`64` MiB).
pub const MAX_RESTORE_REGION_BYTES: u64 = 64 * 1024 * 1024;

contract_fn! {
    /// Verified version compatibility check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `layout_readable_isl`.
    #[must_use]
    pub const fn layout_readable(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// 24-byte CRC-protected crash-restore region superblock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RestoreRegionHeader {
    pub layout_version: u64,
    pub region_bytes: u64,
}

#[inline(never)]
fn crc32_sum(bytes: &[u8]) -> u32 {
    crc32_ieee(bytes)
}

impl RestoreRegionHeader {
    #[must_use]
    pub fn encode(&self) -> [u8; 24] {
        let clamped = layout_span_clamp(self.region_bytes, MAX_RESTORE_REGION_BYTES);
        let mut out = [0u8; 24];
        if let Some(s) = out.get_mut(0..4) {
            s.copy_from_slice(&RESTORE_REGION_MAGIC);
        }
        if let Some(s) = out.get_mut(4..12) {
            s.copy_from_slice(&self.layout_version.to_le_bytes());
        }
        if let Some(s) = out.get_mut(12..20) {
            s.copy_from_slice(&clamped.to_le_bytes());
        }
        let crc = match out.get(0..20) {
            Some(prefix) => crc32_sum(prefix),
            None => 0,
        };
        if let Some(s) = out.get_mut(20..24) {
            s.copy_from_slice(&crc.to_le_bytes());
        }
        out
    }

    /// Decodes and verifies a region header across one `aterm` update (`active_ver - 1 ..= active_ver`).
    #[allow(clippy::manual_range_contains)]
    pub fn decode_compatible(raw: &[u8], active_ver: u64) -> Result<(Self, u64), &'static str> {
        if raw.len() != 24 {
            return Err("invalid restore header size");
        }
        let body = match raw.get(0..20) {
            Some(s) => s,
            None => return Err("short header"),
        };
        let crc_s = match raw.get(20..24) {
            Some(s) => s,
            None => return Err("short crc"),
        };
        let mut c4 = [0u8; 4];
        c4.copy_from_slice(crc_s);
        if crc32_sum(body) != u32::from_le_bytes(c4) {
            return Err("restore region header CRC mismatch");
        }
        if body.get(0..4) != Some(RESTORE_REGION_MAGIC.as_slice()) {
            return Err("bad restore region magic");
        }
        let ver_s = match body.get(4..12) {
            Some(s) => s,
            None => return Err("short ver"),
        };
        let mut b8 = [0u8; 8];
        b8.copy_from_slice(ver_s);
        let ver = u64::from_le_bytes(b8);
        let len_s = match body.get(12..20) {
            Some(s) => s,
            None => return Err("short len"),
        };
        b8.copy_from_slice(len_s);
        let len = u64::from_le_bytes(b8);
        if len < 24 || len > MAX_RESTORE_REGION_BYTES {
            return Err("invalid restore region byte span");
        }

        let min_supported = active_ver.saturating_sub(1);
        if !layout_readable(ver, min_supported) || !layout_readable(active_ver, ver) {
            return Err("unsupported layout_version outside [N-1, N] window");
        }
        let target_ver = layout_ver_advance(ver, active_ver);
        Ok((
            Self {
                layout_version: ver,
                region_bytes: layout_span_clamp(len, MAX_RESTORE_REGION_BYTES),
            },
            target_ver,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn region_header_accepts_previous_and_current_layout_and_rejects_ancient_or_future() {
        let v1 = RestoreRegionHeader {
            layout_version: 1,
            region_bytes: 65_536,
        }
        .encode();
        let (hdr, upgraded_to) = RestoreRegionHeader::decode_compatible(&v1, 2).unwrap();
        assert_eq!(hdr.layout_version, 1);
        assert_eq!(upgraded_to, 2);
        // Active v3 refuses v1 (more than 1 update behind) and active v0 refuses v1 (future).
        assert!(RestoreRegionHeader::decode_compatible(&v1, 3).is_err());
        assert!(RestoreRegionHeader::decode_compatible(&v1, 0).is_err());
    }
}
