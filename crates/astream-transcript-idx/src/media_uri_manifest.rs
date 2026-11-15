// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Out-of-line `media` attachment `(mime_type, uri)` manifest & quota tracker (`transcript.jsonl`
//! stores `uri` references on disk rather than raw media bytes; `Astream.Transcript.TlaMediaUriManifest`).

#[cfg(clean_islands)]
#[path = "media_uri_manifest_island.rs"]
mod media_uri_manifest_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_media_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_bytes_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use media_uri_manifest_island::{tr_bytes_advance, tr_media_clamp};

/// Maximum attachments tracked per conversation manifest (`1,024` files, `256` MiB total).
pub const MAX_MEDIA_ITEMS: u64 = 1_024;
pub const MAX_MEDIA_TOTAL_BYTES: u64 = 256 * 1024 * 1024;

contract_fn! {
    /// Verified media quota check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tr_media_within_cap_isl`.
    #[must_use]
    pub const fn tr_media_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MediaRef {
    pub step_index: u64,
    pub mime_type: String,
    pub uri: String,
    pub byte_len: u64,
}

/// Validates and indexes out-of-line transcript media references.
#[derive(Debug, Clone, Default)]
pub struct TranscriptMediaManifest {
    items: Vec<MediaRef>,
    total_bytes: u64,
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn uri_has_bad_segment(uri: &str) -> bool {
    let bytes = uri.as_bytes();
    let mut idx = 0usize;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if b < 0x20 || b == 0x7F {
            return true;
        }
        if b == b'.' && bytes.get(idx.saturating_add(1)) == Some(&b'.') {
            let prev_slash = idx == 0 || bytes.get(idx.saturating_sub(1)) == Some(&b'/');
            let next_b = bytes.get(idx.saturating_add(2));
            let next_slash = next_b.is_none() || next_b == Some(&b'/');
            if prev_slash && next_slash {
                return true;
            }
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl TranscriptMediaManifest {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            items: Vec::new(),
            total_bytes: 0,
        }
    }

    pub fn register_media(
        &mut self,
        step_index: u64,
        mime_type: &str,
        uri: &str,
        byte_len: u64,
    ) -> Result<(), &'static str> {
        if mime_type.trim().is_empty() || byte_len == 0 {
            return Err("transcript media requires non-empty mime_type and byte_len");
        }
        let cap_items = tr_media_clamp(MAX_MEDIA_ITEMS, MAX_MEDIA_ITEMS) as usize;
        if self.items.len() >= cap_items {
            return Err("media attachment count ceiling exceeded");
        }
        if (!uri.starts_with('/') && !uri.starts_with("file:///")) || uri_has_bad_segment(uri) {
            return Err("transcript media uri must be a clean absolute disk path or file:/// URI");
        }
        let Some(next_bytes) = self.total_bytes.checked_add(byte_len) else {
            return Err("transcript media byte quota exceeded");
        };
        if !tr_media_within_cap(MAX_MEDIA_TOTAL_BYTES, next_bytes) {
            return Err("transcript media byte quota exceeded");
        }
        self.total_bytes = tr_bytes_advance(self.total_bytes, next_bytes);
        self.items.push(MediaRef {
            step_index,
            mime_type: copy_str(mime_type),
            uri: copy_str(uri),
            byte_len,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn media_manifest_tracks_disk_uris_and_enforces_byte_quota() {
        let mut m = TranscriptMediaManifest::new();
        m.register_media(7, "image/png", "file:///tmp/shot.png", 1024)
            .unwrap();
        assert!(m
            .register_media(8, "image/png", "http://remote/x.png", 64)
            .is_err());
        assert!(m
            .register_media(9, "video/mp4", "/tmp/big.mp4", MAX_MEDIA_TOTAL_BYTES)
            .is_err());
    }
}
