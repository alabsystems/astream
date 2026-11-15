// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty Graphics (`APC G`) / iTerm2 (`OSC 1337`) / Sixel Inline-Media Quota & Chunk Sanitizer
//! (`Astream.Term.TlaInlineMediaGuard`).
//!
//! Protects `aterm` local and remote PTY sessions from unbounded inline-image memory exhaustion
//! and chunked-transfer state corruption:
//! - Enforces a per-image reassembly byte cap (`chunk_bytes <= max_image_bytes`); an oversized
//!   multi-chunk `APC G ... m=1` stream enters sink-discard until the final `m=0` chunk without
//!   buffering past `max_image_bytes`.
//! - Enforces a per-session retained-media RAM quota (`retained_bytes <= session_quota`),
//!   deterministically evicting FIFO-oldest completed placements before admitting a new image.
//! - Bounds cell placement dimensions (`cols * rows <= max_placement_cells`) so forged `c=99999,r=99999`
//!   headers cannot trigger multi-gigabyte grid allocations.

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "media_guard_island.rs"]
mod media_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn media_session_bytes_clamp(retained: u64, session_quota: u64) -> u64 {
    if retained < session_quota {
        retained
    } else {
        session_quota
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn media_chunk_bytes_clamp(accum: u64, max_image_bytes: u64) -> u64 {
    if accum < max_image_bytes {
        accum
    } else {
        max_image_bytes
    }
}
#[cfg(clean_islands)]
pub use media_guard_island::{media_chunk_bytes_clamp, media_session_bytes_clamp};

/// Default per-image payload cap (`8 MiB`).
pub const DEFAULT_MAX_IMAGE_BYTES: u64 = 8 * 1024 * 1024;

/// Default per-session retained inline-media quota (`32 MiB`).
pub const DEFAULT_SESSION_MEDIA_QUOTA: u64 = 32 * 1024 * 1024;

/// Default maximum grid cells covered by a single inline image (`400 * 200 = 80_000` cells).
pub const DEFAULT_MAX_PLACEMENT_CELLS: u64 = 80_000;

contract_fn! {
    /// Verified check whether an inline media placement's total cell footprint `cells` fits
    /// `max_cells` (`cells <= max_cells`), linked via `clean-kernel-defeq` to
    /// `media_dims_within_cap_isl`.
    #[must_use]
    pub const fn media_dims_within_cap(cells: u64, max_cells: u64) -> bool
    clauses [ensures result == (cells <= max_cells)]
    {
        cells <= max_cells
    }
}

/// Protocol family of an inline terminal media placement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineMediaProtocol {
    /// Kitty graphics protocol (`ESC _ G <control> ; <base64> ESC \`).
    KittyGraphics,
    /// iTerm2 inline image protocol (`ESC ] 1337 ; File=... BEL/ST`).
    Osc1337File,
    /// DEC Sixel bitmap stream (`ESC P ... q ... ESC \`).
    Sixel,
}

/// Metadata of a retained inline media object in the session cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetainedMediaEntry {
    pub media_id: u64,
    pub protocol: InlineMediaProtocol,
    pub byte_len: u64,
    pub cols: u32,
    pub rows: u32,
}

/// Decision returned when feeding a chunk or single-shot media frame to [`InlineMediaGuard`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MediaIngestVerdict {
    /// Intermediate chunk (`more_chunks == true`) accepted into staging (`accum_bytes <= max_image_bytes`).
    Staging { accum_bytes: u64 },
    /// Complete media object admitted into session cache after `evicted_count` FIFO evictions.
    Admitted {
        media_id: u64,
        byte_len: u64,
        evicted_count: usize,
    },
    /// Rejected because payload exceeded `max_image_bytes` or `session_quota`.
    RejectedOversize,
    /// Rejected because `cols * rows` exceeded `max_placement_cells` (or was `0`).
    RejectedInvalidDimensions,
}

/// Stateful inline-media quota & chunked-transfer guard for one terminal session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineMediaGuard {
    session_quota: u64,
    max_image_bytes: u64,
    max_placement_cells: u64,
    retained_bytes: u64,
    staging_bytes: u64,
    staging_overflowed: bool,
    next_id: u64,
    entries: VecDeque<RetainedMediaEntry>,
}

impl Default for InlineMediaGuard {
    fn default() -> Self {
        Self::new(
            DEFAULT_SESSION_MEDIA_QUOTA,
            DEFAULT_MAX_IMAGE_BYTES,
            DEFAULT_MAX_PLACEMENT_CELLS,
        )
    }
}

impl InlineMediaGuard {
    /// Create a session inline-media guard.
    #[must_use]
    pub fn new(session_quota: u64, max_image_bytes: u64, max_placement_cells: u64) -> Self {
        let quota = if session_quota > 1 { session_quota } else { 1 };
        let img_floor = if max_image_bytes > 1 {
            max_image_bytes
        } else {
            1
        };
        let img_cap = if img_floor < quota { img_floor } else { quota };
        let cell_cap = if max_placement_cells > 1 {
            max_placement_cells
        } else {
            1
        };
        Self {
            session_quota: quota,
            max_image_bytes: img_cap,
            max_placement_cells: cell_cap,
            retained_bytes: 0,
            staging_bytes: 0,
            staging_overflowed: false,
            next_id: 1,
            entries: VecDeque::new(),
        }
    }

    /// Total bytes currently held by retained inline images (`<= session_quota`).
    #[must_use]
    pub const fn retained_bytes(&self) -> u64 {
        self.retained_bytes
    }

    /// Bytes accumulated in the current in-progress multi-chunk transfer (`<= max_image_bytes`).
    #[must_use]
    pub const fn staging_bytes(&self) -> u64 {
        self.staging_bytes
    }

    /// Number of retained inline media placements currently cached.
    #[must_use]
    pub fn retained_count(&self) -> usize {
        self.entries.len()
    }

    /// Reset any partial multi-chunk staging state (e.g. on `RIS` / child exit / malformed stream).
    pub fn abort_staging(&mut self) {
        self.staging_bytes = 0;
        self.staging_overflowed = false;
    }

    /// Feed one chunk (or a whole single-chunk frame with `more_chunks == false`).
    pub fn ingest_chunk(
        &mut self,
        protocol: InlineMediaProtocol,
        chunk_len: u64,
        more_chunks: bool,
        cols: u32,
        rows: u32,
    ) -> MediaIngestVerdict {
        if self.staging_overflowed {
            if !more_chunks {
                self.abort_staging();
            }
            return MediaIngestVerdict::RejectedOversize;
        }

        let raw_accum = self.staging_bytes.saturating_add(chunk_len);
        let clamped_accum = media_chunk_bytes_clamp(raw_accum, self.max_image_bytes);
        if raw_accum > clamped_accum {
            self.staging_bytes = clamped_accum;
            if more_chunks {
                self.staging_overflowed = true;
            } else {
                self.abort_staging();
            }
            return MediaIngestVerdict::RejectedOversize;
        }
        self.staging_bytes = clamped_accum;

        if more_chunks {
            return MediaIngestVerdict::Staging {
                accum_bytes: self.staging_bytes,
            };
        }

        // Final chunk (`m=0`): validate placement dimensions & admit into session quota!
        let final_len = self.staging_bytes;
        self.abort_staging();

        let cells = (cols as u64).saturating_mul(rows as u64);
        if cells == 0 || !media_dims_within_cap(cells, self.max_placement_cells) {
            return MediaIngestVerdict::RejectedInvalidDimensions;
        }
        if final_len > self.session_quota {
            return MediaIngestVerdict::RejectedOversize;
        }

        let mut evicted = 0usize;
        while self.retained_bytes.saturating_add(final_len) > self.session_quota {
            let Some(old) = self.entries.pop_front() else {
                break;
            };
            self.retained_bytes = self.retained_bytes.saturating_sub(old.byte_len);
            evicted = evicted.saturating_add(1);
        }

        let next_retained = media_session_bytes_clamp(
            self.retained_bytes.saturating_add(final_len),
            self.session_quota,
        );
        self.retained_bytes = next_retained;
        let id = self.next_id;
        self.next_id = self.next_id.saturating_add(1);
        self.entries.push_back(RetainedMediaEntry {
            media_id: id,
            protocol,
            byte_len: final_len,
            cols,
            rows,
        });

        MediaIngestVerdict::Admitted {
            media_id: id,
            byte_len: final_len,
            evicted_count: evicted,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(media_session_bytes_clamp(1024, 4096), 1024);
        assert_eq!(media_session_bytes_clamp(8192, 4096), 4096);
        assert_eq!(media_chunk_bytes_clamp(500, 1000), 500);
        assert_eq!(media_chunk_bytes_clamp(2000, 1000), 1000);
        assert!(media_dims_within_cap(800, 800));
        assert!(!media_dims_within_cap(801, 800));
    }

    #[test]
    fn enforces_chunk_cap_sink_discard_and_fifo_session_quota_eviction() {
        let mut g = InlineMediaGuard::new(1_000, 600, 400);

        // Oversized multi-chunk Kitty stream (`400 + 300 > 600`) sinks until `m=0`, then recovers!
        assert_eq!(
            g.ingest_chunk(InlineMediaProtocol::KittyGraphics, 400, true, 10, 10),
            MediaIngestVerdict::Staging { accum_bytes: 400 }
        );
        assert_eq!(
            g.ingest_chunk(InlineMediaProtocol::KittyGraphics, 300, true, 10, 10),
            MediaIngestVerdict::RejectedOversize
        );
        assert_eq!(
            g.ingest_chunk(InlineMediaProtocol::KittyGraphics, 50, false, 10, 10),
            MediaIngestVerdict::RejectedOversize
        );

        // Valid 600-byte image #1 followed by 600-byte image #2 evicts image #1 to stay <= 1_000!
        assert_eq!(
            g.ingest_chunk(InlineMediaProtocol::Osc1337File, 600, false, 20, 10),
            MediaIngestVerdict::Admitted {
                media_id: 1,
                byte_len: 600,
                evicted_count: 0,
            }
        );
        assert_eq!(
            g.ingest_chunk(InlineMediaProtocol::Osc1337File, 600, false, 20, 10),
            MediaIngestVerdict::Admitted {
                media_id: 2,
                byte_len: 600,
                evicted_count: 1,
            }
        );
        assert_eq!(g.retained_bytes(), 600);
        assert_eq!(g.retained_count(), 1);
    }
}
