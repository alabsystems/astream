// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded terminal flight recorder (`term/out`) with crash-pinning freeze semantics
//! (`DESIGN-aterm-fabric.md` §3.3 / §11.2 / line 4046, `Astream.Engine.TlaFlightRecorder`).
//!
//! Continuously records terminal output chunks `(offset, bt_ms, bytes)` inside a bounded
//! memory budget (`<= MAX_FLIGHT_RING_BYTES`), evicting oldest chunks only while unpinned
//! (`flight_evict_permitted`), and freezing eviction across `[pin_base..pin_head]` when
//! `pin(reason)` is triggered (e.g. crash / signal / `aterm-link pin`) until explicitly
//! released, with lossless export/import over `astream_wire::steps` records.

use astream_wire::steps::{encode_step, scan_steps_from, StepEnd};
use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "flight_recorder_island.rs"]
mod flight_recorder_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flight_ring_bytes_clamp(cur_bytes: u64, max_bytes: u64) -> u64 {
    if cur_bytes < max_bytes {
        cur_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flight_pin_epoch_advance(prev_epoch: u64, cand_epoch: u64) -> u64 {
    if prev_epoch < cand_epoch {
        cand_epoch
    } else {
        prev_epoch
    }
}
#[cfg(clean_islands)]
pub use flight_recorder_island::{flight_pin_epoch_advance, flight_ring_bytes_clamp};

/// Hard ceiling on flight-recorder ring capacity (`4 MiB`).
pub const MAX_FLIGHT_RING_BYTES: u64 = 4 * 1024 * 1024;

/// Maximum byte size of a single chunk admitted into the flight recorder (`256 KiB`).
pub const MAX_FLIGHT_CHUNK_BYTES: usize = 262_144;

contract_fn! {
    /// Verified check that ring eviction is permitted (`!pinned && cur_bytes > max_bytes`),
    /// linked via `clean-kernel-defeq` to `flight_evict_permitted_isl`.
    #[must_use]
    pub const fn flight_evict_permitted(pinned: bool, cur_bytes: u64, max_bytes: u64) -> bool
    clauses [ensures result == (!pinned && max_bytes < cur_bytes)]
    {
        !pinned && max_bytes < cur_bytes
    }
}

/// One recorded terminal output chunk in [`FlightRecorder`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlightChunk {
    /// Monotone stream offset of this chunk.
    pub offset: u64,
    /// Monotone broker/host timestamp in milliseconds.
    pub bt_ms: u64,
    /// Raw terminal output bytes.
    pub bytes: Vec<u8>,
}

/// Active freeze pin preventing eviction of pre-incident context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlightPin {
    /// Monotone pin epoch (`>= 1`).
    pub epoch: u64,
    /// Lowest retained offset frozen at pin time.
    pub base_offset: u64,
    /// Highest retained offset frozen at pin time.
    pub head_offset: u64,
    /// Human/supervisor reason string.
    pub reason: String,
}

/// Bounded circular flight recorder with freeze-on-pin crash capture.
#[derive(Debug, Clone)]
pub struct FlightRecorder {
    max_bytes: u64,
    cur_bytes: u64,
    evicted_chunks: u64,
    pin_epoch: u64,
    active_pin: Option<FlightPin>,
    chunks: VecDeque<FlightChunk>,
}

impl FlightRecorder {
    /// Construct a flight recorder with byte budget `max_bytes`
    /// (clamped into `1..=MAX_FLIGHT_RING_BYTES` via [`flight_ring_bytes_clamp`]).
    #[must_use]
    pub fn new(max_bytes: u64) -> Self {
        let clamped = flight_ring_bytes_clamp(max_bytes, MAX_FLIGHT_RING_BYTES);
        let effective = if clamped == 0 { 1024 } else { clamped };
        Self {
            max_bytes: effective,
            cur_bytes: 0,
            evicted_chunks: 0,
            pin_epoch: 0,
            active_pin: None,
            chunks: VecDeque::new(),
        }
    }

    /// Configured byte ceiling (`<= MAX_FLIGHT_RING_BYTES`).
    #[must_use]
    pub const fn max_bytes(&self) -> u64 {
        self.max_bytes
    }

    /// Current retained payload bytes (`<= max_bytes`).
    #[must_use]
    pub const fn retained_bytes(&self) -> u64 {
        self.cur_bytes
    }

    /// Total chunks evicted while unpinned since construction.
    #[must_use]
    pub const fn evicted_chunks(&self) -> u64 {
        self.evicted_chunks
    }

    /// Current active freeze pin, if any.
    #[must_use]
    pub const fn active_pin(&self) -> Option<&FlightPin> {
        self.active_pin.as_ref()
    }

    /// Monotone pin epoch counter.
    #[must_use]
    pub const fn pin_epoch(&self) -> u64 {
        self.pin_epoch
    }

    /// Append a terminal output chunk `(offset, bt_ms, bytes)`:
    /// - Enforces strict offset monotonicity.
    /// - While unpinned, evicts oldest chunks until `cur_bytes <= max_bytes`.
    /// - While pinned, refuses writes that would exceed `max_bytes` so pinned pre-crash
    ///   chunks are NEVER evicted!
    pub fn record_chunk(
        &mut self,
        offset: u64,
        bt_ms: u64,
        bytes: &[u8],
    ) -> Result<(), &'static str> {
        if bytes.len() > MAX_FLIGHT_CHUNK_BYTES || (bytes.len() as u64) > self.max_bytes {
            return Err("chunk exceeds flight recorder capacity");
        }
        if let Some(back) = self.chunks.back() {
            if offset <= back.offset {
                return Err("non-monotone flight chunk offset");
            }
        }
        let add_len = bytes.len() as u64;
        let next_total = self.cur_bytes.saturating_add(add_len);
        let is_pinned = self.active_pin.is_some();

        if is_pinned && next_total > self.max_bytes {
            return Err("flight recorder pinned and at byte capacity");
        }

        let mut chunk_bytes = Vec::new();
        chunk_bytes.extend_from_slice(bytes);
        self.chunks.push_back(FlightChunk {
            offset,
            bt_ms,
            bytes: chunk_bytes,
        });
        let mut raw_cur = next_total;
        while flight_evict_permitted(is_pinned, raw_cur, self.max_bytes) {
            let Some(dropped) = self.chunks.pop_front() else {
                break;
            };
            raw_cur = raw_cur.saturating_sub(dropped.bytes.len() as u64);
            self.evicted_chunks = self.evicted_chunks.saturating_add(1);
        }
        self.cur_bytes = flight_ring_bytes_clamp(raw_cur, self.max_bytes);
        Ok(())
    }

    /// Freeze eviction over the current retained window and advance `pin_epoch` monotonically.
    pub fn pin(&mut self, reason: &str) -> FlightPin {
        let cand = self.pin_epoch.saturating_add(1);
        self.pin_epoch = flight_pin_epoch_advance(self.pin_epoch, cand);
        let base_offset = match self.chunks.front() {
            Some(c) => c.offset,
            None => 0,
        };
        let head_offset = match self.chunks.back() {
            Some(c) => c.offset.saturating_add(1),
            None => 0,
        };
        let mut owned_reason = String::new();
        owned_reason.push_str(reason);
        let p = FlightPin {
            epoch: self.pin_epoch,
            base_offset,
            head_offset,
            reason: owned_reason,
        };
        self.active_pin = Some(p.clone());
        p
    }

    /// Release any active freeze pin, allowing circular ring eviction to resume.
    pub fn unpin(&mut self) -> Option<FlightPin> {
        self.active_pin.take()
    }

    /// Export all currently retained chunks as contiguous `astream_wire::steps` records
    /// starting at step `0`, where each body carries `[offset: u64 LE][bt_ms: u64 LE][bytes..]`.
    pub fn export_steps(&self) -> Result<Vec<u8>, &'static str> {
        let out_cap = if (self.cur_bytes as usize) < 65_536 {
            self.cur_bytes as usize
        } else {
            65_536
        };
        let mut out = {
            let _ = out_cap;
            Vec::new()
        };
        let mut step_idx = 0u64;
        for chunk in &self.chunks {
            let mut body = Vec::new();
            body.extend_from_slice(&chunk.offset.to_le_bytes());
            body.extend_from_slice(&chunk.bt_ms.to_le_bytes());
            body.extend_from_slice(&chunk.bytes);
            let Ok(framed) = encode_step(step_idx, &body) else {
                return Err("failed to frame flight chunk step");
            };
            out.extend_from_slice(&framed);
            step_idx = step_idx.saturating_add(1);
        }
        Ok(out)
    }

    /// Decode exported `astream_wire::steps` bytes back into ordered [`FlightChunk`] records.
    pub fn import_steps(bytes: &[u8]) -> Result<Vec<FlightChunk>, &'static str> {
        let scan = scan_steps_from(bytes, 0);
        if scan.end != StepEnd::Clean {
            return Err("corrupt or torn flight-recorder step stream");
        }
        let rec_cap = if scan.steps.len() < 4096 {
            scan.steps.len()
        } else {
            4096
        };
        let mut out = {
            let _ = rec_cap;
            Vec::new()
        };
        let mut i = 0usize;
        let mut prev_offset: Option<u64> = None;
        while let Some((_, range)) = scan.steps.get(i) {
            let Some(body) = bytes.get(range.start..range.end) else {
                return Err("step range out of bounds");
            };
            let &[o0, o1, o2, o3, o4, o5, o6, o7, t0, t1, t2, t3, t4, t5, t6, t7, ref payload @ ..] =
                body
            else {
                return Err("truncated flight chunk header");
            };
            let offset = u64::from_le_bytes([o0, o1, o2, o3, o4, o5, o6, o7]);
            if let Some(prev) = prev_offset {
                if offset <= prev {
                    return Err("non-monotone flight chunk offset");
                }
            }
            prev_offset = Some(offset);
            let bt_ms = u64::from_le_bytes([t0, t1, t2, t3, t4, t5, t6, t7]);
            let mut payload_vec = Vec::new();
            payload_vec.extend_from_slice(payload);
            out.push(FlightChunk {
                offset,
                bt_ms,
                bytes: payload_vec,
            });
            i = i.saturating_add(1);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_oldest_when_unpinned_freezes_when_pinned_and_round_trips_steps() {
        let mut rec = FlightRecorder::new(16);
        rec.record_chunk(10, 1000, b"aaaaaa").unwrap();
        rec.record_chunk(11, 1005, b"bbbbbb").unwrap();
        // Adding 6 more bytes (total 18 > 16) evicts chunk 10 while unpinned.
        rec.record_chunk(12, 1010, b"cccccc").unwrap();
        assert_eq!(rec.evicted_chunks(), 1);
        assert_eq!(rec.retained_bytes(), 12);

        // Pin on crash!
        let pin = rec.pin("panic in worker");
        assert_eq!(pin.epoch, 1);
        assert_eq!(pin.base_offset, 11);
        assert_eq!(pin.head_offset, 13);

        // Overflowing while pinned is refused rather than evicting chunk 11!
        assert!(rec.record_chunk(13, 1015, b"dddddd").is_err());
        assert_eq!(rec.evicted_chunks(), 1);

        // Export & import over `astream_wire::steps` is lossless.
        let exported = rec.export_steps().unwrap();
        let imported = FlightRecorder::import_steps(&exported).unwrap();
        assert_eq!(imported.len(), 2);
        assert_eq!(imported[0].offset, 11);
        assert_eq!(imported[0].bytes, b"bbbbbb");
        assert_eq!(imported[1].offset, 12);
        assert_eq!(imported[1].bytes, b"cccccc");

        // Unpin resumes eviction.
        assert!(rec.unpin().is_some());
        rec.record_chunk(13, 1015, b"dddddd").unwrap();
        assert_eq!(rec.evicted_chunks(), 2);
    }
}
