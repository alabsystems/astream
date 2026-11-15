// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Memory-bounded cold-prefix payload eviction and on-demand disk-slice reader
//! (`docs/DESIGN-aterm-fabric.md` §13 long-lived fleet RSS bound).
//!
//! When an `aterm` broker runs continuously for days, keeping every historical
//! record payload in RAM scales RSS with total retained disk bytes rather than
//! active working-set size. [`ColdPageIndex`] decouples historical log offsets
//! from resident RAM:
//! - Records at `seq >= hot_floor` stay resident in RAM up to `resident_budget_bytes`
//!   (clamped via Clean-origin [`cold_resident_clamp`]).
//! - As new records arrive and push resident payload bytes past `resident_budget_bytes`,
//!   `hot_floor` advances monotonically via [`cold_hot_floor_advance`], evicting
//!   cold payload `Vec<u8>` buffers while retaining compact 24-byte [`ColdRecordSpan`]
//!   descriptors `(seq, file_offset, frame_len)`.
//! - Cold reads (`read_record_frame`) serve exact frame slices directly from the
//!   immutable prefix of `<log>` via positional `read_exact_at` (Unix `pread`),
//!   verifying `Frame::decode` CRC-32 integrity on every cold fault-in!

use astream_wire::{Offset, HEADER_SIZE};
use std::collections::VecDeque;
use std::fs::File;
use std::io;

#[cfg(clean_islands)]
#[path = "cold_page_island.rs"]
mod cold_page_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn cold_hot_floor_advance(cur_floor: u64, proposed_floor: u64) -> u64 {
    if cur_floor < proposed_floor {
        proposed_floor
    } else {
        cur_floor
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cold_resident_clamp(resident_bytes: u64, budget_bytes: u64) -> u64 {
    if resident_bytes < budget_bytes {
        resident_bytes
    } else {
        budget_bytes
    }
}
#[cfg(clean_islands)]
pub use cold_page_island::{cold_hot_floor_advance, cold_resident_clamp};

contract_fn! {
    /// Contracted check that offset `seq` lies in the evicted cold prefix (`seq < hot_floor`).
    #[must_use]
    pub const fn cold_is_evicted(seq: u64, hot_floor: u64) -> bool
    clauses [ensures result == (seq < hot_floor)]
    {
        seq < hot_floor
    }
}

/// Hard cap on a single cold frame read (`16 MiB` + header).
pub const MAX_COLD_FRAME_BYTES: usize = 16 * 1024 * 1024 + HEADER_SIZE;

/// Compact disk extent descriptor for an indexed log record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ColdRecordSpan {
    pub seq: Offset,
    pub file_offset: u64,
    pub frame_len: u32,
}

/// Indexed entry holding both disk location and optional resident frame payload.
#[derive(Debug, Clone)]
struct ResidentEntry {
    span: ColdRecordSpan,
    payload: Option<Vec<u8>>,
}

/// Memory-bounded log payload cache backed by positional disk reads below `hot_floor`.
#[derive(Debug)]
pub struct ColdPageIndex {
    base_seq: u64,
    hot_floor: u64,
    resident_bytes: u64,
    budget_bytes: u64,
    entries: VecDeque<ResidentEntry>,
}

impl ColdPageIndex {
    pub fn new(base_seq: Offset, budget_bytes: u64) -> Self {
        Self {
            base_seq: base_seq.0,
            hot_floor: base_seq.0,
            resident_bytes: 0,
            budget_bytes,
            entries: VecDeque::new(),
        }
    }

    /// Lowest offset whose payload is still resident in RAM.
    pub fn hot_floor(&self) -> Offset {
        Offset(self.hot_floor)
    }

    /// Current resident payload bytes (`<= budget_bytes` once eviction settles).
    pub fn resident_bytes(&self) -> u64 {
        self.resident_bytes
    }

    /// Configured RAM budget in bytes.
    pub fn budget_bytes(&self) -> u64 {
        self.budget_bytes
    }

    /// Append the next sequential frame `(span, decoded_payload)` and evict cold
    /// prefix payloads until `resident_bytes <= budget_bytes`.
    pub fn push_record(&mut self, span: ColdRecordSpan, payload: Vec<u8>) -> io::Result<()> {
        let expected_seq = self.base_seq.saturating_add(self.entries.len() as u64);
        if span.seq.0 != expected_seq {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "non-dense ColdPageIndex append: expected {}, got {}",
                    expected_seq, span.seq.0
                ),
            ));
        }
        let p_len = payload.len() as u64;
        if p_len > self.budget_bytes {
            // Single record exceeds RAM budget: evict any older hot payloads below the
            // advancing `hot_floor` and index this record's disk span immediately as cold.
            let mut idx = 0usize;
            while let Some(entry) = self.entries.get_mut(idx) {
                let _ = entry.payload.take();
                idx = idx.saturating_add(1);
            }
            self.resident_bytes = 0;
            let next_floor = span.seq.0.saturating_add(1);
            self.hot_floor = cold_hot_floor_advance(self.hot_floor, next_floor);
            self.entries.push_back(ResidentEntry {
                span,
                payload: None,
            });
            return Ok(());
        }

        self.resident_bytes = self.resident_bytes.saturating_add(p_len);
        self.entries.push_back(ResidentEntry {
            span,
            payload: Some(payload),
        });
        self.evict_to_budget();
        Ok(())
    }

    fn evict_to_budget(&mut self) {
        while self.resident_bytes > self.budget_bytes {
            if self.hot_floor < self.base_seq {
                self.hot_floor = self.base_seq;
            }
            let idx = self.hot_floor.saturating_sub(self.base_seq) as usize;
            let Some(entry) = self.entries.get_mut(idx) else {
                break;
            };
            if let Some(bytes) = entry.payload.take() {
                self.resident_bytes = self.resident_bytes.saturating_sub(bytes.len() as u64);
            }
            let proposed = entry.span.seq.0.saturating_add(1);
            self.hot_floor = cold_hot_floor_advance(self.hot_floor, proposed);
        }
        self.resident_bytes = cold_resident_clamp(self.resident_bytes, self.budget_bytes);
    }

    /// Drop descriptors strictly below `new_base` after a log retention cut.
    pub fn retain_from(&mut self, new_base: Offset) {
        while let Some(front) = self.entries.front() {
            if front.span.seq.0 >= new_base.0 {
                break;
            }
            if let Some(entry) = self.entries.pop_front() {
                if let Some(bytes) = entry.payload {
                    self.resident_bytes = self.resident_bytes.saturating_sub(bytes.len() as u64);
                }
            }
        }
        if new_base.0 > self.base_seq {
            self.base_seq = new_base.0;
        }
        self.hot_floor = cold_hot_floor_advance(self.hot_floor, self.base_seq);
        self.resident_bytes = cold_resident_clamp(self.resident_bytes, self.budget_bytes);
    }

    /// Read the verified frame payload at `seq`: returns a clone from RAM when
    /// `!cold_is_evicted(seq.0, self.hot_floor)`, or faults the frame in from `log_file`
    /// and verifies its `Frame` header + CRC-32 when cold.
    pub fn read_payload(&self, seq: Offset, log_file: &File) -> io::Result<Vec<u8>> {
        if seq.0 < self.base_seq {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "offset precedes retained base",
            ));
        }
        let idx = (seq.0 - self.base_seq) as usize;
        let Some(entry) = self.entries.get(idx) else {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "offset at or past head",
            ));
        };
        if !cold_is_evicted(seq.0, self.hot_floor) {
            if let Some(bytes) = &entry.payload {
                return Ok(bytes.clone());
            }
        }
        read_cold_frame_payload(log_file, entry.span)
    }
}

fn read_cold_frame_payload(file: &File, span: ColdRecordSpan) -> io::Result<Vec<u8>> {
    let len = span.frame_len as usize;
    if !matches!(len, HEADER_SIZE..=MAX_COLD_FRAME_BYTES) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid cold frame length",
        ));
    }
    let bounded_len = if len < MAX_COLD_FRAME_BYTES {
        len
    } else {
        MAX_COLD_FRAME_BYTES
    };
    let mut raw = vec![0u8; bounded_len];
    read_exact_at_portable(file, &mut raw, span.file_offset)?;
    let (payload, used) = match astream_wire::frame::decode_frame_slice(&raw) {
        Ok(Some(pair)) => pair,
        Ok(None) => {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                format!("truncated cold frame at offset {}", span.seq.0),
            ));
        }
        Err(e) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "cold frame CRC/header failure at offset {}: {e:?}",
                    span.seq.0
                ),
            ));
        }
    };
    if used != len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "cold frame length mismatch",
        ));
    }
    Ok(payload.to_vec())
}

#[cfg(unix)]
fn read_exact_at_portable(file: &File, buf: &mut [u8], offset: u64) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.read_exact_at(buf, offset)
}

#[cfg(not(unix))]
fn read_exact_at_portable(file: &File, buf: &mut [u8], offset: u64) -> io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    let mut clone = file.try_clone()?;
    clone.seek(SeekFrom::Start(offset))?;
    clone.read_exact(buf)
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_wire::Frame;
    use std::io::Write;

    #[test]
    fn oversized_record_evicts_older_resident_payloads_before_advancing_hot_floor() {
        let path =
            std::env::temp_dir().join(format!("asb_cold_oversized_{}.log", std::process::id()));
        let _ = std::fs::remove_file(&path);
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&path)
            .unwrap();

        let mut idx = ColdPageIndex::new(Offset(0), 64);
        let mut file_pos = 0u64;
        let small = vec![b's'; 32];
        let wire0 = Frame::new(small.clone()).encode().unwrap();
        f.write_all(&wire0).unwrap();
        idx.push_record(
            ColdRecordSpan {
                seq: Offset(0),
                file_offset: file_pos,
                frame_len: wire0.len() as u32,
            },
            small.clone(),
        )
        .unwrap();
        file_pos += wire0.len() as u64;
        assert_eq!(idx.resident_bytes(), 32);

        let huge = vec![b'H'; 96];
        let wire1 = Frame::new(huge.clone()).encode().unwrap();
        f.write_all(&wire1).unwrap();
        idx.push_record(
            ColdRecordSpan {
                seq: Offset(1),
                file_offset: file_pos,
                frame_len: wire1.len() as u32,
            },
            huge.clone(),
        )
        .unwrap();

        assert_eq!(idx.hot_floor(), Offset(2));
        assert_eq!(idx.resident_bytes(), 0);
        assert!(idx.entries.iter().all(|e| e.payload.is_none()));
        assert_eq!(idx.read_payload(Offset(0), &f).unwrap(), small);
        assert_eq!(idx.read_payload(Offset(1), &f).unwrap(), huge);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn evicts_cold_prefix_to_budget_and_faults_verified_frames_from_disk() {
        let path = std::env::temp_dir().join(format!("asb_cold_test_{}.log", std::process::id()));
        let _ = std::fs::remove_file(&path);
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&path)
            .unwrap();

        // Budget allows ~2 payloads of 64 bytes each.
        let mut idx = ColdPageIndex::new(Offset(0), 128);
        let mut file_pos = 0u64;
        for seq in 0..6u64 {
            let payload = vec![(seq as u8) + b'A'; 64];
            let wire = Frame::new(payload.clone()).encode().unwrap();
            f.write_all(&wire).unwrap();
            idx.push_record(
                ColdRecordSpan {
                    seq: Offset(seq),
                    file_offset: file_pos,
                    frame_len: wire.len() as u32,
                },
                payload,
            )
            .unwrap();
            file_pos += wire.len() as u64;
            assert!(idx.resident_bytes() <= 128);
        }
        assert_eq!(idx.hot_floor(), Offset(4));
        assert!(cold_is_evicted(0, idx.hot_floor().0));
        assert!(!cold_is_evicted(4, idx.hot_floor().0));

        // Both cold (0..4) and hot (4..6) offsets read back byte-identically!
        for seq in 0..6u64 {
            let got = idx.read_payload(Offset(seq), &f).unwrap();
            assert_eq!(got, vec![(seq as u8) + b'A'; 64]);
        }
        let _ = std::fs::remove_file(&path);
    }
}
