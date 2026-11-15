// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Rolling IEEE CRC-32 (`astream_wire::crc32_ieee_update`) checkpoint verifier over appended
//! `.jsonl` trajectory lines (`Astream.Transcript.TlaStepCrcCheckpoint`).

use astream_wire::crc32_ieee_update;

#[cfg(clean_islands)]
#[path = "step_crc_checkpoint_island.rs"]
mod step_crc_checkpoint_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_chunk_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_sealed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use step_crc_checkpoint_island::{tr_chunk_clamp, tr_sealed_advance};

/// Maximum single JSONL step byte length hashed in one rolling update (`16` MiB).
pub const MAX_STEP_LINE_BYTES: u64 = 16 * 1024 * 1024;

contract_fn! {
    /// Verified checkpoint step bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tr_crc_matches_isl`.
    #[must_use]
    pub const fn tr_crc_matches(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Rolling CRC-32 accumulator sealing append-only JSONL transcript checkpoints.
#[derive(Debug, Clone)]
pub struct RollingTranscriptCrc {
    state: u32,
    sealed_lines: u64,
}

impl Default for RollingTranscriptCrc {
    fn default() -> Self {
        Self::new()
    }
}

impl RollingTranscriptCrc {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            state: 0,
            sealed_lines: 0,
        }
    }

    pub fn append_line(&mut self, jsonl_line: &[u8]) -> Result<u32, &'static str> {
        let cap = tr_chunk_clamp(MAX_STEP_LINE_BYTES, MAX_STEP_LINE_BYTES);
        if !tr_crc_matches(cap, jsonl_line.len() as u64) {
            return Err("JSONL step line exceeds 16 MiB checkpoint ceiling");
        }
        self.state = crc32_step_wrap(self.state, jsonl_line);
        self.sealed_lines =
            tr_sealed_advance(self.sealed_lines, self.sealed_lines.saturating_add(1));
        Ok(self.current_crc32())
    }

    #[must_use]
    pub const fn current_crc32(&self) -> u32 {
        self.state
    }
}

#[inline(never)]
fn crc32_step_wrap(state: u32, chunk: &[u8]) -> u32 {
    crc32_ieee_update(state, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_wire::crc32_ieee;

    #[test]
    fn rolling_transcript_crc_matches_concatenated_ieee_crc32_and_detects_bitflip() {
        let mut r = RollingTranscriptCrc::new();
        r.append_line(b"{\"step_index\":0}\n").unwrap();
        let digest = r.append_line(b"{\"step_index\":1}\n").unwrap();
        assert_eq!(
            digest,
            crc32_ieee(b"{\"step_index\":0}\n{\"step_index\":1}\n")
        );
    }
}
