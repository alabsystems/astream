// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `FileLog` torn-tail vs mid-log CRC corruption recovery fence
//! (`Astream.Engine.TlaEnvelopeCrcRecoveryFence`).
//!
//! Enforces `astream`'s fail-closed WAL recovery discipline:
//! - Truncation (`truncate_len <= file_len`) is ONLY admissible when an incomplete
//!   frame sits at the EOF tail (`frame_end > file_len`).
//! - Any CRC mismatch or unknown version whose declared `frame_end <= file_len`
//!   is classified as mid-log corruption (`FailClosedMidLogCorruption`) and NEVER
//!   truncated away!

#[cfg(clean_islands)]
#[path = "envelope_crc_recovery_fence_island.rs"]
mod envelope_crc_recovery_fence_island;
#[cfg(clean_islands)]
pub use envelope_crc_recovery_fence_island::{rec_truncate_clamp, rec_valid_advance};

#[cfg(not(clean_islands))]
/// Monotonically advance verified valid byte prefix during recovery scan.
#[must_use]
pub const fn rec_valid_advance(cur_valid: u64, cand_valid: u64) -> u64 {
    if cur_valid < cand_valid {
        cand_valid
    } else {
        cur_valid
    }
}

#[cfg(not(clean_islands))]
/// Clamp truncation target to `<= file_len`.
#[must_use]
pub const fn rec_truncate_clamp(cand_trunc: u64, file_len: u64) -> u64 {
    if cand_trunc < file_len {
        cand_trunc
    } else {
        file_len
    }
}

contract_fn! {
    /// True iff an unreadable/bad frame starting at `valid_offset` with declared `frame_end`
    /// is a genuine torn EOF tail (`file_len < frame_end`) rather than mid-log corruption.
    #[must_use]
    pub const fn rec_is_torn_eof_tail(file_len: u64, frame_end: u64) -> bool
    clauses [ensures result == (file_len < frame_end)]
    {
        file_len < frame_end
    }
}

/// Recovery verdict over an `astream-engine` envelope log file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvelopeRecoveryVerdict {
    Clean {
        valid_bytes: u64,
        records: u64,
    },
    TruncateTornTail {
        truncate_to: u64,
        records: u64,
    },
    FailClosedMidLogCorruption {
        corrupt_at_byte: u64,
        declared_frame_end: u64,
    },
}

/// Stateful recovery scan classifier for `FileLog::open`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvelopeCrcRecoveryFence {
    file_len: u64,
    valid_bytes: u64,
    records: u64,
}

impl EnvelopeCrcRecoveryFence {
    #[must_use]
    pub const fn new(file_len: u64) -> Self {
        Self {
            file_len,
            valid_bytes: 0,
            records: 0,
        }
    }

    #[must_use]
    pub const fn valid_bytes(&self) -> u64 {
        self.valid_bytes
    }

    #[must_use]
    pub const fn records(&self) -> u64 {
        self.records
    }

    /// Record a CRC-verified frame ending at `frame_end <= file_len`.
    pub fn observe_valid_frame(&mut self, frame_end: u64) -> bool {
        if frame_end <= self.valid_bytes || frame_end > self.file_len {
            return false;
        }
        let next_valid = rec_valid_advance(self.valid_bytes, frame_end);
        self.valid_bytes = rec_truncate_clamp(next_valid, self.file_len);
        self.records = self.records.saturating_add(1);
        true
    }

    /// Classify a frame fault at `self.valid_bytes` whose header declared `declared_frame_end`
    /// (pass `u64::MAX` when fewer than header bytes remain before `file_len`).
    #[must_use]
    pub const fn classify_fault(&self, declared_frame_end: u64) -> EnvelopeRecoveryVerdict {
        if rec_is_torn_eof_tail(self.file_len, declared_frame_end) {
            EnvelopeRecoveryVerdict::TruncateTornTail {
                truncate_to: rec_truncate_clamp(self.valid_bytes, self.file_len),
                records: self.records,
            }
        } else {
            EnvelopeRecoveryVerdict::FailClosedMidLogCorruption {
                corrupt_at_byte: self.valid_bytes,
                declared_frame_end,
            }
        }
    }

    /// Finish recovery when the scan reaches `self.valid_bytes == self.file_len` cleanly.
    #[must_use]
    pub const fn finish_clean(&self) -> EnvelopeRecoveryVerdict {
        EnvelopeRecoveryVerdict::Clean {
            valid_bytes: self.valid_bytes,
            records: self.records,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_torn_eof_tail_from_mid_log_crc_corruption() {
        let mut scan = EnvelopeCrcRecoveryFence::new(1000);
        assert!(scan.observe_valid_frame(400));
        assert!(scan.observe_valid_frame(800));

        // Frame at 800..1200 extends past EOF (1000) -> safe torn-tail truncation to 800:
        assert_eq!(
            scan.classify_fault(1200),
            EnvelopeRecoveryVerdict::TruncateTornTail {
                truncate_to: 800,
                records: 2,
            }
        );

        // Frame at 800..950 is wholly inside file (950 <= 1000) with bad CRC -> FAIL CLOSED!
        assert_eq!(
            scan.classify_fault(950),
            EnvelopeRecoveryVerdict::FailClosedMidLogCorruption {
                corrupt_at_byte: 800,
                declared_frame_end: 950,
            }
        );
    }
}
