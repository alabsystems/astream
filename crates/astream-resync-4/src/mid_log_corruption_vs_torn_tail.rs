// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Mid-log rotted-length/CRC corruption vs power-loss torn-tail & `resume_from` truncate barrier
//! (`Astream.Engine.TlaMidLogCorruptionVsTornTail`).
//!
//! Guards three engine/durable-log recovery invariants:
//! 1. A rotted length or CRC mid-log (where non-zero committed bytes exist past the bad header)
//!    MUST return `MidLogCorruptionFault` and NEVER silently truncate acked records after it,
//! 2. A partial frame at EOF or followed solely by zero-filled preallocated extents is classified
//!    as `TornPowerLossTail { truncate_to_bytes }`,
//! 3. `Session::resume_from` MUST NOT append until any torn tail has been truncated AND both the
//!    log file and parent directory have been fsynced (`RefusedAppendOverUntruncatedTail`)!

#[cfg(clean_islands)]
#[path = "mid_log_corruption_vs_torn_tail_island.rs"]
mod mid_log_corruption_vs_torn_tail_island;
#[cfg(clean_islands)]
pub use mid_log_corruption_vs_torn_tail_island::{
    resume_epoch_advance_b140, valid_prefix_bytes_clamp_b140,
};

#[cfg(not(clean_islands))]
/// Clamp the verified prefix byte offset to `file_len_bytes`.
#[must_use]
pub const fn valid_prefix_bytes_clamp_b140(valid_bytes: u64, file_len_bytes: u64) -> u64 {
    if valid_bytes < file_len_bytes {
        valid_bytes
    } else {
        file_len_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the session recovery epoch.
#[must_use]
pub const fn resume_epoch_advance_b140(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// Truncation to `valid_prefix_bytes` is safe ONLY for an incomplete frame at EOF or followed
    /// exclusively by zero-filled preallocated extents (`!non_zero_committed_bytes_after`).
    #[must_use]
    pub const fn tail_truncation_safe_b140(
        incomplete_at_eof_or_zero_extent: bool,
        non_zero_committed_bytes_after: bool,
    ) -> bool
    clauses [ensures result == (incomplete_at_eof_or_zero_extent && !non_zero_committed_bytes_after)]
    {
        incomplete_at_eof_or_zero_extent && !non_zero_committed_bytes_after
    }
}

/// Recovery scan classification and `resume_from` barrier outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryTruncateDecision {
    CleanReadyToAppend {
        append_at_byte: u64,
        resume_epoch: u64,
    },
    TornPowerLossTailRequiresTruncateAndSync {
        truncate_to_bytes: u64,
        discarded_tail_bytes: u64,
    },
    MidLogCorruptionFault {
        corrupt_byte_offset: u64,
        file_len_bytes: u64,
    },
    RefusedAppendOverUntruncatedTail,
}

/// Recovery gate preventing silent mid-log truncation and mid-frame `resume_from` appends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogRecoveryTruncateGate {
    valid_prefix_bytes: u64,
    file_len_bytes: u64,
    resume_epoch: u64,
    truncated_and_synced: bool,
    corrupted: bool,
}

impl LogRecoveryTruncateGate {
    #[must_use]
    pub fn classify_open_scan(
        raw_valid_prefix_bytes: u64,
        file_len_bytes: u64,
        incomplete_at_eof_or_zero_extent: bool,
        non_zero_committed_bytes_after: bool,
        initial_epoch: u64,
    ) -> (Self, RecoveryTruncateDecision) {
        let valid_prefix = valid_prefix_bytes_clamp_b140(raw_valid_prefix_bytes, file_len_bytes);
        if valid_prefix == file_len_bytes && !non_zero_committed_bytes_after {
            let gate = Self {
                valid_prefix_bytes: valid_prefix,
                file_len_bytes,
                resume_epoch: initial_epoch,
                truncated_and_synced: true,
                corrupted: false,
            };
            return (
                gate,
                RecoveryTruncateDecision::CleanReadyToAppend {
                    append_at_byte: valid_prefix,
                    resume_epoch: initial_epoch,
                },
            );
        }
        if tail_truncation_safe_b140(
            incomplete_at_eof_or_zero_extent,
            non_zero_committed_bytes_after,
        ) {
            let gate = Self {
                valid_prefix_bytes: valid_prefix,
                file_len_bytes,
                resume_epoch: initial_epoch,
                truncated_and_synced: false,
                corrupted: false,
            };
            (
                gate,
                RecoveryTruncateDecision::TornPowerLossTailRequiresTruncateAndSync {
                    truncate_to_bytes: valid_prefix,
                    discarded_tail_bytes: file_len_bytes.saturating_sub(valid_prefix),
                },
            )
        } else {
            let gate = Self {
                valid_prefix_bytes: valid_prefix,
                file_len_bytes,
                resume_epoch: initial_epoch,
                truncated_and_synced: false,
                corrupted: true,
            };
            (
                gate,
                RecoveryTruncateDecision::MidLogCorruptionFault {
                    corrupt_byte_offset: valid_prefix,
                    file_len_bytes,
                },
            )
        }
    }

    pub fn complete_truncate_and_fsync(&mut self, cand_epoch: u64) -> RecoveryTruncateDecision {
        if self.corrupted {
            return RecoveryTruncateDecision::MidLogCorruptionFault {
                corrupt_byte_offset: self.valid_prefix_bytes,
                file_len_bytes: self.file_len_bytes,
            };
        }
        self.resume_epoch = resume_epoch_advance_b140(self.resume_epoch, cand_epoch);
        self.file_len_bytes = self.valid_prefix_bytes;
        self.truncated_and_synced = true;
        RecoveryTruncateDecision::CleanReadyToAppend {
            append_at_byte: self.valid_prefix_bytes,
            resume_epoch: self.resume_epoch,
        }
    }

    #[must_use]
    pub const fn admit_resume_append(&self) -> RecoveryTruncateDecision {
        if self.corrupted {
            RecoveryTruncateDecision::MidLogCorruptionFault {
                corrupt_byte_offset: self.valid_prefix_bytes,
                file_len_bytes: self.file_len_bytes,
            }
        } else if !self.truncated_and_synced {
            RecoveryTruncateDecision::RefusedAppendOverUntruncatedTail
        } else {
            RecoveryTruncateDecision::CleanReadyToAppend {
                append_at_byte: valid_prefix_bytes_clamp_b140(
                    self.valid_prefix_bytes,
                    self.file_len_bytes,
                ),
                resume_epoch: self.resume_epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mid_log_rotted_length_never_truncates_and_torn_tail_blocks_append_until_synced() {
        // Rotted length at 4096 followed by committed records up to 65536 -> MidLogCorruptionFault!
        let (corrupt_gate, d1) =
            LogRecoveryTruncateGate::classify_open_scan(4_096, 65_536, true, true, 1);
        assert_eq!(
            d1,
            RecoveryTruncateDecision::MidLogCorruptionFault {
                corrupt_byte_offset: 4_096,
                file_len_bytes: 65_536
            }
        );
        assert_eq!(corrupt_gate.admit_resume_append(), d1);

        // Power-loss torn tail + zeroed extents at 8192..12288 -> requires truncate + fsync before append!
        let (mut torn_gate, d2) =
            LogRecoveryTruncateGate::classify_open_scan(8_192, 12_288, true, false, 1);
        assert_eq!(
            d2,
            RecoveryTruncateDecision::TornPowerLossTailRequiresTruncateAndSync {
                truncate_to_bytes: 8_192,
                discarded_tail_bytes: 4_096
            }
        );
        assert_eq!(
            torn_gate.admit_resume_append(),
            RecoveryTruncateDecision::RefusedAppendOverUntruncatedTail
        );
        assert_eq!(
            torn_gate.complete_truncate_and_fsync(2),
            RecoveryTruncateDecision::CleanReadyToAppend {
                append_at_byte: 8_192,
                resume_epoch: 2
            }
        );
    }
}
