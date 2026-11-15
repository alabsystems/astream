// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Newer `BREC_VERSION` (`> 2`) `Unsupported` non-truncation guard for `open` & `open_repair`
//! (`evidence/manifest.toml` `broker.log-newer-format-refused`;
//! `Astream.Broker.TlaNewerBrecVersionUnsupportedGuard`).
//!
//! Enforces the record-version forward-safety law:
//! - Inside a CRC-valid frame, a record version byte `rec_version > BREC_VERSION` (`2`) is a
//!   NEWER format (`RefusedUnsupportedNewerFormat`), NEVER corruption: BOTH `open` and
//!   `open_repair` leave the log file byte-identical (zero truncation!),
//! - Conversely, an older unsupported record format (`rec_version < BREC_VERSION`), bad CRC,
//!   or length past EOF — even behind a valid newer-format record or vice versa — is classified
//!   accurately: real corruption before any newer-format frame is `InvalidData` and `open_repair`
//!   truncates to `intact_prefix_bytes <= file_len`!

#[cfg(clean_islands)]
#[path = "newer_brec_version_unsupported_guard_island.rs"]
mod newer_brec_version_unsupported_guard_island;
#[cfg(clean_islands)]
pub use newer_brec_version_unsupported_guard_island::{
    intact_prefix_advance_b148, repair_cut_clamp_b148,
};

/// Current broker record wire format version (`BREC_VERSION = 2`).
pub const SUPPORTED_BREC_VERSION: u64 = 2;

#[cfg(not(clean_islands))]
/// Clamp repair truncation target so it never exceeds `file_len`.
#[must_use]
pub const fn repair_cut_clamp_b148(cand_cut: u64, file_len: u64) -> u64 {
    if cand_cut < file_len {
        cand_cut
    } else {
        file_len
    }
}

#[cfg(not(clean_islands))]
/// Advance verified intact byte prefix monotonically during sequential scan.
#[must_use]
pub const fn intact_prefix_advance_b148(cur_intact: u64, cand_intact: u64) -> u64 {
    if cur_intact < cand_intact {
        cand_intact
    } else {
        cur_intact
    }
}

contract_fn! {
    /// True iff a CRC-valid frame carries a record version strictly newer than `supported_ver`.
    #[must_use]
    pub const fn is_newer_brec_format_b148(
        frame_crc_valid: bool,
        rec_version: u64,
        supported_ver: u64,
    ) -> bool
    clauses [ensures result == (frame_crc_valid && rec_version > supported_ver)]
    {
        frame_crc_valid && rec_version > supported_ver
    }
}

/// Classification of a scanned broker-log frame under `open` or `open_repair`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BrecFormatScanDecision {
    AcceptedSupportedRecord {
        intact_prefix_bytes: u64,
    },
    /// `ErrorKind::Unsupported`: BOTH `open` and `open_repair` MUST leave the file untouched!
    RefusedUnsupportedNewerFormat {
        rec_version: u64,
        untouched_file_len: u64,
    },
    /// `ErrorKind::InvalidData`: `open` leaves untouched; `open_repair` truncates to `cut_to_bytes`.
    RefusedCorruptOrOlderFormat {
        repair_mode: bool,
        resulting_file_len: u64,
    },
}

/// Sequential broker-log scan guard distinguishing `Unsupported` newer format from `InvalidData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NewerBrecFormatGuard {
    file_len: u64,
    intact_prefix_bytes: u64,
}

impl NewerBrecFormatGuard {
    #[must_use]
    pub const fn new(file_len: u64) -> Self {
        Self {
            file_len,
            intact_prefix_bytes: 0,
        }
    }

    #[must_use]
    pub const fn intact_prefix_bytes(&self) -> u64 {
        repair_cut_clamp_b148(self.intact_prefix_bytes, self.file_len)
    }

    /// Inspect the next frame at `intact_prefix_bytes .. frame_end_bytes`.
    pub fn inspect_frame(
        &mut self,
        frame_end_bytes: u64,
        frame_crc_valid: bool,
        rec_version: u64,
        repair_mode: bool,
    ) -> BrecFormatScanDecision {
        if frame_end_bytes > self.file_len || !frame_crc_valid {
            let cut = repair_cut_clamp_b148(self.intact_prefix_bytes, self.file_len);
            return BrecFormatScanDecision::RefusedCorruptOrOlderFormat {
                repair_mode,
                resulting_file_len: if repair_mode { cut } else { self.file_len },
            };
        }
        if is_newer_brec_format_b148(frame_crc_valid, rec_version, SUPPORTED_BREC_VERSION) {
            return BrecFormatScanDecision::RefusedUnsupportedNewerFormat {
                rec_version,
                untouched_file_len: self.file_len,
            };
        }
        if rec_version < SUPPORTED_BREC_VERSION {
            let cut = repair_cut_clamp_b148(self.intact_prefix_bytes, self.file_len);
            return BrecFormatScanDecision::RefusedCorruptOrOlderFormat {
                repair_mode,
                resulting_file_len: if repair_mode { cut } else { self.file_len },
            };
        }
        let bounded_end = repair_cut_clamp_b148(frame_end_bytes, self.file_len);
        self.intact_prefix_bytes =
            intact_prefix_advance_b148(self.intact_prefix_bytes, bounded_end);
        BrecFormatScanDecision::AcceptedSupportedRecord {
            intact_prefix_bytes: self.intact_prefix_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn open_repair_leaves_crc_valid_newer_format_untouched_while_truncating_real_damage() {
        let mut g = NewerBrecFormatGuard::new(200);
        assert_eq!(
            g.inspect_frame(80, true, 2, true),
            BrecFormatScanDecision::AcceptedSupportedRecord {
                intact_prefix_bytes: 80,
            }
        );
        // CRC-valid BREC v3 frame at 80..160 -> `open_repair` refuses Unsupported & leaves all 200 bytes!
        assert_eq!(
            g.inspect_frame(160, true, 3, true),
            BrecFormatScanDecision::RefusedUnsupportedNewerFormat {
                rec_version: 3,
                untouched_file_len: 200,
            }
        );
        // Conversely, older BREC v1 or bad CRC at 80..160 -> `open_repair` cuts to intact prefix 80!
        assert_eq!(
            g.inspect_frame(160, true, 1, true),
            BrecFormatScanDecision::RefusedCorruptOrOlderFormat {
                repair_mode: true,
                resulting_file_len: 80,
            }
        );
    }
}
