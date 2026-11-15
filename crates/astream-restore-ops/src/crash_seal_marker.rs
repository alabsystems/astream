// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Boot-session (`boot_id`) and clean-exit seal verifier distinguishing graceful tab close,
//! live crash (`SIGKILL`), and across-OS-reboot recovery (`astream-sys`, `Astream.Restore.TlaCrashSealMarker`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "crash_seal_marker_island.rs"]
mod crash_seal_marker_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seal_epoch_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seal_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use crash_seal_marker_island::{seal_epoch_clamp, seal_seq_advance};

/// Maximum tracked open/seal cycles per crash-restore file.
pub const MAX_SEAL_CYCLES: u64 = 1_000_000;

contract_fn! {
    /// Verified seal sequence check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `seal_matches_boot_isl`.
    #[must_use]
    pub const fn seal_matches_boot(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Recovery disposition of a crash-restore region on startup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryDisposition {
    CleanExit { final_offset: u64 },
    ProcessCrashSameBoot { open_seq: u64 },
    OsRebootCrash { open_seq: u64 },
}

///Boot-bound crash seal record.
#[derive(Debug, Clone)]
pub struct CrashSealRecord {
    boot_digest: [u8; 32],
    open_seq: u64,
    sealed_seq: u64,
    final_offset: u64,
}

fn hash_boot_id(boot_id: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-BOOT-SEAL-V1\0");
    h.update_slice(boot_id.as_bytes());
    h.finalize()
}

impl CrashSealRecord {
    #[must_use]
    pub fn open_for_boot(boot_id: &str, prev_seq: u64) -> Self {
        let base_prev = seal_epoch_clamp(prev_seq, MAX_SEAL_CYCLES.saturating_sub(1));
        let next = seal_epoch_clamp(base_prev.saturating_add(1), MAX_SEAL_CYCLES);
        let open_seq = seal_seq_advance(base_prev, next);
        Self {
            boot_digest: hash_boot_id(boot_id),
            open_seq,
            sealed_seq: base_prev,
            final_offset: 0,
        }
    }

    pub fn mark_clean_shutdown(&mut self, final_offset: u64) {
        self.sealed_seq = seal_seq_advance(self.sealed_seq, self.open_seq);
        self.final_offset = final_offset;
    }

    #[must_use]
    pub fn classify_on_startup(&self, current_boot_id: &str) -> RecoveryDisposition {
        if seal_matches_boot(self.sealed_seq, self.open_seq) {
            return RecoveryDisposition::CleanExit {
                final_offset: self.final_offset,
            };
        }
        let cur = hash_boot_id(current_boot_id);
        if ct_eq(&self.boot_digest, &cur) {
            RecoveryDisposition::ProcessCrashSameBoot {
                open_seq: self.open_seq,
            }
        } else {
            RecoveryDisposition::OsRebootCrash {
                open_seq: self.open_seq,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seal_distinguishes_same_boot_sigkill_os_reboot_and_clean_exit() {
        let mut s = CrashSealRecord::open_for_boot("boot-A", 0);
        assert_eq!(
            s.classify_on_startup("boot-A"),
            RecoveryDisposition::ProcessCrashSameBoot { open_seq: 1 }
        );
        assert_eq!(
            s.classify_on_startup("boot-B"),
            RecoveryDisposition::OsRebootCrash { open_seq: 1 }
        );
        s.mark_clean_shutdown(999);
        assert_eq!(
            s.classify_on_startup("boot-B"),
            RecoveryDisposition::CleanExit { final_offset: 999 }
        );
    }
}
