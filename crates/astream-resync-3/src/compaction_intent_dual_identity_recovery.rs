// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe off-ack-path compaction `<log>.compact` dual-identity recovery
//! (`docs/REQUIREMENTS-fabric-operations-2026-09-14.md` R4 lines 146–162, `compact.rs`;
//! `Astream.Broker.TlaCompactionIntentDualIdentityRecovery`).
//!
//! Guarantees that a crash or power loss at ANY point inside a compaction leaves `<log>` openable:
//! - Before renaming `<log>.kept` over `<log>`, the compactor flushes `<log>.kept`, `<log>.state.next`,
//!   and `<log>.compact { new_base, old_first_frame_id, new_first_frame_id }` (plus directory fsync),
//! - On reopen:
//!   * No `<log>.compact` -> `NormalOpen { base: current_base }`,
//!   * `<log>`'s first frame matches `new_first_frame_id` (crash AFTER rename!) -> finish installing
//!     `new_base`, `<log>.state.next`, and anti-rollback `.hw`, then remove `<log>.compact`,
//!   * `<log>`'s first frame matches `old_first_frame_id` (crash BEFORE rename!) -> discard `<log>.kept`,
//!     `<log>.state.next`, and `<log>.compact`, keeping `current_base` intact,
//!   * `<log>`'s first frame matches NEITHER -> fail closed (`RefusedCorruptCompactionIntent`)!

#[cfg(clean_islands)]
#[path = "compaction_intent_dual_identity_recovery_island.rs"]
mod compaction_intent_dual_identity_recovery_island;
#[cfg(clean_islands)]
pub use compaction_intent_dual_identity_recovery_island::{
    compact_base_advance_b138, compact_chunk_clamp_b138,
};

/// Streaming off-ack-path copy chunk ceiling (`1 MiB` = `1_048_576` B; never reads whole log into RAM).
pub const COMPACT_STREAM_CHUNK_MAX: u64 = 1_048_576;

#[cfg(not(clean_islands))]
/// Clamp streaming compaction copy chunk size to `chunk_cap` (`COMPACT_STREAM_CHUNK_MAX`).
#[must_use]
pub const fn compact_chunk_clamp_b138(cand_chunk: u64, chunk_cap: u64) -> u64 {
    if cand_chunk < chunk_cap {
        cand_chunk
    } else {
        chunk_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance log base offset across completed compactions.
#[must_use]
pub const fn compact_base_advance_b138(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}

contract_fn! {
    /// True iff `(matches_new && cur_base <= intent_new_base) || matches_old`.
    #[must_use]
    pub const fn compact_intent_recoverable_b138(
        matches_new: bool,
        matches_old: bool,
        cur_base: u64,
        intent_new_base: u64,
    ) -> bool
    clauses [ensures result == ((matches_new && cur_base <= intent_new_base) || matches_old)]
    {
        (matches_new && cur_base <= intent_new_base) || matches_old
    }
}

/// Durable `<log>.compact` sidecar record.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CompactionIntentRecord {
    pub new_base: u64,
    pub old_first_frame_id: u64,
    pub new_first_frame_id: u64,
}

/// Recovery action taken during `BrokerLog::open` when inspecting `<log>.compact`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CompactionRecoveryOutcome {
    /// No `<log>.compact` present.
    NormalOpen { base: u64 },
    /// Crash happened BEFORE rename (`first_frame == old_id`): discard `.kept`/`.state.next`/`.compact`!
    DiscardedPreRenameStaging { preserved_base: u64 },
    /// Crash happened AFTER rename (`first_frame == new_id`): finalize `.base`/`.state`/`.hw`!
    FinalizedPostRenameInstall { installed_base: u64 },
    /// `<log>`'s first frame matches neither `old_id` nor `new_id` (or `new_base < cur_base`): fail closed!
    RefusedCorruptCompactionIntent,
}

/// Single-flight off-ack-path compaction & crash recovery coordinator.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CompactionCoordinator {
    chunk_cap: u64,
    current_base: u64,
    compaction_running: bool,
    retention_skips: u64,
}

impl CompactionCoordinator {
    #[must_use]
    pub const fn new(initial_base: u64) -> Self {
        Self {
            chunk_cap: COMPACT_STREAM_CHUNK_MAX,
            current_base: initial_base,
            compaction_running: false,
            retention_skips: 0,
        }
    }

    #[must_use]
    pub const fn current_base(&self) -> u64 {
        self.current_base
    }

    #[must_use]
    pub const fn retention_skips(&self) -> u64 {
        self.retention_skips
    }

    #[must_use]
    pub const fn stream_copy_chunk(&self, remaining_bytes: u64) -> u64 {
        compact_chunk_clamp_b138(remaining_bytes, self.chunk_cap)
    }

    /// Acquire single-flight compaction slot; overlapping ticks increment `retention_skips` (R4 line 179)!
    pub fn try_begin_compaction(&mut self) -> bool {
        if self.compaction_running {
            self.retention_skips = self.retention_skips.saturating_add(1);
            false
        } else {
            self.compaction_running = true;
            true
        }
    }

    pub fn finish_compaction(&mut self, new_base: u64) {
        self.current_base = compact_base_advance_b138(self.current_base, new_base);
        self.compaction_running = false;
    }

    /// Recover `<log>` on open against optional `<log>.compact` and the actual first frame on disk.
    pub fn recover_on_open(
        &mut self,
        disk_first_frame_id: u64,
        intent: Option<CompactionIntentRecord>,
    ) -> CompactionRecoveryOutcome {
        let Some(rec) = intent else {
            return CompactionRecoveryOutcome::NormalOpen {
                base: self.current_base,
            };
        };
        let matches_new = disk_first_frame_id == rec.new_first_frame_id;
        let matches_old = disk_first_frame_id == rec.old_first_frame_id;
        if !compact_intent_recoverable_b138(
            matches_new,
            matches_old,
            self.current_base,
            rec.new_base,
        ) {
            return CompactionRecoveryOutcome::RefusedCorruptCompactionIntent;
        }
        if matches_new && self.current_base <= rec.new_base {
            let installed = compact_base_advance_b138(self.current_base, rec.new_base);
            self.current_base = installed;
            CompactionRecoveryOutcome::FinalizedPostRenameInstall {
                installed_base: installed,
            }
        } else {
            CompactionRecoveryOutcome::DiscardedPreRenameStaging {
                preserved_base: self.current_base,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recovers_both_pre_rename_and_post_rename_crashes_and_counts_overlapping_tick_skips() {
        let mut c = CompactionCoordinator::new(100);
        assert!(c.try_begin_compaction());
        assert!(!c.try_begin_compaction());
        assert_eq!(c.retention_skips(), 1);
        c.finish_compaction(100);

        let intent = CompactionIntentRecord {
            new_base: 250,
            old_first_frame_id: 0x1111,
            new_first_frame_id: 0x2222,
        };
        // Crash BEFORE rename (`disk == 0x1111`) -> discards `.kept` and preserves `base = 100`:
        assert_eq!(
            c.recover_on_open(0x1111, Some(intent)),
            CompactionRecoveryOutcome::DiscardedPreRenameStaging {
                preserved_base: 100
            }
        );
        // Crash AFTER rename (`disk == 0x2222`) -> finalizes `base = 250`!
        assert_eq!(
            c.recover_on_open(0x2222, Some(intent)),
            CompactionRecoveryOutcome::FinalizedPostRenameInstall {
                installed_base: 250
            }
        );
        // Unknown first frame (`0x9999`) -> fails closed!
        assert_eq!(
            c.recover_on_open(0x9999, Some(intent)),
            CompactionRecoveryOutcome::RefusedCorruptCompactionIntent
        );
    }
}
