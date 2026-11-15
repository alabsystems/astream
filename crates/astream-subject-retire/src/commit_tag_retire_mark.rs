// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Marked `/a/retire` record classifier (`COMMIT_TAG_RETIRE = 2`, `RETIRE_PRODUCER_SEQ = u64::MAX`,
//! `docs/ROADMAP.md` §2) distinguishing marked retire commands and legacy seq-zero compatibility
//! headers from ordinary `/a/retire` data rows (`Astream.SubjRet.TlaCommitTagRetireMark`).

#[cfg(clean_islands)]
#[path = "commit_tag_retire_mark_island.rs"]
mod commit_tag_retire_mark_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_tag_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use commit_tag_retire_mark_island::{srb_seq_advance, srb_tag_clamp};

/// Reserved commit tag for `/a/retire` control records.
pub const COMMIT_TAG_RETIRE: u64 = 2;
/// Sentinel `producer_seq` causing older record/replicate decoders to fail closed.
pub const RETIRE_PRODUCER_SEQ: u64 = u64::MAX;

contract_fn! {
    /// Verified retire control marker (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `srb_is_retire_cmd_isl`.
    #[must_use]
    pub const fn srb_is_retire_cmd(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct RetireRecordClassifier {
    decoded_commands: u64,
}

impl RetireRecordClassifier {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            decoded_commands: 0,
        }
    }

    pub fn is_retire_command(
        &mut self,
        subject: &str,
        commit_tag: Option<u64>,
        producer_seq: u64,
    ) -> bool {
        if subject != "/a/retire" {
            return false;
        }
        let marked = match commit_tag {
            Some(t) => {
                srb_tag_clamp(t, COMMIT_TAG_RETIRE) == COMMIT_TAG_RETIRE
                    && t == COMMIT_TAG_RETIRE
                    && producer_seq == RETIRE_PRODUCER_SEQ
            }
            None => producer_seq == 0,
        };
        if srb_is_retire_cmd(u64::from(marked), 1) {
            self.decoded_commands = srb_seq_advance(
                self.decoded_commands,
                self.decoded_commands.saturating_add(1),
            );
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_marked_and_seq_zero_retire_while_leaving_other_rows_as_data() {
        let mut c = RetireRecordClassifier::new();
        assert!(c.is_retire_command("/a/retire", Some(COMMIT_TAG_RETIRE), RETIRE_PRODUCER_SEQ));
        assert!(c.is_retire_command("/a/retire", None, 0));
        assert!(!c.is_retire_command("/a/retire", None, 7));
    }
}
