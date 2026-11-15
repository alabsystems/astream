// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic `V1Receipt` / `ReceiptVerdict` batch auditor (`astream-evidence`).
//!
//! Enforces strict sequence monotonicity (`receipt_seq_advance`) and fail-closed batch
//! completeness (`receipt_batch_all_passed`) across streams of execution/verification
//! receipts without closures (`0 mandated`). Any failed, unknown, or out-of-order receipt
//! prevents the batch from certifying green.
//! Backed by Clean TLA+ island `Astream.Evidence.TlaReceiptVerdictAudit`.

#[cfg(clean_islands)]
#[path = "receipt_verdict_auditor_island.rs"]
mod receipt_verdict_auditor_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn receipt_pass_clamp(pass_count: u64, total_receipts: u64) -> u64 {
    if pass_count < total_receipts {
        pass_count
    } else {
        total_receipts
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn receipt_seq_advance(cur_seq: u64, proposed_seq: u64) -> u64 {
    if cur_seq < proposed_seq {
        proposed_seq
    } else {
        cur_seq
    }
}
#[cfg(clean_islands)]
pub use receipt_verdict_auditor_island::{receipt_pass_clamp, receipt_seq_advance};

contract_fn! {
    /// Kernel-certified batch gate check (`expected_count <= pass_count`), linked via
    /// `clean-kernel-defeq` to `receipt_batch_all_passed_isl`.
    #[must_use]
    pub const fn receipt_batch_all_passed(pass_count: u64, expected_count: u64) -> bool
    clauses [ensures result == (expected_count <= pass_count)]
    {
        expected_count <= pass_count
    }
}

/// Canonical three-valued receipt verdict (`aterm-link` `ReceiptVerdict::ALL` compatible).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuditedVerdict {
    /// Claim or step verified / passed cleanly.
    Pass,
    /// Claim or step refuted / failed.
    Fail,
    /// Claim or step timed out or remained unclassified (never counted as `Pass`!).
    Unknown,
}

impl AuditedVerdict {
    /// All canonical variants in deterministic table order.
    pub const ALL: [Self; 3] = [Self::Pass, Self::Fail, Self::Unknown];
}

/// Summary report emitted by [`ReceiptBatchAuditor::finish`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReceiptAuditSummary {
    /// Total receipts ingested.
    pub total_receipts: u64,
    /// Clamped count of `Pass` receipts (`<= total_receipts`).
    pub pass_count: u64,
    /// Count of `Fail` receipts.
    pub fail_count: u64,
    /// Count of `Unknown` receipts.
    pub unknown_count: u64,
    /// Count of non-strictly-increasing sequence violations observed.
    pub sequence_regressions: u64,
    /// Highest sequence number observed.
    pub highest_seq: u64,
    /// True iff `total_receipts == expected_count`, `pass_count == expected_count`,
    /// `fail_count == 0`, `unknown_count == 0`, and `sequence_regressions == 0`.
    pub certified_green: bool,
}

/// Streaming fail-closed auditor over ordered verification / execution receipts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReceiptBatchAuditor {
    expected_count: u64,
    total_receipts: u64,
    pass_count: u64,
    fail_count: u64,
    unknown_count: u64,
    sequence_regressions: u64,
    has_first: bool,
    prev_seq: u64,
    cur_seq: u64,
}

impl ReceiptBatchAuditor {
    /// Construct an auditor expecting `expected_count` strictly-increasing `Pass` receipts.
    #[must_use]
    pub const fn new(expected_count: u64) -> Self {
        Self {
            expected_count,
            total_receipts: 0,
            pass_count: 0,
            fail_count: 0,
            unknown_count: 0,
            sequence_regressions: 0,
            has_first: false,
            prev_seq: 0,
            cur_seq: 0,
        }
    }

    /// Previous sequence number observed prior to the latest `record` call.
    #[must_use]
    pub const fn prev_seq(&self) -> u64 {
        self.prev_seq
    }

    /// Ingest a single receipt `(seq, verdict)`.
    pub fn record(&mut self, seq: u64, verdict: AuditedVerdict) {
        self.total_receipts = self.total_receipts.saturating_add(1);
        if !self.has_first {
            self.has_first = true;
            self.prev_seq = seq;
            self.cur_seq = seq;
        } else {
            if seq <= self.cur_seq {
                self.sequence_regressions = self.sequence_regressions.saturating_add(1);
            }
            self.prev_seq = self.cur_seq;
            self.cur_seq = receipt_seq_advance(self.cur_seq, seq);
        }

        match verdict {
            AuditedVerdict::Pass => {
                let raw_pass = self.pass_count.saturating_add(1);
                self.pass_count = receipt_pass_clamp(raw_pass, self.total_receipts);
            }
            AuditedVerdict::Fail => {
                self.fail_count = self.fail_count.saturating_add(1);
            }
            AuditedVerdict::Unknown => {
                self.unknown_count = self.unknown_count.saturating_add(1);
            }
        }
    }

    /// Finalize and evaluate whether the entire expected receipt batch certified green.
    #[must_use]
    pub const fn finish(&self) -> ReceiptAuditSummary {
        let certified_green = self.total_receipts == self.expected_count
            && receipt_batch_all_passed(self.pass_count, self.expected_count)
            && self.fail_count == 0
            && self.unknown_count == 0
            && self.sequence_regressions == 0;
        ReceiptAuditSummary {
            total_receipts: self.total_receipts,
            pass_count: self.pass_count,
            fail_count: self.fail_count,
            unknown_count: self.unknown_count,
            sequence_regressions: self.sequence_regressions,
            highest_seq: self.cur_seq,
            certified_green,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receipt_auditor_certifies_complete_monotone_pass_batch_and_rejects_unknown_or_out_of_order()
    {
        let mut ok_aud = ReceiptBatchAuditor::new(3);
        ok_aud.record(1, AuditedVerdict::Pass);
        ok_aud.record(2, AuditedVerdict::Pass);
        ok_aud.record(5, AuditedVerdict::Pass);
        let rep = ok_aud.finish();
        assert!(rep.certified_green);
        assert_eq!(rep.pass_count, 3);
        assert_eq!(rep.highest_seq, 5);

        // `Unknown` never counts as `Pass`!
        let mut unk_aud = ReceiptBatchAuditor::new(2);
        unk_aud.record(1, AuditedVerdict::Pass);
        unk_aud.record(2, AuditedVerdict::Unknown);
        assert!(!unk_aud.finish().certified_green);

        // Duplicate/regressing sequence fails closed even if all verdicts say `Pass`!
        let mut dup_aud = ReceiptBatchAuditor::new(2);
        dup_aud.record(4, AuditedVerdict::Pass);
        dup_aud.record(4, AuditedVerdict::Pass);
        let drep = dup_aud.finish();
        assert!(!drep.certified_green);
        assert_eq!(drep.sequence_regressions, 1);
    }
}
