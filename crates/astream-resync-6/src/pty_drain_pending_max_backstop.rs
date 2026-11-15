// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY interleaved drain `PENDING_MAX` (`8 MiB`) backstop & pre-write frame-cap refusal
//! (`evidence/manifest.toml` `term.drive.interactive-exactly-once`;
//! `Astream.Host.TlaPtyDrainPendingMaxBackstop`).
//!
//! Models `astream-host::Driver`'s deadlock-free yet bounded PTY write path:
//! - Before a single byte touches the PTY master, `Session::precheck_input` verifies holder
//!   authority AND `payload_len <= MAX_FRAME_PAYLOAD_BYTES` (`RefusedOversizedProposalBeforePty`),
//! - While the kernel PTY input queue returns `EAGAIN`, the driver drains child `/out` bytes up
//!   to `PENDING_MAX_DRAIN_BYTES` (`8 MiB`),
//! - If a runaway child floods output past `8 MiB` during a single input write, the write aborts
//!   at `PENDING_MAX` with NO `Record::In` committed!

#[cfg(clean_islands)]
#[path = "pty_drain_pending_max_backstop_island.rs"]
mod pty_drain_pending_max_backstop_island;
#[cfg(clean_islands)]
pub use pty_drain_pending_max_backstop_island::{
    committed_in_count_advance_b144, pending_drain_bytes_clamp_b144,
};

/// `PENDING_MAX` (`8 MiB`) cap on output drained while unblocking a stalled PTY write.
pub const PENDING_MAX_DRAIN_BYTES: u64 = 8 * 1024 * 1024;
/// Maximum `Record::In` payload accepted by `Session::precheck_input` (`16 MiB - 64`).
pub const MAX_IN_PAYLOAD_BYTES: u64 = 16 * 1024 * 1024 - 64;

#[cfg(not(clean_islands))]
/// Clamp drained output buffer size to `pending_max_bytes`.
#[must_use]
pub const fn pending_drain_bytes_clamp_b144(cand_bytes: u64, pending_max_bytes: u64) -> u64 {
    if cand_bytes < pending_max_bytes {
        cand_bytes
    } else {
        pending_max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of committed `Record::In` proposals.
#[must_use]
pub const fn committed_in_count_advance_b144(cur_ins: u64, cand_ins: u64) -> u64 {
    if cur_ins < cand_ins {
        cand_ins
    } else {
        cur_ins
    }
}

contract_fn! {
    /// True iff `holder_valid`, `payload_len <= max_frame_payload`, and `pending_out_bytes < pending_max_bytes`.
    #[must_use]
    pub const fn pty_proposal_admissible_b144(
        holder_valid: bool,
        payload_len: u64,
        max_frame_payload: u64,
        pending_out_bytes: u64,
        pending_max_bytes: u64,
    ) -> bool
    clauses [ensures result == (holder_valid && payload_len <= max_frame_payload && pending_out_bytes < pending_max_bytes)]
    {
        holder_valid && payload_len <= max_frame_payload && pending_out_bytes < pending_max_bytes
    }
}

/// Outcome of `Driver` precheck, interleaved output drain, and `Record::In` commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtyDriveStepOutcome {
    RefusedNotHolderBeforePty,
    RefusedOversizedProposalBeforePty { payload_len: u64 },
    DrainedChunkKeepWriting { pending_out_bytes: u64 },
    AbortedPendingMaxExceededNoInRecorded { pending_out_bytes: u64 },
    CommittedInRecord { committed_ins: u64 },
}

/// Bounded interleaved-drain state machine for `Driver::drive_input`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyDrainBackstop {
    pending_out_bytes: u64,
    committed_ins: u64,
}

impl PtyDrainBackstop {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pending_out_bytes: 0,
            committed_ins: 0,
        }
    }

    #[must_use]
    pub const fn precheck_before_pty(
        &self,
        holder_valid: bool,
        payload_len: u64,
    ) -> Option<PtyDriveStepOutcome> {
        if !holder_valid {
            return Some(PtyDriveStepOutcome::RefusedNotHolderBeforePty);
        }
        if payload_len > MAX_IN_PAYLOAD_BYTES {
            return Some(PtyDriveStepOutcome::RefusedOversizedProposalBeforePty { payload_len });
        }
        if !pty_proposal_admissible_b144(
            holder_valid,
            payload_len,
            MAX_IN_PAYLOAD_BYTES,
            self.pending_out_bytes,
            PENDING_MAX_DRAIN_BYTES,
        ) {
            return Some(PtyDriveStepOutcome::AbortedPendingMaxExceededNoInRecorded {
                pending_out_bytes: self.pending_out_bytes,
            });
        }
        None
    }

    pub fn drain_while_pty_full(&mut self, child_chunk_bytes: u64) -> PtyDriveStepOutcome {
        let cand = self.pending_out_bytes.saturating_add(child_chunk_bytes);
        self.pending_out_bytes = pending_drain_bytes_clamp_b144(cand, PENDING_MAX_DRAIN_BYTES);
        if cand >= PENDING_MAX_DRAIN_BYTES {
            PtyDriveStepOutcome::AbortedPendingMaxExceededNoInRecorded {
                pending_out_bytes: self.pending_out_bytes,
            }
        } else {
            PtyDriveStepOutcome::DrainedChunkKeepWriting {
                pending_out_bytes: self.pending_out_bytes,
            }
        }
    }

    pub fn finish_in_commit(&mut self) -> PtyDriveStepOutcome {
        self.pending_out_bytes = 0;
        let next = self.committed_ins.saturating_add(1);
        self.committed_ins = committed_in_count_advance_b144(self.committed_ins, next);
        PtyDriveStepOutcome::CommittedInRecord {
            committed_ins: self.committed_ins,
        }
    }
}

impl Default for PtyDrainBackstop {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_oversized_before_pty_and_aborts_runaway_child_at_8mib_without_in_record() {
        let mut d = PtyDrainBackstop::new();
        assert_eq!(
            d.precheck_before_pty(true, MAX_IN_PAYLOAD_BYTES + 1),
            Some(PtyDriveStepOutcome::RefusedOversizedProposalBeforePty {
                payload_len: MAX_IN_PAYLOAD_BYTES + 1
            })
        );
        assert_eq!(
            d.drain_while_pty_full(4 * 1024 * 1024),
            PtyDriveStepOutcome::DrainedChunkKeepWriting {
                pending_out_bytes: 4 * 1024 * 1024
            }
        );
        assert_eq!(
            d.drain_while_pty_full(4 * 1024 * 1024),
            PtyDriveStepOutcome::AbortedPendingMaxExceededNoInRecorded {
                pending_out_bytes: PENDING_MAX_DRAIN_BYTES
            }
        );
        assert_eq!(d.committed_ins, 0);
    }
}
