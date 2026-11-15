// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY idempotency four-way seam (`send|key|feed-bin|turn … id=<epoch>:<producer>:<seq>`)
//! (`docs/DESIGN-aterm-fabric.md` §11.2 A6 lines 3408–3423, `crates/aterm-gui/src/pty_idem.rs`;
//! `Astream.Host.TlaPtyIdempotencyFourWaySeam`).
//!
//! Enforces the four-way reply contract at the PTY sink:
//! 1. `epoch != session_epoch` -> `RefusedStaleEpoch`,
//! 2. `seq > high_water` -> `ExecuteFresh`: advances `high_water = seq` in `InFlight` state,
//! 3. `seq <= high_water` and mark settled `Applied` -> `DupAlreadyApplied { zero_rows_prefix }`
//!    (`OK dup=1` for `Status` framing, `OK 0 dup=1` for `Lines`/`Bytes` framing so `dup=1` is
//!    never misread as a row count!),
//! 4. `seq == high_water` and mark `InFlight` -> `ErrBusyIdem(seq)` (`ERR busy idem=<seq>`),
//! 5. `seq == high_water` and mark `UnknownOutcome` (e.g. `cmd_turn` typed text then failed submit)
//!    -> `ErrInDoubt(seq)` (`ERR in-doubt seq=<seq>`, never re-typing!).

#[cfg(clean_islands)]
#[path = "pty_idempotency_four_way_seam_island.rs"]
mod pty_idempotency_four_way_seam_island;
#[cfg(clean_islands)]
pub use pty_idempotency_four_way_seam_island::{idem_hw_advance_b136, idem_in_doubt_clamp_b136};

/// Maximum tracked `in-doubt` timeline annotations per session (`256`).
pub const MAX_IN_DOUBT_ROWS: u64 = 256;

#[cfg(not(clean_islands))]
/// Clamp session `in-doubt` timeline count to `rows_cap`.
#[must_use]
pub const fn idem_in_doubt_clamp_b136(cand_rows: u64, rows_cap: u64) -> u64 {
    if cand_rows < rows_cap {
        cand_rows
    } else {
        rows_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance per-(session, producer) idempotency high-water sequence.
#[must_use]
pub const fn idem_hw_advance_b136(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `epoch_matches && (!has_hw || high_water < seq) && !mark_is_in_flight`.
    #[must_use]
    pub const fn pty_idem_fresh_admissible_b136(
        epoch_matches: bool,
        has_hw: bool,
        high_water: u64,
        seq: u64,
        mark_is_in_flight: bool,
    ) -> bool
    clauses [ensures result == (epoch_matches && (!has_hw || high_water < seq) && !mark_is_in_flight)]
    {
        epoch_matches && (!has_hw || high_water < seq) && !mark_is_in_flight
    }
}

/// Disposition of the sequence currently sitting at `high_water`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IdemMarkDisposition {
    Applied,
    InFlight,
    UnknownOutcome,
}

/// Reply verdict for `send|key|feed-bin|turn` carrying `id=<epoch>:<producer>:<seq>`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PtyIdemReply {
    /// Fresh sequence above `high_water` — execute verb against PTY!
    ExecuteFresh { seq: u64 },
    /// Already applied: `zero_rows_prefix == true` emits `OK 0 dup=1` (`Lines`/`Bytes`), else `OK dup=1`.
    DupAlreadyApplied { zero_rows_prefix: bool },
    /// Currently running at `high_water`: `ERR busy idem=<seq>`.
    ErrBusyIdem(u64),
    /// Partial/unknown outcome at `high_water`: `ERR in-doubt seq=<seq>` (never re-types!).
    ErrInDoubt(u64),
    /// Relaunched session nonce mismatch!
    RefusedStaleEpoch,
}

/// Per-(session, producer) PTY idempotency guard.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PtyIdempotencyGuard {
    session_epoch: u64,
    has_hw: bool,
    high_water: u64,
    top_disposition: IdemMarkDisposition,
    in_doubt_rows: u64,
    in_doubt_cap: u64,
}

impl PtyIdempotencyGuard {
    #[must_use]
    pub const fn new(session_epoch: u64) -> Self {
        Self {
            session_epoch,
            has_hw: false,
            high_water: 0,
            top_disposition: IdemMarkDisposition::Applied,
            in_doubt_rows: 0,
            in_doubt_cap: MAX_IN_DOUBT_ROWS,
        }
    }

    #[must_use]
    pub const fn high_water(&self) -> Option<u64> {
        if self.has_hw {
            Some(self.high_water)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn in_doubt_rows(&self) -> u64 {
        idem_in_doubt_clamp_b136(self.in_doubt_rows, self.in_doubt_cap)
    }

    /// Evaluate an incoming PTY verb carrying `id=<req_epoch>:<producer>:<seq>`.
    /// `is_lines_or_bytes_framed` controls `OK 0 dup=1` vs `OK dup=1` (§11.2 A6).
    pub fn check_or_arm(
        &mut self,
        req_epoch: u64,
        seq: u64,
        is_lines_or_bytes_framed: bool,
    ) -> PtyIdemReply {
        let epoch_ok = req_epoch == self.session_epoch;
        let in_flight =
            self.has_hw && matches!(self.top_disposition, IdemMarkDisposition::InFlight);
        if !epoch_ok {
            return PtyIdemReply::RefusedStaleEpoch;
        }
        if pty_idem_fresh_admissible_b136(epoch_ok, self.has_hw, self.high_water, seq, in_flight) {
            self.high_water = if self.has_hw {
                idem_hw_advance_b136(self.high_water, seq)
            } else {
                seq
            };
            self.has_hw = true;
            self.top_disposition = IdemMarkDisposition::InFlight;
            return PtyIdemReply::ExecuteFresh { seq };
        }
        if in_flight && seq >= self.high_water {
            return PtyIdemReply::ErrBusyIdem(self.high_water);
        }
        if seq == self.high_water {
            return match self.top_disposition {
                IdemMarkDisposition::Applied => PtyIdemReply::DupAlreadyApplied {
                    zero_rows_prefix: is_lines_or_bytes_framed,
                },
                IdemMarkDisposition::InFlight => PtyIdemReply::ErrBusyIdem(seq),
                IdemMarkDisposition::UnknownOutcome => PtyIdemReply::ErrInDoubt(seq),
            };
        }
        // `seq < high_water`: any earlier sequence was settled before `high_water` advanced!
        PtyIdemReply::DupAlreadyApplied {
            zero_rows_prefix: is_lines_or_bytes_framed,
        }
    }

    /// Settle the in-flight sequence at `high_water` (`outcome_known_applied == false` records `in-doubt`!).
    pub fn settle_in_flight(&mut self, outcome_known_applied: bool) {
        if !self.has_hw || !matches!(self.top_disposition, IdemMarkDisposition::InFlight) {
            return;
        }
        if outcome_known_applied {
            self.top_disposition = IdemMarkDisposition::Applied;
        } else {
            self.top_disposition = IdemMarkDisposition::UnknownOutcome;
            self.in_doubt_rows =
                idem_in_doubt_clamp_b136(self.in_doubt_rows.saturating_add(1), self.in_doubt_cap);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn four_way_seam_distinguishes_fresh_busy_dup_and_in_doubt() {
        let mut g = PtyIdempotencyGuard::new(0xCAFE);
        assert_eq!(
            g.check_or_arm(0xBEEF, 1, false),
            PtyIdemReply::RefusedStaleEpoch
        );
        assert_eq!(
            g.check_or_arm(0xCAFE, 10, true),
            PtyIdemReply::ExecuteFresh { seq: 10 }
        );
        // Concurrent retry while 10 is still running -> `ERR busy idem=10`!
        assert_eq!(
            g.check_or_arm(0xCAFE, 10, true),
            PtyIdemReply::ErrBusyIdem(10)
        );
        g.settle_in_flight(true);
        // Replay on `Lines`-framed verb -> `OK 0 dup=1` (`zero_rows_prefix == true`)!
        assert_eq!(
            g.check_or_arm(0xCAFE, 10, true),
            PtyIdemReply::DupAlreadyApplied {
                zero_rows_prefix: true
            }
        );
        // `cmd_turn` at seq 11 types text then fails to submit -> `in-doubt`!
        assert_eq!(
            g.check_or_arm(0xCAFE, 11, false),
            PtyIdemReply::ExecuteFresh { seq: 11 }
        );
        g.settle_in_flight(false);
        assert_eq!(
            g.check_or_arm(0xCAFE, 11, false),
            PtyIdemReply::ErrInDoubt(11)
        );
        assert_eq!(g.in_doubt_rows(), 1);
    }
}
