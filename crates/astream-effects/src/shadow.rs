// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hermetic shadow / counterfactual policy evaluation over recorded effect tapes
//! (`Astream.Effects.TlaShadowReplay`; `aterm-agent` `Shadow` & `KeyedView` semantics).
//!
//! [`ReplaySeam`](crate::ReplaySeam) drives a recorded program strictly in order, failing
//! on the first out-of-order question or altered output. When re-evaluating a candidate
//! policy across every decision point of a recorded tape (`aterm drive replay --shadow`),
//! the candidate may ask recorded [`Exchange`](crate::EffectRecord::Exchange) doors in a
//! different order, skip a probe, or request a probe the original run never needed:
//!
//! - [`ShadowSeam`] implements [`EffectSeam`] hermetically at a tape cutoff `seen`:
//!   - [`EffectSeam::exchange`] answers out-of-order from [`KeyedView::lookup`] within
//!     `0..seen` without ever invoking `live`, recording any unrecorded `(door, request)`
//!     into [`ShadowSeam::missing_needs`] before returning [`ReplayDivergence::Unrecorded`].
//!   - [`EffectSeam::now_nanos`], [`EffectSeam::mono_nanos`], [`EffectSeam::next_rand`],
//!     and [`EffectSeam::read_file`] answer from the latest matching record `< seen`
//!     without advancing a destructive cursor.
//!   - [`EffectSeam::emit`] captures candidate outputs into [`ShadowSeam::emitted`]
//!     instead of failing on difference, so the caller can compare recorded vs. candidate
//!     decisions cleanly.
//! - [`ShadowLedger`] tracks decision-by-decision outcomes across a tape, latching
//!   `taint` monotonically after the first differing decision ([`shadow_taint_latch`])
//!   and computing the exact exit code (`0` = all re-decided as recorded, `1` = at least
//!   one decided otherwise, `3` = zero known differences, at least one undecided due to
//!   missing tape data; [`shadow_exit_code`]).

use crate::keyed::KeyedView;
use crate::replay::ReplayDivergence;
use crate::seam::{EffectRecord, EffectSeam};

#[cfg(clean_islands)]
#[path = "shadow_island.rs"]
mod shadow_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{shadow_code_select, shadow_nonzero_bit};
#[cfg(clean_islands)]
pub use shadow_island::{shadow_code_select, shadow_nonzero_bit};

/// Monotone shadow taint latch (`shadow_taint_latch_isl` in `shadow_island.rs`),
/// composed over Clean-origin [`shadow_code_select`] and [`shadow_nonzero_bit`].
#[must_use]
pub const fn shadow_taint_latch(cur_taint: u64, row_differed: u64) -> u64 {
    shadow_code_select(cur_taint, 1, shadow_nonzero_bit(row_differed, 1))
}

/// Shadow evaluation exit-code selector (`shadow_exit_code_isl` in `shadow_island.rs`),
/// composed over Clean-origin [`shadow_code_select`] and [`shadow_nonzero_bit`]:
/// `1` if `differs_count > 0`, else `3` if `unknown_count > 0`, else `0`.
#[must_use]
pub const fn shadow_exit_code(differs_count: u64, unknown_count: u64) -> u64 {
    shadow_code_select(differs_count, 1, shadow_nonzero_bit(unknown_count, 3))
}

/// Maximum number of missing `(door, request)` needs retained on a single [`ShadowSeam`].
pub const MAX_SHADOW_NEEDS: usize = 256;

/// Maximum number of emitted `(door, bytes)` acts retained on a single [`ShadowSeam`].
pub const MAX_SHADOW_EMITS: usize = 256;

/// Maximum number of decision points tracked in a [`ShadowLedger`].
pub const MAX_SHADOW_ROWS: usize = 16_384;

contract_fn! {
    /// Kernel-certified exit-code range guard (`code <= 3`).
    #[must_use]
    pub const fn shadow_code_in_range(code: u64) -> bool
    clauses [ensures result == (code <= 3)]
    {
        code <= 3
    }
}

/// Missing `(door, request)` probe encountered while evaluating a candidate on [`ShadowSeam`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowNeed {
    /// Name of the exchange/file door whose answer was absent before `seen`.
    pub door: String,
    /// Opaque request bytes (or UTF-8 file path) that were not recorded before `seen`.
    pub request: Vec<u8>,
}

/// Candidate output captured through [`EffectSeam::emit`] on a [`ShadowSeam`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowEmit {
    /// Output door name.
    pub door: String,
    /// Emitted payload bytes.
    pub bytes: Vec<u8>,
}

/// Non-consuming, hermetic [`EffectSeam`] backed by a [`KeyedView`] at cutoff `seen`.
pub struct ShadowSeam<'a> {
    records: &'a [EffectRecord],
    view: &'a KeyedView<'a>,
    seen: usize,
    needs: Vec<ShadowNeed>,
    emitted: Vec<ShadowEmit>,
}

impl<'a> ShadowSeam<'a> {
    /// Construct a [`ShadowSeam`] answering from `records[..seen.min(records.len())]`.
    #[must_use]
    pub fn new(records: &'a [EffectRecord], view: &'a KeyedView<'a>, seen: usize) -> Self {
        let clamped_seen =
            crate::keyed::keyed_clamp_cutoff(seen as u64, records.len() as u64) as usize;
        Self {
            records,
            view,
            seen: clamped_seen,
            needs: Vec::new(),
            emitted: Vec::new(),
        }
    }

    /// Cutoff index (`0..=records.len()`) bounding which tape entries are visible.
    #[must_use]
    pub const fn seen(&self) -> usize {
        self.seen
    }

    /// Missing `(door, request)` probes requested by the candidate that were absent `< seen`.
    #[must_use]
    pub fn missing_needs(&self) -> &[ShadowNeed] {
        &self.needs
    }

    /// Outputs produced by the candidate via [`EffectSeam::emit`].
    #[must_use]
    pub fn emitted(&self) -> &[ShadowEmit] {
        &self.emitted
    }

    fn record_need(&mut self, door: &str, request: &[u8]) {
        if self.needs.len() < MAX_SHADOW_NEEDS {
            self.needs.push(ShadowNeed {
                door: door.to_string(),
                request: request.to_vec(),
            });
        }
    }
}

impl EffectSeam for ShadowSeam<'_> {
    type Error = ReplayDivergence;

    fn now_nanos(&mut self) -> Result<u64, Self::Error> {
        let mut end =
            crate::keyed::keyed_clamp_cutoff(self.seen as u64, self.records.len() as u64) as usize;
        while let Some(pos) = end.checked_sub(1) {
            if let Some(EffectRecord::Clock(v)) = self.records.get(pos) {
                return Ok(*v);
            }
            end = pos;
        }
        self.record_need("clock", b"now_nanos");
        Err(ReplayDivergence::Exhausted { expected: "Clock" })
    }

    fn mono_nanos(&mut self) -> Result<u64, Self::Error> {
        let mut end =
            crate::keyed::keyed_clamp_cutoff(self.seen as u64, self.records.len() as u64) as usize;
        while let Some(pos) = end.checked_sub(1) {
            if let Some(EffectRecord::Mono(v)) = self.records.get(pos) {
                return Ok(*v);
            }
            end = pos;
        }
        self.record_need("mono", b"mono_nanos");
        Err(ReplayDivergence::Exhausted { expected: "Mono" })
    }

    fn next_rand(&mut self) -> Result<u64, Self::Error> {
        let mut end =
            crate::keyed::keyed_clamp_cutoff(self.seen as u64, self.records.len() as u64) as usize;
        while let Some(pos) = end.checked_sub(1) {
            if let Some(EffectRecord::Rand(v)) = self.records.get(pos) {
                return Ok(*v);
            }
            end = pos;
        }
        self.record_need("rand", b"next_rand");
        Err(ReplayDivergence::Exhausted { expected: "Rand" })
    }

    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, Self::Error> {
        match self.try_read_file(path)? {
            Ok(bytes) => Ok(bytes),
            Err(_) => Ok(Vec::new()),
        }
    }

    fn try_read_file(&mut self, path: &str) -> Result<std::io::Result<Vec<u8>>, Self::Error> {
        let mut end =
            crate::keyed::keyed_clamp_cutoff(self.seen as u64, self.records.len() as u64) as usize;
        while let Some(pos) = end.checked_sub(1) {
            match self.records.get(pos) {
                Some(EffectRecord::File { path: p, bytes }) if p == path => {
                    return Ok(Ok(bytes.clone()));
                }
                Some(EffectRecord::FileErr { path: p, kind }) if p == path => {
                    return Ok(Err(std::io::Error::from(*kind)));
                }
                _ => {}
            }
            end = pos;
        }
        self.record_need("file", path.as_bytes());
        Err(ReplayDivergence::Unrecorded {
            door: "file".to_string(),
            request: path.as_bytes().to_vec(),
        })
    }

    fn exchange(
        &mut self,
        door: &str,
        request: &[u8],
        _live: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error> {
        match self.view.lookup(door, request, self.seen) {
            Ok(hit) => Ok(hit.reply.to_vec()),
            Err(div) => {
                self.record_need(door, request);
                Err(div)
            }
        }
    }

    fn emit(&mut self, door: &str, bytes: &[u8]) -> Result<(), Self::Error> {
        if self.emitted.len() < MAX_SHADOW_EMITS {
            self.emitted.push(ShadowEmit {
                door: door.to_string(),
                bytes: bytes.to_vec(),
            });
        }
        Ok(())
    }

    fn raised(&mut self, door: &str, _live: &mut dyn FnMut() -> bool) -> Result<bool, Self::Error> {
        let mut end =
            crate::keyed::keyed_clamp_cutoff(self.seen as u64, self.records.len() as u64) as usize;
        while let Some(pos) = end.checked_sub(1) {
            if let Some(EffectRecord::Raised { door: d, .. }) = self.records.get(pos) {
                if d == door {
                    return Ok(true);
                }
            }
            end = pos;
        }
        Ok(false)
    }
}

/// Outcome of re-evaluating one recorded decision point under a candidate policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShadowDecisionOutcome {
    /// Candidate reached a decision (`differs == (candidate != recorded)`).
    Decided { candidate: String, differs: bool },
    /// Candidate could not decide because the tape lacked required probes (`needs`).
    Undecided { reason: String },
}

/// Recorded vs. candidate comparison row in a [`ShadowLedger`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowPoint {
    /// Decision ordinal on the tape.
    pub ordinal: u64,
    /// Decision door name (e.g. `"decide.approval"`, `"decide.turn_end"`).
    pub door: String,
    /// Recorded outcome string.
    pub recorded: String,
    /// Candidate outcome (`Some(false)` = same, `Some(true)` = otherwise, `None` = unknown).
    pub differs: Option<bool>,
    /// Candidate decision text when decided.
    pub candidate: Option<String>,
    /// `true` on every row strictly after the first row with `differs == Some(true)`.
    pub taint: bool,
    /// Missing probes encountered at this point.
    pub needs: Vec<ShadowNeed>,
    /// Diagnostic note when `differs` is `None`.
    pub note: Option<String>,
}

/// Tape-wide shadow evaluation ledger (`Astream.Effects.TlaShadowReplay`).
#[derive(Debug, Clone, Default)]
pub struct ShadowLedger {
    rows: Vec<ShadowPoint>,
    differs_count: u64,
    unknown_count: u64,
    taint: u64,
}

impl ShadowLedger {
    /// Construct an empty [`ShadowLedger`].
    #[must_use]
    pub const fn new() -> Self {
        Self {
            rows: Vec::new(),
            differs_count: 0,
            unknown_count: 0,
            taint: 0,
        }
    }

    /// Recorded comparison points in evaluation order.
    #[must_use]
    pub fn rows(&self) -> &[ShadowPoint] {
        &self.rows
    }

    /// Number of points where the candidate decided otherwise (`differs == Some(true)`).
    #[must_use]
    pub const fn differs_count(&self) -> u64 {
        self.differs_count
    }

    /// Number of points that could not be re-decided from the tape (`differs == None`).
    #[must_use]
    pub const fn unknown_count(&self) -> u64 {
        self.unknown_count
    }

    /// Whether later rows are tainted by an earlier counterfactual divergence.
    #[must_use]
    pub const fn is_tainted(&self) -> bool {
        self.taint != 0
    }

    /// Exit code matching `aterm drive replay --shadow`:
    /// - `0`: every decision point was re-decided identically to the recorded run,
    /// - `1`: at least one decision point decided otherwise,
    /// - `3`: zero known differences, but at least one point could not be re-decided.
    #[must_use]
    pub const fn exit_code(&self) -> u8 {
        let code = shadow_exit_code(self.differs_count, self.unknown_count);
        let _ = shadow_code_in_range(code);
        code as u8
    }

    /// Append one evaluated decision point, applying `taint` from prior divergences first
    /// and then latching `taint` via [`shadow_taint_latch`] if this point differed.
    pub fn record_point(
        &mut self,
        ordinal: u64,
        door: &str,
        recorded: &str,
        outcome: ShadowDecisionOutcome,
        needs: Vec<ShadowNeed>,
    ) -> Result<(), String> {
        if self.rows.len() >= MAX_SHADOW_ROWS {
            return Err(format!(
                "shadow ledger reached max {MAX_SHADOW_ROWS} decision rows"
            ));
        }
        let row_taint = self.taint != 0;
        let (differs, candidate, note, row_diff_flag) = match outcome {
            ShadowDecisionOutcome::Decided { candidate, differs } => {
                if differs {
                    self.differs_count = self.differs_count.saturating_add(1);
                }
                (
                    Some(differs),
                    Some(candidate),
                    None,
                    if differs { 1u64 } else { 0u64 },
                )
            }
            ShadowDecisionOutcome::Undecided { reason } => {
                self.unknown_count = self.unknown_count.saturating_add(1);
                (None, None, Some(reason), 0u64)
            }
        };
        self.taint = shadow_taint_latch(self.taint, row_diff_flag);
        self.rows.push(ShadowPoint {
            ordinal,
            door: door.to_string(),
            recorded: recorded.to_string(),
            differs,
            candidate,
            taint: row_taint,
            needs,
            note,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shadow_seam_answers_out_of_order_within_cutoff_and_never_calls_live() {
        let tape = vec![
            EffectRecord::Clock(1_000),
            EffectRecord::Exchange {
                door: "probe.git".to_string(),
                request: b"status".to_vec(),
                reply: b"clean".to_vec(),
            },
            EffectRecord::Exchange {
                door: "probe.env".to_string(),
                request: b"HOME".to_vec(),
                reply: b"/fixture-home".to_vec(),
            },
            EffectRecord::Exchange {
                door: "probe.git".to_string(),
                request: b"status".to_vec(),
                reply: b"dirty".to_vec(),
            },
        ];
        let view = KeyedView::new(&tape);
        let mut live_never = |_: &[u8]| -> Vec<u8> { panic!("shadow seam must never call live") };

        // At seen = 3, out-of-order lookup sees `HOME` and the FIRST `probe.git` (`clean`), not `dirty` at #3!
        let mut seam = ShadowSeam::new(&tape, &view, 3);
        assert_eq!(
            seam.exchange("probe.env", b"HOME", &mut live_never)
                .unwrap(),
            b"/fixture-home"
        );
        assert_eq!(
            seam.exchange("probe.git", b"status", &mut live_never)
                .unwrap(),
            b"clean"
        );
        assert_eq!(seam.now_nanos().unwrap(), 1_000);

        // Unrecorded probe records a need and returns Unrecorded without calling live.
        let err = seam
            .exchange("probe.net", b"whois", &mut live_never)
            .unwrap_err();
        assert!(matches!(err, ReplayDivergence::Unrecorded { .. }));
        assert_eq!(seam.missing_needs().len(), 1);
        assert_eq!(seam.missing_needs()[0].door, "probe.net");
    }

    #[test]
    fn shadow_ledger_taint_propagation_and_exit_codes_match_aterm() {
        let mut ledger = ShadowLedger::new();
        assert_eq!(ledger.exit_code(), 0);

        // Row 1: identical -> exit_code 0, taint false.
        ledger
            .record_point(
                1,
                "decide.approval",
                "approve",
                ShadowDecisionOutcome::Decided {
                    candidate: "approve".to_string(),
                    differs: false,
                },
                Vec::new(),
            )
            .unwrap();
        assert_eq!(ledger.exit_code(), 0);
        assert!(!ledger.rows()[0].taint);

        // Row 2: undecided -> exit_code 3, taint still false.
        let mut unknown_ledger = ledger.clone();
        unknown_ledger
            .record_point(
                2,
                "decide.turn_end",
                "continue",
                ShadowDecisionOutcome::Undecided {
                    reason: "unrecorded probe".to_string(),
                },
                Vec::new(),
            )
            .unwrap();
        assert_eq!(unknown_ledger.exit_code(), 3);
        assert!(!unknown_ledger.rows()[1].taint);

        // Row 2 on main ledger: differs -> exit_code 1; Row 2 itself has taint=false, Row 3 gets taint=true!
        ledger
            .record_point(
                2,
                "decide.approval",
                "approve",
                ShadowDecisionOutcome::Decided {
                    candidate: "hold".to_string(),
                    differs: true,
                },
                Vec::new(),
            )
            .unwrap();
        ledger
            .record_point(
                3,
                "decide.approval",
                "approve",
                ShadowDecisionOutcome::Decided {
                    candidate: "approve".to_string(),
                    differs: false,
                },
                Vec::new(),
            )
            .unwrap();
        assert_eq!(ledger.exit_code(), 1);
        assert!(!ledger.rows()[1].taint);
        assert!(ledger.rows()[2].taint);
    }
}
