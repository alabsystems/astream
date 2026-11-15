// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `EVENT turn … by=<driver>` digest provenance attestor
//! (`docs/DESIGN-aterm-fabric.md` §14 Q4, §14 line 3921, §15 line 4059;
//! `Astream.Agent.TlaEventTurnByDriverAttestor`).
//!
//! Stamps exact, unforgeable driver provenance onto `EVENT turn <n> … by=<src>` digest lines:
//! - Distinguishes inferred physical keyboard input (`holder=human?`) from authenticated local
//!   `ctl` owners, Autopilot (`cruise` / `land`), and cap-bound fabric drivers,
//! - Monotonically advances `attested_turn_id` and clamps `by=` token byte lengths to `MAX_BY_BYTES`
//!   (`48` ASCII bytes, preventing context injection through driver names).

#[cfg(clean_islands)]
#[path = "event_turn_by_driver_attestor_island.rs"]
mod event_turn_by_driver_attestor_island;
#[cfg(clean_islands)]
pub use event_turn_by_driver_attestor_island::{turn_by_len_clamp_b129, turn_id_advance_b129};

#[cfg(not(clean_islands))]
/// Clamp `by=<token>` byte length to `max_by_bytes` (`48`).
#[must_use]
pub const fn turn_by_len_clamp_b129(cand_len: u64, max_by_bytes: u64) -> u64 {
    if cand_len < max_by_bytes {
        cand_len
    } else {
        max_by_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `attested_turn_id`.
#[must_use]
pub const fn turn_id_advance_b129(cur_turn: u64, cand_turn: u64) -> u64 {
    if cur_turn < cand_turn {
        cand_turn
    } else {
        cur_turn
    }
}

contract_fn! {
    /// True iff `candidate_turn > attested_turn_id && by_token_len > 0`.
    #[must_use]
    pub const fn turn_by_fresh_and_nonempty_b129(
        candidate_turn: u64,
        attested_turn_id: u64,
        by_token_len: u64,
    ) -> bool
    clauses [ensures result == (candidate_turn > attested_turn_id && by_token_len > 0)]
    {
        candidate_turn > attested_turn_id && by_token_len > 0
    }
}

pub const MAX_BY_TOKEN_BYTES: u64 = 48;

/// Closed-vocabulary provenance of the actor that drove a settled turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnDriverProvenance {
    /// Physical keyboard input (inferred: rendered as `human?` per §14 line 3921).
    HumanKeyboardInferred,
    /// Authenticated local `aterm ctl` socket owner.
    LocalCtlOwner,
    /// `aterm` harness under `autopilot=cruise`.
    AutopilotCruise,
    /// `aterm` harness under `autopilot=land`.
    AutopilotLand,
    /// Remote `aterm ctl --host <h>` TLS step-in operator.
    FleetTlsStepIn,
}

/// Attestation result for an `EVENT turn` digest line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnByAttestOutcome {
    Attested {
        turn_id: u64,
        provenance: TurnDriverProvenance,
        inferred_marker: bool,
        clamped_by_bytes: u64,
    },
    RefusedStaleOrEmptyTurn {
        candidate_turn: u64,
        attested_turn_id: u64,
    },
}

/// Stateful `EVENT turn … by=` digest attestor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EventTurnByDriverAttestor {
    attested_turn_id: u64,
    max_by_bytes: u64,
}

impl EventTurnByDriverAttestor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            attested_turn_id: 0,
            max_by_bytes: MAX_BY_TOKEN_BYTES,
        }
    }

    #[must_use]
    pub const fn attested_turn_id(&self) -> u64 {
        self.attested_turn_id
    }

    /// Attest a settled turn `candidate_turn` driven by `provenance` with `raw_by_token_bytes`.
    pub fn attest_turn(
        &mut self,
        candidate_turn: u64,
        provenance: TurnDriverProvenance,
        raw_by_token_bytes: u64,
    ) -> TurnByAttestOutcome {
        if !turn_by_fresh_and_nonempty_b129(
            candidate_turn,
            self.attested_turn_id,
            raw_by_token_bytes,
        ) {
            return TurnByAttestOutcome::RefusedStaleOrEmptyTurn {
                candidate_turn,
                attested_turn_id: self.attested_turn_id,
            };
        }
        self.attested_turn_id = turn_id_advance_b129(self.attested_turn_id, candidate_turn);
        TurnByAttestOutcome::Attested {
            turn_id: self.attested_turn_id,
            provenance,
            inferred_marker: matches!(provenance, TurnDriverProvenance::HumanKeyboardInferred),
            clamped_by_bytes: turn_by_len_clamp_b129(raw_by_token_bytes, self.max_by_bytes),
        }
    }
}

impl Default for EventTurnByDriverAttestor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marks_physical_keyboard_as_inferred_clamps_by_token_and_rejects_stale_turns() {
        let mut att = EventTurnByDriverAttestor::new();

        assert_eq!(
            att.attest_turn(1, TurnDriverProvenance::HumanKeyboardInferred, 6),
            TurnByAttestOutcome::Attested {
                turn_id: 1,
                provenance: TurnDriverProvenance::HumanKeyboardInferred,
                inferred_marker: true,
                clamped_by_bytes: 6,
            }
        );
        assert_eq!(
            att.attest_turn(2, TurnDriverProvenance::AutopilotCruise, 120),
            TurnByAttestOutcome::Attested {
                turn_id: 2,
                provenance: TurnDriverProvenance::AutopilotCruise,
                inferred_marker: false,
                clamped_by_bytes: MAX_BY_TOKEN_BYTES,
            }
        );
        // Duplicate/stale turn 2 rejected.
        assert_eq!(
            att.attest_turn(2, TurnDriverProvenance::LocalCtlOwner, 10),
            TurnByAttestOutcome::RefusedStaleOrEmptyTurn {
                candidate_turn: 2,
                attested_turn_id: 2,
            }
        );
    }
}
