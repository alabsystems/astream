// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Turn-level supervisor state machine for driving a nested interactive TUI agent
//! (such as Claude Code under [`astream_term::events::Profile::claude`]) end-to-end
//! over `astream-host::Pty` + `Driver`, `astream-broker`, and `aspump`
//! (`Astream.Pump.TlaNestedDrive`).
//!
//! Ensures every `PROMPT_READY boffset=<N>` boundary is driven at most once across
//! supervisor/pump restarts (`nested_turn_ready_to_drive`), bounds injected prompt
//! sizes (`nested_prompt_bytes_clamp` / [`MAX_NESTED_PROMPT_BYTES`]), and allocates
//! strictly monotone `(producer_id, turn_seq)` keys (`nested_turn_seq_advance`) so
//! `astream-host::Driver::drive_input` deduplicates any replayed in-flight turn.

use std::io;

#[cfg(clean_islands)]
#[path = "nested_drive_island.rs"]
mod nested_drive_island;

#[cfg(not(clean_islands))]
pub use crate::twins::{nested_prompt_bytes_clamp, nested_turn_seq_advance};
#[cfg(clean_islands)]
pub use nested_drive_island::{nested_prompt_bytes_clamp, nested_turn_seq_advance};

/// Maximum single-turn prompt byte length injected into a nested agent PTY.
pub const MAX_NESTED_PROMPT_BYTES: u64 = 16_384;

contract_fn! {
    /// Kernel-verified guard ensuring a newly woken `PROMPT_READY` offset strictly
    /// exceeds the last driven prompt offset (`last_driven_boffset < woken_boffset`),
    /// linked via `clean-kernel-defeq` to `nested_turn_ready_to_drive_isl`.
    #[must_use]
    pub const fn nested_turn_ready_to_drive(
        woken_boffset: u64,
        last_driven_boffset: u64,
    ) -> bool
    clauses [ensures result == (last_driven_boffset < woken_boffset)]
    {
        last_driven_boffset < woken_boffset
    }
}

fn parse_u64_token(raw: &str) -> Option<u64> {
    if raw.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in raw.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = acc
            .checked_mul(10)?
            .checked_add(u64::from(b.saturating_sub(b'0')))?;
    }
    Some(acc)
}

/// Extract `boffset` from a `PROMPT_READY boffset=<N>[ ...]` wake line; returns `None`
/// for `QUIESCED`, `COMMAND_START`, `COMMAND_END`, or malformed lines.
#[must_use]
pub fn parse_prompt_ready_boffset(wake_line: &str) -> Option<u64> {
    let trimmed = wake_line.trim_end_matches(['\r', '\n']);
    let rest = trimmed.strip_prefix("PROMPT_READY ")?;
    for tok in rest.split(' ') {
        if let Some(val) = tok.strip_prefix("boffset=") {
            return parse_u64_token(val);
        }
    }
    None
}

/// Monotone turn-admission gate for an outer supervisor driving a nested PTY agent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedTurnState {
    producer_id: u64,
    turn_seq: u64,
    last_driven_boffset: Option<u64>,
}

impl NestedTurnState {
    /// Construct a fresh or resumed nested-agent turn controller for `producer_id`.
    #[must_use]
    pub const fn new(
        producer_id: u64,
        initial_turn_seq: u64,
        last_driven_boffset: Option<u64>,
    ) -> Self {
        Self {
            producer_id,
            turn_seq: initial_turn_seq,
            last_driven_boffset,
        }
    }

    /// Producer ID passed to `Driver::drive_input` for PTY-side deduplication.
    #[must_use]
    pub const fn producer_id(&self) -> u64 {
        self.producer_id
    }

    /// Highest turn sequence admitted so far.
    #[must_use]
    pub const fn turn_seq(&self) -> u64 {
        self.turn_seq
    }

    /// Last `/out` broker offset whose `PROMPT_READY` boundary triggered a turn.
    #[must_use]
    pub const fn last_driven_boffset(&self) -> Option<u64> {
        self.last_driven_boffset
    }

    /// Admit a `PROMPT_READY` boundary at `woken_boffset` for `prompt_bytes`.
    ///
    /// Returns `Ok(None)` when `woken_boffset` has already been driven (e.g. a
    /// re-delivered wake after a crash before group commit), `Err(InvalidInput)` if
    /// `prompt_bytes` is empty or exceeds [`MAX_NESTED_PROMPT_BYTES`], or
    /// `Ok(Some((producer_id, turn_seq)))` for `Driver::drive_input`.
    pub fn admit_prompt_wake(
        &mut self,
        woken_boffset: u64,
        prompt_bytes: &[u8],
    ) -> io::Result<Option<(u64, u64)>> {
        if prompt_bytes.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "nested prompt payload must not be empty",
            ));
        }
        let raw_len = prompt_bytes.len() as u64;
        let clamped = nested_prompt_bytes_clamp(raw_len, MAX_NESTED_PROMPT_BYTES);
        if clamped < raw_len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "nested prompt payload exceeds MAX_NESTED_PROMPT_BYTES",
            ));
        }
        if let Some(last) = self.last_driven_boffset {
            if !nested_turn_ready_to_drive(woken_boffset, last) {
                return Ok(None);
            }
        }
        let cand = self.turn_seq.saturating_add(1);
        let next_seq = nested_turn_seq_advance(self.turn_seq, cand);
        self.turn_seq = next_seq;
        self.last_driven_boffset = Some(woken_boffset);
        Ok(Some((self.producer_id, next_seq)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_turn_state_parses_wakes_and_deduplicates_offsets() {
        assert_eq!(
            parse_prompt_ready_boffset("PROMPT_READY boffset=0 cwd=/repo title=Claude"),
            Some(0)
        );
        assert_eq!(
            parse_prompt_ready_boffset("PROMPT_READY boffset=42\n"),
            Some(42)
        );
        assert_eq!(parse_prompt_ready_boffset("QUIESCED boffset=42"), None);
        assert_eq!(
            parse_prompt_ready_boffset("COMMAND_END boffset=5 exit=0"),
            None
        );

        let mut st = NestedTurnState::new(99, 0, None);
        assert_eq!(st.admit_prompt_wake(0, b"first\n").unwrap(), Some((99, 1)));
        assert_eq!(st.admit_prompt_wake(0, b"dup\n").unwrap(), None);
        assert_eq!(st.admit_prompt_wake(5, b"second\n").unwrap(), Some((99, 2)));
        assert_eq!(st.admit_prompt_wake(3, b"stale\n").unwrap(), None);
        assert_eq!(st.turn_seq(), 2);
        assert_eq!(st.last_driven_boffset(), Some(5));
    }
}
