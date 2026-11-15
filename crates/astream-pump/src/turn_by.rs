// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Driver identity attribution (`EVENT turn … by=`) on `aspump` turn-boundary wake lines
//! (`DESIGN-aterm-fabric.md` §15 line 4059, `Astream.Pump.TlaTurnAttribution`).
//!
//! Tracks causal input frontiers per session (`human`, `agent`, `harness`, `local`) so each
//! emitted `EVENT turn` digest line carries exact, monotone `seq=<n>`, `off=<turn_off>`,
//! `cause=<input_off>`, and `by=<kind>:<principal>` attribution without false carry-over
//! across unprompted background output.

#![allow(clippy::manual_is_ascii_check, clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "turn_by_island.rs"]
mod turn_by_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn turn_seq_advance(prev_seq: u64, cand_seq: u64) -> u64 {
    if prev_seq < cand_seq {
        cand_seq
    } else {
        prev_seq
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn turn_driver_len_clamp(driver_len: u64, max_len: u64) -> u64 {
    if driver_len < max_len {
        driver_len
    } else {
        max_len
    }
}
#[cfg(clean_islands)]
pub use turn_by_island::{turn_driver_len_clamp, turn_seq_advance};

/// Maximum UTF-8 byte length of a driver principal identifier on `EVENT turn … by=`.
pub const MAX_TURN_DRIVER_LEN: u64 = 64;

contract_fn! {
    /// Verified causal ordering guard (`cause_off <= turn_off`) for turn attribution,
    /// linked via `clean-kernel-defeq` to `turn_attribution_valid_isl`.
    #[must_use]
    pub const fn turn_attribution_valid(cause_off: u64, turn_off: u64) -> bool
    clauses [ensures result == (cause_off <= turn_off)]
    {
        cause_off <= turn_off
    }
}

/// Origin class of the driver that initiated a terminal turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnDriverKind {
    /// Direct physical keyboard / person-authored input (`human:<id>`).
    Human,
    /// Peer or parent agent session (`agent:<sid>`).
    Agent,
    /// Autopilot harness continuation (`harness:<mode>`).
    Harness,
    /// Unattributed local PTY input (`local:<id>`).
    Local,
}

impl TurnDriverKind {
    /// Canonical prefix in `by=<kind>:<principal>`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Human => "human",
            Self::Agent => "agent",
            Self::Harness => "harness",
            Self::Local => "local",
        }
    }

    /// Parse `human | agent | harness | local`.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "human" => Some(Self::Human),
            "agent" => Some(Self::Agent),
            "harness" => Some(Self::Harness),
            "local" => Some(Self::Local),
            _ => None,
        }
    }
}

/// Canonical attributed `EVENT turn` digest record (`DESIGN-aterm-fabric.md:4059`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttributedTurnEvent {
    /// Monotone 1-based turn sequence number.
    pub seq: u64,
    /// Stream offset of the output record that closed/quiesced the turn.
    pub turn_offset: u64,
    /// Stream offset of the causal input record (`Some(off)` with `off <= turn_offset`, or `None` for initial startup prompt).
    pub cause_offset: Option<u64>,
    /// Driver class (`human`, `agent`, `harness`, `local`) when driven by an input record.
    pub driver_kind: Option<TurnDriverKind>,
    /// Sanitized, length-clamped principal identifier (`<= MAX_TURN_DRIVER_LEN` bytes).
    pub driver_id: String,
}

impl AttributedTurnEvent {
    /// Format canonical single-line digest:
    /// `EVENT turn seq=<seq> off=<turn_off> cause=<off|-> by=<kind:id|none>`
    #[must_use]
    pub fn format_line(&self) -> String {
        let cause_str = match self.cause_offset {
            Some(c) => c.to_string(),
            None => "-".to_string(),
        };
        let by_str = match self.driver_kind {
            Some(k) => format!("{}:{}", k.as_str(), self.driver_id),
            None => "none".to_string(),
        };
        format!(
            "EVENT turn seq={} off={} cause={cause_str} by={by_str}",
            self.seq, self.turn_offset
        )
    }

    /// Parse a canonical `EVENT turn ...` line back into [`AttributedTurnEvent`].
    pub fn parse_line(line: &str) -> Result<Self, &'static str> {
        let Some(rest) = line.strip_prefix("EVENT turn ") else {
            return Err("missing EVENT turn prefix");
        };
        let mut seq: Option<u64> = None;
        let mut turn_off: Option<u64> = None;
        let mut cause_off: Option<Option<u64>> = None;
        let mut by_pair: Option<(Option<TurnDriverKind>, String)> = None;

        for tok in rest.split(' ') {
            if tok.is_empty() {
                continue;
            }
            let Some((k, v)) = tok.split_once('=') else {
                return Err("malformed token");
            };
            match k {
                "seq" => {
                    if seq.is_some() {
                        return Err("duplicate seq");
                    }
                    let Some(n) = parse_u64_dec_str(v) else {
                        return Err("invalid seq");
                    };
                    seq = Some(n);
                }
                "off" => {
                    if turn_off.is_some() {
                        return Err("duplicate off");
                    }
                    let Some(n) = parse_u64_dec_str(v) else {
                        return Err("invalid off");
                    };
                    turn_off = Some(n);
                }
                "cause" => {
                    if cause_off.is_some() {
                        return Err("duplicate cause");
                    }
                    if v == "-" {
                        cause_off = Some(None);
                    } else {
                        let Some(n) = parse_u64_dec_str(v) else {
                            return Err("invalid cause");
                        };
                        cause_off = Some(Some(n));
                    }
                }
                "by" => {
                    if by_pair.is_some() {
                        return Err("duplicate by");
                    }
                    if v == "none" {
                        by_pair = Some((None, String::new()));
                    } else {
                        let Some((kind_s, id_s)) = v.split_once(':') else {
                            return Err("invalid by= value");
                        };
                        let Some(kind) = TurnDriverKind::parse(kind_s) else {
                            return Err("unknown driver kind");
                        };
                        let clamped = match sanitize_driver_id(id_s) {
                            Ok(s) => s,
                            Err(e) => return Err(e),
                        };
                        by_pair = Some((Some(kind), clamped));
                    }
                }
                _ => return Err("unknown field"),
            }
        }

        let (Some(s), Some(toff), Some(coff), Some((dk, did))) =
            (seq, turn_off, cause_off, by_pair)
        else {
            return Err("missing required field");
        };
        if coff.is_some() != dk.is_some() {
            return Err("mismatched cause and by attribution");
        }
        if let Some(c) = coff {
            if !turn_attribution_valid(c, toff) {
                return Err("cause offset exceeds turn offset");
            }
        }
        Ok(Self {
            seq: s,
            turn_offset: toff,
            cause_offset: coff,
            driver_kind: dk,
            driver_id: did,
        })
    }
}

#[derive(Debug, Clone)]
struct PendingDriver {
    input_offset: u64,
    kind: TurnDriverKind,
    principal: String,
}

/// Stateful per-stream turn-attribution tracker.
#[derive(Debug, Clone, Default)]
pub struct TurnAttributionTracker {
    emitted_seq: u64,
    pending: Option<PendingDriver>,
}

impl TurnAttributionTracker {
    /// Create a fresh tracker at `seq = 0`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            emitted_seq: 0,
            pending: None,
        }
    }

    /// Highest turn `seq` emitted so far.
    #[must_use]
    pub const fn emitted_seq(&self) -> u64 {
        self.emitted_seq
    }

    /// Record an observed input record at `input_offset` authored by `(kind, principal)`.
    ///
    /// Note: when multiple inputs arrive before the turn boundary quiesces (e.g., a human
    /// interrupt overriding a harness continuation), a `Human` driver takes precedence over
    /// non-human drivers within the same open turn; otherwise the newest input wins.
    pub fn record_input(
        &mut self,
        input_offset: u64,
        kind: TurnDriverKind,
        principal: &str,
    ) -> Result<(), &'static str> {
        let clean_id = match sanitize_driver_id(principal) {
            Ok(s) => s,
            Err(e) => return Err(e),
        };
        let should_replace = match &self.pending {
            None => true,
            Some(cur) => {
                if cur.kind == TurnDriverKind::Human {
                    kind == TurnDriverKind::Human && input_offset >= cur.input_offset
                } else {
                    kind == TurnDriverKind::Human || input_offset >= cur.input_offset
                }
            }
        };
        if should_replace {
            self.pending = Some(PendingDriver {
                input_offset,
                kind,
                principal: clean_id,
            });
        }
        Ok(())
    }

    /// Emit an [`AttributedTurnEvent`] at `turn_offset`, consuming the pending input
    /// attribution so subsequent unprompted background wakes report `by=none` instead of
    /// stale attribution.
    pub fn emit_turn(&mut self, turn_offset: u64) -> AttributedTurnEvent {
        let cand_seq = self.emitted_seq.saturating_add(1);
        self.emitted_seq = turn_seq_advance(self.emitted_seq, cand_seq);

        if let Some(pend) = self.pending.take() {
            if turn_attribution_valid(pend.input_offset, turn_offset) {
                return AttributedTurnEvent {
                    seq: self.emitted_seq,
                    turn_offset,
                    cause_offset: Some(pend.input_offset),
                    driver_kind: Some(pend.kind),
                    driver_id: pend.principal,
                };
            }
            // Keep future-offset input pending if out-of-order replay inspected an earlier turn.
            self.pending = Some(pend);
        }

        AttributedTurnEvent {
            seq: self.emitted_seq,
            turn_offset,
            cause_offset: None,
            driver_kind: None,
            driver_id: String::new(),
        }
    }
}

const fn parse_u64_dec_str(s: &str) -> Option<u64> {
    let mut rest = s.as_bytes();
    if rest.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    while let &[b, ref tail @ ..] = rest {
        if !matches!(b, b'0'..=b'9') {
            return None;
        }
        let Some(m) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = m.checked_add(b.saturating_sub(b'0') as u64) else {
            return None;
        };
        acc = next;
        rest = tail;
    }
    Some(acc)
}

fn sanitize_driver_id(raw: &str) -> Result<String, &'static str> {
    if raw.is_empty() {
        return Err("empty driver id");
    }
    let bytes = raw.as_bytes();
    let mut scan = 0usize;
    while scan < bytes.len() {
        let Some(&b) = bytes.get(scan) else {
            break;
        };
        let valid = b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.';
        if !valid {
            return Err("invalid character in driver id");
        }
        scan = scan.saturating_add(1);
    }
    let clamped_len = turn_driver_len_clamp(raw.len() as u64, MAX_TURN_DRIVER_LEN) as usize;
    let out_cap = if clamped_len < (MAX_TURN_DRIVER_LEN as usize) {
        clamped_len
    } else {
        MAX_TURN_DRIVER_LEN as usize
    };
    let mut out = {
        let _ = out_cap;
        String::new()
    };
    let mut i = 0usize;
    while i < clamped_len {
        let Some(&b) = bytes.get(i) else {
            break;
        };
        out.push(b as char);
        i = i.saturating_add(1);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attributes_turn_to_driver_and_clears_after_quiesce() {
        let mut tracker = TurnAttributionTracker::new();

        // Startup prompt before any input -> `by=none`.
        let t1 = tracker.emit_turn(0);
        let l1 = t1.format_line();
        assert_eq!(l1, "EVENT turn seq=1 off=0 cause=- by=none");
        assert_eq!(AttributedTurnEvent::parse_line(&l1).unwrap(), t1);

        // Harness types at offset 5, then human interrupts at offset 7 before turn ends at 12:
        // human driver takes precedence!
        tracker
            .record_input(5, TurnDriverKind::Harness, "cruise")
            .unwrap();
        tracker
            .record_input(7, TurnDriverKind::Human, "h-user")
            .unwrap();

        let t2 = tracker.emit_turn(12);
        let l2 = t2.format_line();
        assert_eq!(l2, "EVENT turn seq=2 off=12 cause=7 by=human:h-user");
        assert_eq!(AttributedTurnEvent::parse_line(&l2).unwrap(), t2);

        // Unprompted background output waking at offset 15 does NOT falsely repeat human attribution!
        let t3 = tracker.emit_turn(15);
        assert_eq!(t3.format_line(), "EVENT turn seq=3 off=15 cause=- by=none");
    }

    #[test]
    fn parse_and_tracker_reject_duplicates_mismatched_cause_stale_human_and_tail_injection() {
        assert_eq!(
            AttributedTurnEvent::parse_line("EVENT turn seq=1 seq=2 off=5 cause=3 by=human:h-user"),
            Err("duplicate seq")
        );
        assert_eq!(
            AttributedTurnEvent::parse_line("EVENT turn seq=1 off=5 cause=- by=human:h-user"),
            Err("mismatched cause and by attribution")
        );
        assert_eq!(
            AttributedTurnEvent::parse_line("EVENT turn seq=1 off=5 cause=3 by=none"),
            Err("mismatched cause and by attribution")
        );

        // Invalid byte past MAX_TURN_DRIVER_LEN is rejected before clamping.
        let mut bad_long = "a".repeat(MAX_TURN_DRIVER_LEN as usize);
        bad_long.push(':');
        let mut tracker = TurnAttributionTracker::new();
        assert_eq!(
            tracker.record_input(1, TurnDriverKind::Agent, &bad_long),
            Err("invalid character in driver id")
        );

        // Valid over-long driver id clamps cleanly to MAX_TURN_DRIVER_LEN.
        let valid_long = "a".repeat((MAX_TURN_DRIVER_LEN as usize) + 8);
        tracker
            .record_input(10, TurnDriverKind::Human, &valid_long)
            .unwrap();
        // Out-of-order stale human input at lower offset does NOT overwrite newer human input.
        tracker
            .record_input(4, TurnDriverKind::Human, "stale-human")
            .unwrap();
        let ev = tracker.emit_turn(15);
        assert_eq!(ev.cause_offset, Some(10));
        assert_eq!(ev.driver_id.len(), MAX_TURN_DRIVER_LEN as usize);
    }
}
