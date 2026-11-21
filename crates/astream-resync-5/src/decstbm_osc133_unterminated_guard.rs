// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! xterm `DECSTBM`/`CUU`/`CUD` margin-clamp oracle parity & unterminated `OSC 133` abort guard
//! (`Astream.Term.TlaDecstbmOsc133UnterminatedGuard`).
//!
//! Enforces both VT/shell-integration parity rules verified against the `aterm` oracle:
//! 1. **xterm `CUU`/`CUD` margin rules**:
//!    - `CUU(n)` stops at `top_margin` ONLY when `cursor_row >= top_margin`; if the cursor is
//!      already above `top_margin` (`cursor_row < top_margin`), `CUU(n)` moves toward row `0`!
//!    - `CUD(n)` stops at `bottom_margin` ONLY when `cursor_row <= bottom_margin`; if the cursor
//!      is already below `bottom_margin`, `CUD(n)` moves toward `screen_rows - 1`!
//! 2. **Unterminated `OSC 133` recovery**:
//!    - An unterminated `ESC ] 133 ; ...` sequence is aborted cleanly on `CAN` (`0x18`), `SUB`
//!      (`0x1A`), payload cap (`MAX_OSC133_PAYLOAD_BYTES`), or a fresh `ESC ]` introducer so a
//!      truncated sequence NEVER swallows subsequent `133;A/B/C/D` prompt marks!

#[cfg(clean_islands)]
#[path = "decstbm_osc133_unterminated_guard_island.rs"]
mod decstbm_osc133_unterminated_guard_island;
#[cfg(clean_islands)]
pub use decstbm_osc133_unterminated_guard_island::{
    osc133_mark_seq_advance_b141, osc133_payload_clamp_b141,
};

/// Maximum payload buffered inside a single `OSC 133` command/prompt mark (`1_024` bytes).
pub const MAX_OSC133_PAYLOAD_BYTES: u64 = 1_024;

#[cfg(not(clean_islands))]
/// Clamp buffered `OSC 133` payload length to `max_osc_bytes`.
#[must_use]
pub const fn osc133_payload_clamp_b141(cand_len: u64, max_osc_bytes: u64) -> u64 {
    if cand_len < max_osc_bytes {
        cand_len
    } else {
        max_osc_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the emitted `OSC 133` prompt-mark sequence counter.
#[must_use]
pub const fn osc133_mark_seq_advance_b141(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `cursor_row` starts inside `[top_margin, bottom_margin]`.
    #[must_use]
    pub const fn xterm_cursor_inside_margins_b141(
        cursor_row: u64,
        top_margin: u64,
        bottom_margin: u64,
    ) -> bool
    clauses [ensures result == (top_margin <= cursor_row && cursor_row <= bottom_margin)]
    {
        top_margin <= cursor_row && cursor_row <= bottom_margin
    }
}

/// Compute `CUU(delta)` destination row under xterm's `DECSTBM` rule (`0`-indexed rows).
#[must_use]
pub const fn xterm_cuu_row(cursor_row: u64, delta: u64, top_margin: u64) -> u64 {
    let step = if delta == 0 { 1 } else { delta };
    let floor = if cursor_row >= top_margin {
        top_margin
    } else {
        0
    };
    let moved = cursor_row.saturating_sub(step);
    if moved < floor {
        floor
    } else {
        moved
    }
}

/// Compute `CUD(delta)` destination row under xterm's `DECSTBM` rule (`0`-indexed rows).
#[must_use]
pub const fn xterm_cud_row(
    cursor_row: u64,
    delta: u64,
    bottom_margin: u64,
    last_screen_row: u64,
) -> u64 {
    let step = if delta == 0 { 1 } else { delta };
    let ceiling = if cursor_row <= bottom_margin {
        bottom_margin
    } else {
        last_screen_row
    };
    let moved = cursor_row.saturating_add(step);
    if moved > ceiling {
        ceiling
    } else {
        moved
    }
}

/// Outcome of feeding a byte/introducer into the `OSC 133` framing guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc133GuardEvent {
    Accumulating { buf_len: u64 },
    AbortedUnterminatedAndReset,
    EmittedMark { mark_kind: u8, mark_seq: u64 },
}

/// Bounded `OSC 133` state machine that aborts unterminated marks instead of swallowing new ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc133UnterminatedGuard {
    in_osc133: bool,
    pending_kind: u8,
    osc_buf_len: u64,
    mark_seq: u64,
}

impl Osc133UnterminatedGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            in_osc133: false,
            pending_kind: 0,
            osc_buf_len: 0,
            mark_seq: 0,
        }
    }

    /// Begin a fresh `ESC ] 133 ; <kind>`: if an earlier `OSC 133` was left unterminated,
    /// discard the partial state and start the new mark cleanly!
    pub fn begin_osc133(&mut self, mark_kind: u8) -> bool {
        let aborted_prior = self.in_osc133;
        self.in_osc133 = true;
        self.pending_kind = mark_kind;
        self.osc_buf_len = 0;
        aborted_prior
    }

    pub fn feed_osc_byte(&mut self, byte: u8) -> Osc133GuardEvent {
        if !self.in_osc133 {
            return Osc133GuardEvent::AbortedUnterminatedAndReset;
        }
        // BEL (`0x07`) terminates OSC cleanly:
        if byte == 0x07 {
            self.in_osc133 = false;
            self.osc_buf_len = 0;
            let next_seq = self.mark_seq.saturating_add(1);
            self.mark_seq = osc133_mark_seq_advance_b141(self.mark_seq, next_seq);
            return Osc133GuardEvent::EmittedMark {
                mark_kind: self.pending_kind,
                mark_seq: self.mark_seq,
            };
        }
        // CAN (`0x18`), SUB (`0x1A`), or overflow aborts the unterminated OSC:
        if byte == 0x18 || byte == 0x1A || self.osc_buf_len >= MAX_OSC133_PAYLOAD_BYTES {
            self.in_osc133 = false;
            self.osc_buf_len = 0;
            return Osc133GuardEvent::AbortedUnterminatedAndReset;
        }
        let next_len = self.osc_buf_len.saturating_add(1);
        self.osc_buf_len = osc133_payload_clamp_b141(next_len, MAX_OSC133_PAYLOAD_BYTES);
        Osc133GuardEvent::Accumulating {
            buf_len: self.osc_buf_len,
        }
    }
}

impl Default for Osc133UnterminatedGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xterm_cuu_cud_respect_margin_boundaries_and_unterminated_osc133_never_swallows_next_mark() {
        assert!(xterm_cursor_inside_margins_b141(5, 2, 10));
        // Inside scroll region `[2, 10]`, `CUU(99)` clamps at `2`, `CUD(99)` clamps at `10`:
        assert_eq!(xterm_cuu_row(5, 99, 2), 2);
        assert_eq!(xterm_cud_row(5, 99, 10, 23), 10);
        // Above `top_margin` (`row = 1 < 2`), `CUU(5)` moves to `0`:
        assert_eq!(xterm_cuu_row(1, 5, 2), 0);
        // Below `bottom_margin` (`row = 12 > 10`), `CUD(99)` moves to `23`:
        assert_eq!(xterm_cud_row(12, 99, 10, 23), 23);

        let mut osc = Osc133UnterminatedGuard::new();
        assert!(!osc.begin_osc133(b'A'));
        assert_eq!(
            osc.feed_osc_byte(b'x'),
            Osc133GuardEvent::Accumulating { buf_len: 1 }
        );
        // Unterminated `133;A` followed by a fresh `ESC ] 133 ; B BEL` aborts `A` and emits `B`!
        assert!(osc.begin_osc133(b'B'));
        assert_eq!(
            osc.feed_osc_byte(0x07),
            Osc133GuardEvent::EmittedMark {
                mark_kind: b'B',
                mark_seq: 1
            }
        );
    }
}
