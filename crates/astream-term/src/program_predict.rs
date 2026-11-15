// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Verified program-response speculation `P̂` (`docs/THEORY-deterministic-sessions.md` §3,
//! `docs/ROADMAP.md` "a predictor `P̂` for program responses").
//!
//! Where [`crate::Predictor`] predicts only cooked-mode ASCII-printable glyphs and
//! abstains on control bytes, escape sequences, and alternate-screen TUIs,
//! [`ProgramPredictor`] learns causal `(ScreenContext, input_bytes) -> Vec<ScreenOp>`
//! transitions online from authoritative `Out` records stamped with `caused_by`
//! in-offsets and speculatively projects full [`ScreenOp`] responses across high-RTT
//! links before the round-trip completes.
//!
//! ## Safety & Confluence Guarantees (`TlaProgramSpeculation`)
//!
//! 1. **Ground-Truth Confluence (`view() == authoritative()` once quiescent):**
//!    speculative transitions never touch `base` (the pure authoritative [`Folder`]).
//!    Once every pending speculative transition is causally retired or reconciled,
//!    [`ProgramPredictor::view`] returns `base.screen().clone()` verbatim.
//! 2. **Screen-Level Confluence Check:** if a program emits a different VT byte stream
//!    that folds to the *exact same* [`Screen`] as predicted (e.g., `MoveTo(2, 0)` vs
//!    `\r\n`), causal retirement confirms [`Verdict::Confirmed`] with zero visual glitch.
//! 3. **Squash-and-Rebuild:** if an authoritative response contradicts an earlier
//!    in-flight prediction, [`ProgramPredictor`] squashes the stale intermediate path
//!    and re-projects all remaining in-flight inputs on top of the new ground-truth
//!    screen using the updated transition table.
//! 4. **Bounded Memory:** the learned rule cache is capped at [`MAX_PROGRAM_RULES`]
//!    (`program_rule_cap_clamp`), input keys at [`MAX_RULE_INPUT_BYTES`], and per-rule
//!    op vectors at [`MAX_OPS_PER_RULE`] (`program_ops_within_cap`).

use crate::ops::ScreenOp;
use crate::predict::{echo_admit_causal_watermark, watermark_advances, Verdict};
use crate::record::Record;
use crate::screen::{apply_ops_to, attr, Cell, Color, Folder, Screen};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "program_predict_island.rs"]
mod program_predict_island;
#[cfg(not(clean_islands))]
pub use crate::twins::program_rule_cap_clamp;
#[cfg(clean_islands)]
pub use program_predict_island::program_rule_cap_clamp;

/// Maximum number of learned `(context, input) -> Vec<ScreenOp>` rules retained.
pub const MAX_PROGRAM_RULES: usize = 256;

/// Maximum byte length of an input sequence eligible for transition learning.
pub const MAX_RULE_INPUT_BYTES: usize = 64;

/// Maximum number of [`ScreenOp`]s stored in a single learned transition rule.
pub const MAX_OPS_PER_RULE: usize = 128;

contract_fn! {
    /// Kernel-certified check that a learned `ScreenOp` sequence fits within `cap`
    /// (`ops_len <= cap`), linked via `clean-kernel-defeq` to `program_ops_within_cap_isl`.
    #[must_use]
    pub const fn program_ops_within_cap(ops_len: usize, cap: usize) -> bool
    clauses [ensures result == (ops_len <= cap)]
    {
        ops_len <= cap
    }
}

/// Compact deterministic fingerprint of the screen state preceding an input event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScreenContext {
    /// Viewport `(cols, rows)`.
    pub dims: (u16, u16),
    /// Whether the alternate screen (`?1049`/`?47`/`?1047`) is active.
    pub altscreen: bool,
    /// Zero-based `(row, col)` cursor coordinates.
    pub cursor: (u16, u16),
    /// 64-bit FNV-1a digest over the cells of the cursor's current row.
    pub row_hash: u64,
}

impl ScreenContext {
    /// Extract the [`ScreenContext`] of `screen` with zero heap allocation.
    #[must_use]
    pub fn of(screen: &Screen) -> Self {
        let dims = screen.dims();
        let cursor = screen.cursor();
        let altscreen = screen.is_altscreen();
        let row_hash = hash_row_cells(screen, cursor.0, dims.0);
        Self {
            dims,
            altscreen,
            cursor,
            row_hash,
        }
    }
}

fn fnv1a_step(state: u64, byte: u8) -> u64 {
    (state ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
}

fn hash_color(mut h: u64, c: Color) -> u64 {
    match c {
        Color::Default => fnv1a_step(h, 0),
        Color::Indexed(idx) => {
            h = fnv1a_step(h, 1);
            fnv1a_step(h, idx)
        }
    }
}

fn hash_opt_rgb(mut h: u64, rgb: Option<(u8, u8, u8)>) -> u64 {
    match rgb {
        None => fnv1a_step(h, 0),
        Some((r, g, b)) => {
            h = fnv1a_step(h, 1);
            h = fnv1a_step(h, r);
            h = fnv1a_step(h, g);
            fnv1a_step(h, b)
        }
    }
}

fn hash_row_cells(screen: &Screen, row: u16, cols: u16) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut col = 0u16;
    while col < cols {
        if let Some(cell) = screen.cell(row, col) {
            let cp = cell.ch as u32;
            h = fnv1a_step(h, cp as u8);
            h = fnv1a_step(h, (cp >> 8) as u8);
            h = fnv1a_step(h, (cp >> 16) as u8);
            h = fnv1a_step(h, (cp >> 24) as u8);
            h = hash_color(h, cell.fg);
            h = hash_color(h, cell.bg);
            h = hash_opt_rgb(h, cell.fg_rgb);
            h = hash_opt_rgb(h, cell.bg_rgb);
            h = fnv1a_step(h, cell.attrs);
            h = fnv1a_step(h, cell.underline.code());
            h = hash_color(h, cell.ul);
            h = hash_opt_rgb(h, cell.ul_rgb);
            h = fnv1a_step(h, cell.width);
            h = fnv1a_step(h, cell.combining_len);
            for &m in cell.combining_marks() {
                let mcp = m as u32;
                h = fnv1a_step(h, mcp as u8);
                h = fnv1a_step(h, (mcp >> 8) as u8);
                h = fnv1a_step(h, (mcp >> 16) as u8);
                h = fnv1a_step(h, (mcp >> 24) as u8);
            }
        }
        col = col.saturating_add(1);
    }
    h
}

const fn all_ascii_printable(mut bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    while let &[b, ref tail @ ..] = bytes {
        if b < 0x20 || b > 0x7e {
            return false;
        }
        bytes = tail;
    }
    true
}

const fn is_cursor_relative_op(op: &ScreenOp) -> bool {
    match op {
        ScreenOp::Print(_)
        | ScreenOp::CarriageReturn
        | ScreenOp::LineFeed
        | ScreenOp::Tab
        | ScreenOp::Backspace
        | ScreenOp::CursorUp(_)
        | ScreenOp::CursorDown(_)
        | ScreenOp::CursorForward(_)
        | ScreenOp::CursorBack(_)
        | ScreenOp::EraseLine(_)
        | ScreenOp::EraseChars(_)
        | ScreenOp::InsertChars(_)
        | ScreenOp::DeleteChars(_)
        | ScreenOp::InsertLines(_)
        | ScreenOp::DeleteLines(_)
        | ScreenOp::ReverseIndex
        | ScreenOp::SetSgr { .. }
        | ScreenOp::SetSgrRgb { .. }
        | ScreenOp::SetUnderline { .. }
        | ScreenOp::ScrollUp(_)
        | ScreenOp::ScrollDown(_) => true,
        ScreenOp::MoveTo(_, _)
        | ScreenOp::EraseDisplay(_)
        | ScreenOp::SetMode { .. }
        | ScreenOp::SaveCursor
        | ScreenOp::RestoreCursor
        | ScreenOp::SetScrollRegion { .. }
        | ScreenOp::SetInsertMode(_)
        | ScreenOp::SetNewlineMode(_)
        | ScreenOp::Designate { .. }
        | ScreenOp::LockShift { .. }
        | ScreenOp::SetLeftRightMargins { .. }
        | ScreenOp::Reset
        | ScreenOp::Resize(_, _) => false,
    }
}

/// Returns `true` iff every op in `ops` is cursor-relative (no absolute `MoveTo`,
/// whole-screen erase, mode switch, scroll-region/margin reset, or resize), so a
/// transition learned on one row generalizes safely across rows in the same mode.
#[must_use]
pub fn is_cursor_relative_ops(ops: &[ScreenOp]) -> bool {
    if ops.is_empty() {
        return false;
    }
    for op in ops {
        if !is_cursor_relative_op(op) {
            return false;
        }
    }
    true
}

#[derive(Debug, Clone)]
struct LearnedRule {
    context: ScreenContext,
    input: Vec<u8>,
    ops: Vec<ScreenOp>,
    cursor_relative: bool,
}

#[derive(Debug, Clone)]
struct PendingTransition {
    client_seq: u64,
    in_offset: Option<u64>,
    pre_context: ScreenContext,
    input: Vec<u8>,
    predicted_ops: Vec<ScreenOp>,
    post_screen: Screen,
}

#[derive(Debug, Clone)]
struct ObservedInput {
    in_offset: u64,
    pre_context: ScreenContext,
    input: Vec<u8>,
}

/// Verified program-response predictor `P̂` over a recording [`Folder`].
#[derive(Debug, Clone)]
pub struct ProgramPredictor {
    base: Folder,
    rules: Vec<LearnedRule>,
    pending: Vec<PendingTransition>,
    observed: Vec<ObservedInput>,
    in_watermark: Option<u64>,
    hits: u64,
    misses: u64,
    abstentions: u64,
}

impl ProgramPredictor {
    /// Construct a fresh [`ProgramPredictor`] over a blank `(cols, rows)` screen.
    #[must_use]
    pub fn new(cols: u16, rows: u16) -> Self {
        Self {
            base: Folder::new_recording(cols, rows),
            rules: Vec::new(),
            pending: Vec::new(),
            observed: Vec::new(),
            in_watermark: None,
            hits: 0,
            misses: 0,
            abstentions: 0,
        }
    }

    /// Borrow the pure authoritative [`Screen`] (never touched by speculation).
    #[must_use]
    pub fn authoritative(&self) -> &Screen {
        self.base.screen()
    }

    /// Highest authoritative `out_offset` causally retired so far.
    #[must_use]
    pub const fn in_watermark(&self) -> Option<u64> {
        self.in_watermark
    }

    /// Number of learned `(context, input) -> Vec<ScreenOp>` rules currently cached.
    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.rules.len()
    }

    /// Number of unconfirmed speculative transitions currently in flight.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Count of causally retired predictions confirmed by ground truth.
    #[must_use]
    pub const fn hits(&self) -> u64 {
        self.hits
    }

    /// Count of causally retired predictions contradicted by ground truth.
    #[must_use]
    pub const fn misses(&self) -> u64 {
        self.misses
    }

    /// Count of `predict` / `predict_at` calls where `P̂` abstained (no matching rule).
    #[must_use]
    pub const fn abstentions(&self) -> u64 {
        self.abstentions
    }

    /// Empirical confirmation rate in integer basis points (`0..=10_000`, where
    /// `10_000` = `100.00%`; returns `10_000` when `hits + misses == 0`).
    #[must_use]
    pub const fn hit_rate_bps(&self) -> u64 {
        let total = self.hits.saturating_add(self.misses);
        if total == 0 {
            10_000
        } else {
            let scaled = (self.hits as u128) * 10_000u128;
            (scaled / (total as u128)) as u64
        }
    }

    /// Explicitly seed or overwrite a learned `(ScreenContext::of(screen), input) -> ops`
    /// transition rule. Returns `false` if `input` or `ops` exceeds the bounded caps.
    pub fn seed_rule(&mut self, screen: &Screen, input: &[u8], ops: Vec<ScreenOp>) -> bool {
        let ctx = ScreenContext::of(screen);
        self.insert_rule(ctx, input, ops)
    }

    fn insert_rule(&mut self, ctx: ScreenContext, input: &[u8], ops: Vec<ScreenOp>) -> bool {
        if input.is_empty()
            || !program_ops_within_cap(input.len(), MAX_RULE_INPUT_BYTES)
            || ops.is_empty()
            || !program_ops_within_cap(ops.len(), MAX_OPS_PER_RULE)
        {
            return false;
        }
        let cursor_relative = is_cursor_relative_ops(&ops);
        // Update in place if an exact `(context, input)` entry already exists, moving it
        // to the back (most-recently-updated) so newer rules take precedence.
        let mut kept = Vec::new();
        for existing in &self.rules {
            if !(existing.context == ctx && existing.input.as_slice() == input) {
                kept.push(existing.clone());
            }
        }
        let keep_cap = program_rule_cap_clamp(
            kept.len() as u64,
            (MAX_PROGRAM_RULES.saturating_sub(1)) as u64,
        ) as usize;
        let drop_front = kept.len().saturating_sub(keep_cap);
        let mut bounded = Vec::new();
        if let Some(tail) = kept.get(drop_front..) {
            bounded.extend_from_slice(tail);
        }
        bounded.push(LearnedRule {
            context: ctx,
            input: input.to_vec(),
            ops,
            cursor_relative,
        });
        self.rules = bounded;
        true
    }

    /// Predict the [`ScreenOp`] sequence for `input` from `ctx`:
    /// 1. Most-recent exact `(dims, altscreen, cursor, row_hash, input)` rule;
    /// 2. Most-recent cursor-relative `(dims, altscreen, input)` rule;
    /// 3. Main-screen ASCII-printable fallback (`ScreenOp::Print` per byte).
    #[must_use]
    pub fn lookup_ops(&self, ctx: &ScreenContext, input: &[u8]) -> Option<Vec<ScreenOp>> {
        if input.is_empty() {
            return None;
        }
        // Reverse scan so the newest learned transition wins.
        let mut idx = self.rules.len();
        while idx > 0 {
            idx -= 1;
            if let Some(rule) = self.rules.get(idx) {
                if rule.context == *ctx && rule.input.as_slice() == input {
                    return Some(rule.ops.clone());
                }
            }
        }
        let mut rel_idx = self.rules.len();
        while rel_idx > 0 {
            rel_idx -= 1;
            if let Some(rule) = self.rules.get(rel_idx) {
                if rule.cursor_relative
                    && rule.context.dims == ctx.dims
                    && rule.context.altscreen == ctx.altscreen
                    && rule.input.as_slice() == input
                {
                    return Some(rule.ops.clone());
                }
            }
        }
        if !ctx.altscreen
            && all_ascii_printable(input)
            && program_ops_within_cap(input.len(), MAX_OPS_PER_RULE)
        {
            let mut ops = Vec::new();
            for &b in input {
                ops.push(ScreenOp::Print(b as char));
            }
            return Some(ops);
        }
        None
    }

    /// Speculatively predict the screen effect of `bytes` without an engine `in_offset`.
    pub fn predict(&mut self, client_seq: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, None, bytes)
    }

    /// Speculatively predict the screen effect of `bytes` stamped with its engine
    /// `in_offset`. Even when `P̂` abstains on a cold-start TUI keystroke (returning
    /// `false`), it records `(in_offset, ScreenContext, bytes)` so the ensuing causal
    /// `Out` teaches `P̂` the transition for subsequent presses.
    pub fn predict_at(&mut self, client_seq: u64, in_offset: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, Some(in_offset), bytes)
    }

    fn enqueue(&mut self, client_seq: u64, in_offset: Option<u64>, bytes: &[u8]) -> bool {
        let pre_screen = match self.pending.last() {
            Some(last) => &last.post_screen,
            None => self.base.screen(),
        };
        let pre_context = ScreenContext::of(pre_screen);
        if !program_ops_within_cap(self.pending.len().saturating_add(1), MAX_PROGRAM_RULES) {
            if let Some(in_off) = in_offset {
                if !bytes.is_empty() && program_ops_within_cap(bytes.len(), MAX_RULE_INPUT_BYTES) {
                    self.record_observed(in_off, pre_context, bytes);
                }
            }
            self.abstentions = self.abstentions.saturating_add(1);
            return false;
        }
        let Some(predicted_ops) = self.lookup_ops(&pre_context, bytes) else {
            if let Some(in_off) = in_offset {
                if !bytes.is_empty() && program_ops_within_cap(bytes.len(), MAX_RULE_INPUT_BYTES) {
                    self.record_observed(in_off, pre_context, bytes);
                }
            }
            self.abstentions = self.abstentions.saturating_add(1);
            return false;
        };
        let mut post_screen = pre_screen.clone();
        apply_ops_to(&mut post_screen, &predicted_ops);
        self.pending.push(PendingTransition {
            client_seq,
            in_offset,
            pre_context,
            input: bytes.to_vec(),
            predicted_ops,
            post_screen,
        });
        true
    }

    fn record_observed(&mut self, in_offset: u64, pre_context: ScreenContext, bytes: &[u8]) {
        let keep_cap = program_rule_cap_clamp(
            self.observed.len() as u64,
            (MAX_PROGRAM_RULES.saturating_sub(1)) as u64,
        ) as usize;
        let drop_front = self.observed.len().saturating_sub(keep_cap);
        let mut next_obs = Vec::new();
        if let Some(tail) = self.observed.get(drop_front..) {
            next_obs.extend_from_slice(tail);
        }
        next_obs.push(ObservedInput {
            in_offset,
            pre_context,
            input: bytes.to_vec(),
        });
        self.observed = next_obs;
    }

    /// Fold an authoritative record without causal offset metadata and re-project any
    /// outstanding speculative transitions on top of the updated authoritative screen.
    pub fn apply_output(&mut self, record: &Record) {
        let _ = self.base.take_ops();
        self.base.apply(record);
        let _ = self.base.take_ops();
        let _ = self.rebuild_pending();
    }

    /// Fold an authoritative record at `out_offset` with optional `caused_by`
    /// `in_offset_for_out`:
    /// - Learns `(pre_context, input) -> actual_ops` into the bounded rule cache (both
    ///   for predicted transitions and for cold-start abstentions recorded via
    ///   [`predict_at`](Self::predict_at)).
    /// - Confirms via exact op equality OR screen-level confluence
    ///   (`base.screen() == &post_screen`), or contradicts and squash-rebuilds remaining
    ///   in-flight speculative transitions on top of the new authoritative screen.
    pub fn apply_output_caused(
        &mut self,
        out_offset: u64,
        in_offset_for_out: Option<u64>,
        record: &Record,
    ) -> Vec<(u64, Verdict)> {
        let _ = self.base.take_ops();
        self.base.apply(record);
        let actual_ops = self.base.take_ops();

        let Some(in_off) = in_offset_for_out else {
            let mut verdicts = self.rebuild_pending();
            let _ = &mut verdicts;
            return verdicts;
        };

        // Teach cold-start abstained inputs first.
        let mut obs_match: Option<ObservedInput> = None;
        let mut kept_obs = Vec::new();
        for item in &self.observed {
            if obs_match.is_none() && item.in_offset == in_off {
                obs_match = Some(item.clone());
            } else {
                kept_obs.push(item.clone());
            }
        }
        self.observed = kept_obs;
        if let Some(obs) = obs_match {
            let _ = self.insert_rule(obs.pre_context, &obs.input, actual_ops.clone());
        }

        let mut found_pos = None;
        for (idx, p) in self.pending.iter().enumerate() {
            if p.in_offset == Some(in_off) {
                found_pos = Some(idx);
                break;
            }
        }
        let Some(pos) = found_pos else {
            return self.rebuild_pending();
        };
        let Some(entry) = self.pending.get(pos).cloned() else {
            return Vec::new();
        };

        let mut remaining = Vec::new();
        if let Some(head) = self.pending.get(..pos) {
            remaining.extend_from_slice(head);
        }
        if let Some(tail) = self.pending.get(pos.saturating_add(1)..) {
            remaining.extend_from_slice(tail);
        }
        self.pending = remaining;

        if let Some(pred_in_off) = entry.in_offset {
            let cur_wm = self.in_watermark.unwrap_or(out_offset);
            self.in_watermark = Some(echo_admit_causal_watermark(
                in_off,
                pred_in_off,
                cur_wm,
                out_offset,
            ));
        }

        // Update learned transition table with authoritative ops.
        let _ = self.insert_rule(entry.pre_context, &entry.input, actual_ops.clone());

        let confluent = actual_ops == entry.predicted_ops
            || (pos == 0 && self.base.screen() == &entry.post_screen);
        let verdict = if confluent {
            self.hits = self.hits.saturating_add(1);
            Verdict::Confirmed
        } else {
            self.misses = self.misses.saturating_add(1);
            Verdict::Contradicted
        };

        let mut verdicts = vec![(entry.client_seq, verdict)];
        if !confluent || pos > 0 {
            let lost = self.rebuild_pending();
            verdicts.extend(lost);
        }
        verdicts
    }

    fn rebuild_pending(&mut self) -> Vec<(u64, Verdict)> {
        if self.pending.is_empty() {
            return Vec::new();
        }
        let old = std::mem::take(&mut self.pending);
        let mut rebuilt: Vec<PendingTransition> = Vec::new();
        let mut retired = Vec::new();
        for item in old {
            let pre_screen = match rebuilt.last() {
                Some(prev) => &prev.post_screen,
                None => self.base.screen(),
            };
            let pre_context = ScreenContext::of(pre_screen);
            if let Some(ops) = self.lookup_ops(&pre_context, &item.input) {
                let mut post_screen = pre_screen.clone();
                apply_ops_to(&mut post_screen, &ops);
                rebuilt.push(PendingTransition {
                    client_seq: item.client_seq,
                    in_offset: item.in_offset,
                    pre_context,
                    input: item.input,
                    predicted_ops: ops,
                    post_screen,
                });
            } else {
                retired.push((item.client_seq, Verdict::Lost));
            }
        }
        self.pending = rebuilt;
        retired
    }

    /// Render the user-visible [`Screen`]:
    /// - When `pending` is empty, returns `authoritative().clone()` byte-for-byte
    ///   (`ProgramSpecSafetyInv`).
    /// - When speculative transitions are in flight, returns the latest speculative
    ///   `post_screen` with `attr::FAINT` applied to every cell that differs from the
    ///   authoritative screen.
    #[must_use]
    pub fn view(&self) -> Screen {
        let auth = self.base.screen();
        let Some(last) = self.pending.last() else {
            return auth.clone();
        };
        let mut out = last.post_screen.clone();
        let (cols, rows) = out.dims();
        if auth.dims() == (cols, rows) {
            let mut r = 0u16;
            while r < rows {
                let mut c = 0u16;
                while c < cols {
                    if let (Some(ac), Some(sc)) = (auth.cell(r, c), out.cell(r, c)) {
                        if ac != sc {
                            let faint_cell = Cell {
                                attrs: sc.attrs | attr::FAINT,
                                ..*sc
                            };
                            out.set_cell(r, c, faint_cell);
                        }
                    }
                    c = c.saturating_add(1);
                }
                r = r.saturating_add(1);
            }
        }
        out
    }

    /// Reconcile and clear all outstanding speculative transitions against the current
    /// authoritative [`Screen`]. After this call, [`pending_count`](Self::pending_count)
    /// is `0` and [`view`](Self::view) equals [`authoritative`](Self::authoritative)
    /// byte-for-byte.
    pub fn reconcile(&mut self) -> Vec<(u64, Verdict)> {
        let mut verdicts = Vec::new();
        let auth = self.base.screen();
        for item in &self.pending {
            let verdict = if auth == &item.post_screen {
                Verdict::Confirmed
            } else {
                Verdict::Lost
            };
            verdicts.push((item.client_seq, verdict));
        }
        self.pending.clear();
        self.observed.clear();
        verdicts
    }
}

const fn contains_line_break(mut bytes: &[u8]) -> bool {
    while let &[b, ref tail @ ..] = bytes {
        if b == b'\r' || b == b'\n' {
            return true;
        }
        bytes = tail;
    }
    false
}

fn is_masked_or_silent_echo(input: &[u8], actual_ops: &[ScreenOp]) -> bool {
    if !all_ascii_printable(input) {
        return false;
    }
    if actual_ops.is_empty() {
        return true;
    }
    if actual_ops.len() == 1 && input != b"*" {
        if let Some(ScreenOp::Print('*') | ScreenOp::Print('•')) = actual_ops.first() {
            return true;
        }
    }
    false
}

fn is_literal_printable_echo(input: &[u8], actual_ops: &[ScreenOp]) -> bool {
    if !all_ascii_printable(input) || input.len() != actual_ops.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < input.len() {
        match (input.get(idx), actual_ops.get(idx)) {
            (Some(&b), Some(ScreenOp::Print(ch))) if (b as char) == *ch => {}
            _ => return false,
        }
        idx = idx.saturating_add(1);
    }
    true
}

fn ops_strict_prefix(prefix: &[ScreenOp], full: &[ScreenOp]) -> bool {
    !prefix.is_empty() && prefix.len() < full.len() && full.get(..prefix.len()) == Some(prefix)
}

/// Unified speculative terminal combining:
/// 1. Learned `P̂` [`ProgramPredictor`] `(ScreenContext, input) -> Vec<ScreenOp>` rules
///    (for alternate-screen TUIs, REPL prompts, and custom bindings);
/// 2. Zero-cold-start cooked/readline main-screen speculation for printable ASCII runs AND
///    cursor-motion / line-editing keys (`ESC [ D`, `ESC [ C`, `0x7f`/`0x08` Backspace);
/// 3. Automatic echo suppression on silent/masked (`stty -echo` / password) prompt rows
///    after a single contradicted keystroke until newline or row change;
/// 4. Dual retirement: exact `caused_by` causal retirement ([`Self::apply_output_caused`])
///    and monotone engine `out_offset` watermark squash-and-rebuild ([`Self::apply_output_at`]).
#[derive(Debug, Clone)]
pub struct SpeculativeTerminal {
    inner: ProgramPredictor,
    out_watermark: Option<u64>,
    no_echo_row: Option<(u16, u16, bool, u16)>,
    squashes: u64,
}

impl SpeculativeTerminal {
    /// Construct a fresh [`SpeculativeTerminal`] over a blank `(cols, rows)` viewport.
    #[must_use]
    pub fn new(cols: u16, rows: u16) -> Self {
        Self {
            inner: ProgramPredictor::new(cols, rows),
            out_watermark: None,
            no_echo_row: None,
            squashes: 0,
        }
    }

    /// Borrow the pure authoritative [`Screen`] (never mutated by speculation).
    #[must_use]
    pub fn authoritative(&self) -> &Screen {
        self.inner.authoritative()
    }

    /// Render the user-visible [`Screen`] (byte-equal to [`Self::authoritative`] whenever
    /// [`Self::pending_count`] is `0`).
    #[must_use]
    pub fn view(&self) -> Screen {
        self.inner.view()
    }

    /// Highest authoritative `out_offset` retired on the `caused_by` path.
    #[must_use]
    pub const fn in_watermark(&self) -> Option<u64> {
        self.inner.in_watermark()
    }

    /// Highest monotone authoritative `out_offset` retired via [`Self::apply_output_at`].
    #[must_use]
    pub const fn out_watermark(&self) -> Option<u64> {
        self.out_watermark
    }

    /// Number of learned `(context, input) -> Vec<ScreenOp>` rules currently cached.
    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.inner.rule_count()
    }

    /// Number of unconfirmed speculative transitions currently in flight.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.inner.pending_count()
    }

    /// Count of retired predictions confirmed against authoritative ground truth.
    #[must_use]
    pub const fn hits(&self) -> u64 {
        self.inner.hits()
    }

    /// Count of retired predictions contradicted by authoritative ground truth.
    #[must_use]
    pub const fn misses(&self) -> u64 {
        self.inner.misses()
    }

    /// Count of input proposals on which [`SpeculativeTerminal`] abstained.
    #[must_use]
    pub const fn abstentions(&self) -> u64 {
        self.inner.abstentions()
    }

    /// Count of speculative squash-and-rebuild events triggered by contradictions.
    #[must_use]
    pub const fn squashes(&self) -> u64 {
        self.squashes
    }

    /// Precision among attempted predictions in basis points (`hits / (hits + misses)`).
    #[must_use]
    pub const fn precision_bps(&self) -> u64 {
        self.inner.hit_rate_bps()
    }

    /// Overall corpus hit rate in integer basis points (`0..=10_000`) across ALL input
    /// events (`hits / (hits + misses + abstentions)`), immune to abstention gaming.
    #[must_use]
    pub const fn corpus_hit_rate_bps(&self) -> u64 {
        let total = self
            .inner
            .hits
            .saturating_add(self.inner.misses)
            .saturating_add(self.inner.abstentions);
        if total == 0 {
            0
        } else {
            let scaled = (self.inner.hits as u128) * 10_000u128;
            (scaled / (total as u128)) as u64
        }
    }

    /// Seed or overwrite an explicit `(ScreenContext::of(screen), input) -> ops` rule.
    pub fn seed_rule(&mut self, screen: &Screen, input: &[u8], ops: Vec<ScreenOp>) -> bool {
        self.inner.seed_rule(screen, input, ops)
    }

    fn is_no_echo_active(&self, ctx: &ScreenContext) -> bool {
        self.no_echo_row == Some((ctx.dims.0, ctx.dims.1, ctx.altscreen, ctx.cursor.0))
    }

    fn sync_no_echo_after_fold(&mut self) {
        if let Some((cols, rows, alt, row)) = self.no_echo_row {
            let auth = self.inner.base.screen();
            if auth.dims() != (cols, rows) || auth.is_altscreen() != alt || auth.cursor().0 != row {
                self.no_echo_row = None;
            }
        }
    }

    /// Resolve speculative [`ScreenOp`]s for `input` from `ctx`:
    /// 1. Suppresses printable main-screen speculation if `ctx` sits on an active
    ///    no-echo/masked prompt row;
    /// 2. Checks exact `(dims, altscreen, cursor, row_hash, input)` learned rules;
    /// 3. Checks cursor-relative `(dims, altscreen, input)` learned rules;
    /// 4. Falls back on main screen to printable ASCII echo and cooked/readline cursor
    ///    & backspace editing (`ESC [ D`, `ESC [ C`, `0x7f`/`0x08`).
    #[must_use]
    pub fn lookup_ops(&self, ctx: &ScreenContext, input: &[u8]) -> Option<Vec<ScreenOp>> {
        if input.is_empty() {
            return None;
        }
        if !ctx.altscreen && self.is_no_echo_active(ctx) && all_ascii_printable(input) {
            return None;
        }
        let mut idx = self.inner.rules.len();
        while idx > 0 {
            idx -= 1;
            if let Some(rule) = self.inner.rules.get(idx) {
                if rule.context == *ctx && rule.input.as_slice() == input {
                    return Some(rule.ops.clone());
                }
            }
        }
        let mut rel_idx = self.inner.rules.len();
        while rel_idx > 0 {
            rel_idx -= 1;
            if let Some(rule) = self.inner.rules.get(rel_idx) {
                if rule.cursor_relative
                    && rule.context.dims == ctx.dims
                    && rule.context.altscreen == ctx.altscreen
                    && rule.input.as_slice() == input
                {
                    return Some(rule.ops.clone());
                }
            }
        }
        if !ctx.altscreen {
            if all_ascii_printable(input) && program_ops_within_cap(input.len(), MAX_OPS_PER_RULE) {
                let mut ops = Vec::new();
                for &b in input {
                    ops.push(ScreenOp::Print(b as char));
                }
                return Some(ops);
            }
            if input == b"\x1b[D" && ctx.cursor.1 > 0 {
                return Some(vec![ScreenOp::CursorBack(1)]);
            }
            if input == b"\x1b[C" && ctx.cursor.1.saturating_add(1) < ctx.dims.0 {
                return Some(vec![ScreenOp::CursorForward(1)]);
            }
            if (input == b"\x7f" || input == b"\x08") && ctx.cursor.1 > 0 {
                return Some(vec![ScreenOp::Backspace, ScreenOp::DeleteChars(1)]);
            }
        }
        None
    }

    /// Speculatively predict the screen effect of `bytes` without an engine `in_offset`.
    pub fn predict(&mut self, client_seq: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, None, bytes)
    }

    /// Speculatively predict the screen effect of `bytes` stamped with its engine `in_offset`.
    pub fn predict_at(&mut self, client_seq: u64, in_offset: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, Some(in_offset), bytes)
    }

    fn enqueue(&mut self, client_seq: u64, in_offset: Option<u64>, bytes: &[u8]) -> bool {
        if contains_line_break(bytes) {
            self.no_echo_row = None;
        }
        let pre_screen = match self.inner.pending.last() {
            Some(last) => &last.post_screen,
            None => self.inner.base.screen(),
        };
        let pre_context = ScreenContext::of(pre_screen);
        if !program_ops_within_cap(
            self.inner.pending.len().saturating_add(1),
            MAX_PROGRAM_RULES,
        ) {
            if let Some(in_off) = in_offset {
                if !bytes.is_empty() && program_ops_within_cap(bytes.len(), MAX_RULE_INPUT_BYTES) {
                    self.inner.record_observed(in_off, pre_context, bytes);
                }
            }
            self.inner.abstentions = self.inner.abstentions.saturating_add(1);
            return false;
        }
        let Some(predicted_ops) = self.lookup_ops(&pre_context, bytes) else {
            if let Some(in_off) = in_offset {
                if !bytes.is_empty() && program_ops_within_cap(bytes.len(), MAX_RULE_INPUT_BYTES) {
                    self.inner.record_observed(in_off, pre_context, bytes);
                }
            }
            self.inner.abstentions = self.inner.abstentions.saturating_add(1);
            return false;
        };
        let mut post_screen = pre_screen.clone();
        apply_ops_to(&mut post_screen, &predicted_ops);
        self.inner.pending.push(PendingTransition {
            client_seq,
            in_offset,
            pre_context,
            input: bytes.to_vec(),
            predicted_ops,
            post_screen,
        });
        true
    }

    fn rebuild_pending_unified(&mut self) -> Vec<(u64, Verdict)> {
        if self.inner.pending.is_empty() {
            return Vec::new();
        }
        let old = std::mem::take(&mut self.inner.pending);
        let mut rebuilt: Vec<PendingTransition> = Vec::new();
        let mut retired = Vec::new();
        for item in old {
            let pre_screen = match rebuilt.last() {
                Some(prev) => &prev.post_screen,
                None => self.inner.base.screen(),
            };
            let pre_context = ScreenContext::of(pre_screen);
            if let Some(ops) = self.lookup_ops(&pre_context, &item.input) {
                let mut post_screen = pre_screen.clone();
                apply_ops_to(&mut post_screen, &ops);
                rebuilt.push(PendingTransition {
                    client_seq: item.client_seq,
                    in_offset: item.in_offset,
                    pre_context,
                    input: item.input,
                    predicted_ops: ops,
                    post_screen,
                });
            } else {
                retired.push((item.client_seq, Verdict::Lost));
            }
        }
        self.inner.pending = rebuilt;
        retired
    }

    /// Fold an authoritative record without watermark or causal metadata and re-project
    /// any outstanding speculative transitions on top of the updated authoritative screen.
    pub fn apply_output(&mut self, record: &Record) {
        let _ = self.inner.base.take_ops();
        self.inner.base.apply(record);
        let _ = self.inner.base.take_ops();
        self.sync_no_echo_after_fold();
        let _ = self.rebuild_pending_unified();
    }

    /// Monotone `out_offset` watermark retirement with squash-and-rebuild:
    /// - Rejects stale/duplicate `watermark` (`!watermark_advances(cur, watermark)`).
    /// - Confirms any non-empty prefix `0..=k` of in-flight predictions whose cumulative
    ///   `post_screen` now matches the authoritative screen (handling batched echoes).
    /// - Keeps partial multi-glyph echoes pending when `actual_ops` is a strict prefix
    ///   of the head prediction's `predicted_ops`.
    /// - Otherwise marks the head prediction `Contradicted`, increments `squashes`,
    ///   engages row echo-suppression if silent/masked, and squash-rebuilds remaining
    ///   in-flight inputs over the new authoritative ground truth.
    pub fn apply_output_at(&mut self, watermark: u64, record: &Record) -> Vec<(u64, Verdict)> {
        if let Some(cur) = self.out_watermark {
            if !watermark_advances(cur, watermark) {
                return Vec::new();
            }
        }
        self.out_watermark = Some(watermark);

        let _ = self.inner.base.take_ops();
        self.inner.base.apply(record);
        let actual_ops = self.inner.base.take_ops();
        self.sync_no_echo_after_fold();

        if self.inner.pending.is_empty() {
            return Vec::new();
        }

        // Check if authoritative screen reached `pending[k].post_screen` (including batched echoes).
        let mut matched_thru: Option<usize> = None;
        for (idx, item) in self.inner.pending.iter().enumerate() {
            if self.inner.base.screen() == &item.post_screen {
                matched_thru = Some(idx);
            }
        }
        if let Some(k) = matched_thru {
            let mut verdicts = Vec::new();
            let confirmed_len = k.saturating_add(1);
            if let Some(prefix) = self.inner.pending.get(..confirmed_len) {
                for item in prefix {
                    verdicts.push((item.client_seq, Verdict::Confirmed));
                    self.inner.hits = self.inner.hits.saturating_add(1);
                }
            }
            let mut tail_vec = Vec::new();
            if let Some(tail) = self.inner.pending.get(confirmed_len..) {
                tail_vec.extend_from_slice(tail);
            }
            self.inner.pending = tail_vec;
            return verdicts;
        }

        if actual_ops.is_empty() {
            return Vec::new();
        }

        // Partial echo of a multi-op head prediction (e.g., "ls" echoed as "l" then "s"):
        // trim the already-applied prefix and wait for the rest of the echo only if
        // applying the remaining suffix on top of the updated authoritative screen still
        // reaches `head.post_screen`.
        let base_screen = self.inner.base.screen().clone();
        if let Some(head) = self.inner.pending.first_mut() {
            if ops_strict_prefix(&actual_ops, &head.predicted_ops) {
                let mut rem = Vec::new();
                if let Some(suffix) = head.predicted_ops.get(actual_ops.len()..) {
                    rem.extend_from_slice(suffix);
                }
                let mut projected = base_screen;
                apply_ops_to(&mut projected, &rem);
                if projected == head.post_screen {
                    head.predicted_ops = rem;
                    return Vec::new();
                }
            }
        }

        // Contradiction on the head prediction: retire it Contradicted and squash-rebuild tail.
        let Some(head_entry) = self.inner.pending.first().cloned() else {
            return Vec::new();
        };
        let mut rest = Vec::new();
        if let Some(tail) = self.inner.pending.get(1..) {
            rest.extend_from_slice(tail);
        }
        self.inner.pending = rest;
        self.inner.misses = self.inner.misses.saturating_add(1);
        self.squashes = self.squashes.saturating_add(1);

        if !head_entry.pre_context.altscreen
            && is_masked_or_silent_echo(&head_entry.input, &actual_ops)
        {
            let auth = self.inner.base.screen();
            self.no_echo_row = Some((
                auth.dims().0,
                auth.dims().1,
                auth.is_altscreen(),
                auth.cursor().0,
            ));
        }

        let mut verdicts = vec![(head_entry.client_seq, Verdict::Contradicted)];
        let lost = self.rebuild_pending_unified();
        verdicts.extend(lost);
        verdicts
    }

    /// Exact `caused_by` causal retirement with online `P̂` rule learning, no-echo prompt
    /// detection, and squash-and-rebuild on contradiction.
    pub fn apply_output_caused(
        &mut self,
        out_offset: u64,
        in_offset_for_out: Option<u64>,
        record: &Record,
    ) -> Vec<(u64, Verdict)> {
        let _ = self.inner.base.take_ops();
        self.inner.base.apply(record);
        let actual_ops = self.inner.base.take_ops();
        self.sync_no_echo_after_fold();

        let Some(in_off) = in_offset_for_out else {
            return self.rebuild_pending_unified();
        };

        let mut obs_match: Option<ObservedInput> = None;
        let mut kept_obs = Vec::new();
        for item in &self.inner.observed {
            if obs_match.is_none() && item.in_offset == in_off {
                obs_match = Some(item.clone());
            } else {
                kept_obs.push(item.clone());
            }
        }
        self.inner.observed = kept_obs;
        if let Some(obs) = obs_match {
            if is_literal_printable_echo(&obs.input, &actual_ops) {
                self.no_echo_row = None;
            }
            let _ = self
                .inner
                .insert_rule(obs.pre_context, &obs.input, actual_ops.clone());
        }

        let mut found_pos = None;
        for (idx, p) in self.inner.pending.iter().enumerate() {
            if p.in_offset == Some(in_off) {
                found_pos = Some(idx);
                break;
            }
        }
        let Some(pos) = found_pos else {
            return self.rebuild_pending_unified();
        };
        let Some(entry) = self.inner.pending.get(pos).cloned() else {
            return Vec::new();
        };

        let mut remaining = Vec::new();
        if let Some(head) = self.inner.pending.get(..pos) {
            remaining.extend_from_slice(head);
        }
        if let Some(tail) = self.inner.pending.get(pos.saturating_add(1)..) {
            remaining.extend_from_slice(tail);
        }
        self.inner.pending = remaining;

        if let Some(pred_in_off) = entry.in_offset {
            let cur_wm = self.inner.in_watermark.unwrap_or(out_offset);
            self.inner.in_watermark = Some(echo_admit_causal_watermark(
                in_off,
                pred_in_off,
                cur_wm,
                out_offset,
            ));
        }

        // Only cache non-printable or altscreen rules, or custom non-identity printable rules,
        // so normal cooked ASCII typing doesn't evict TUI/REPL command rules from the cache.
        if entry.pre_context.altscreen || !is_literal_printable_echo(&entry.input, &actual_ops) {
            let _ = self
                .inner
                .insert_rule(entry.pre_context, &entry.input, actual_ops.clone());
        } else {
            self.no_echo_row = None;
        }

        let confluent = actual_ops == entry.predicted_ops
            || (pos == 0 && self.inner.base.screen() == &entry.post_screen);
        let verdict = if confluent {
            self.inner.hits = self.inner.hits.saturating_add(1);
            Verdict::Confirmed
        } else {
            self.inner.misses = self.inner.misses.saturating_add(1);
            self.squashes = self.squashes.saturating_add(1);
            if !entry.pre_context.altscreen && is_masked_or_silent_echo(&entry.input, &actual_ops) {
                let auth = self.inner.base.screen();
                self.no_echo_row = Some((
                    auth.dims().0,
                    auth.dims().1,
                    auth.is_altscreen(),
                    auth.cursor().0,
                ));
            }
            Verdict::Contradicted
        };

        let mut verdicts = vec![(entry.client_seq, verdict)];
        if !confluent || pos > 0 {
            let lost = self.rebuild_pending_unified();
            verdicts.extend(lost);
        }
        verdicts
    }

    /// Reconcile and clear all outstanding speculative transitions against the current
    /// authoritative [`Screen`]. Guarantees `pending_count() == 0` and
    /// `view().serialize() == authoritative().serialize()`.
    pub fn reconcile(&mut self) -> Vec<(u64, Verdict)> {
        self.inner.reconcile()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pending_queue_is_bounded_by_max_program_rules() {
        let mut st = SpeculativeTerminal::new(80, 24);
        for seq in 0..(MAX_PROGRAM_RULES as u64) {
            assert!(st.predict(seq, b"a"));
        }
        assert_eq!(st.pending_count(), MAX_PROGRAM_RULES);
        assert!(!st.predict(MAX_PROGRAM_RULES as u64, b"a"));
        assert_eq!(st.pending_count(), MAX_PROGRAM_RULES);
        assert_eq!(st.abstentions(), 1);
    }

    #[test]
    fn apply_output_at_handles_split_echo_prefix_confluently() {
        let mut st = SpeculativeTerminal::new(80, 24);
        assert!(st.predict(1, b"ls"));
        assert!(st
            .apply_output_at(1, &Record::Out(b"l".to_vec()))
            .is_empty());
        assert_eq!(st.pending_count(), 1);
        let verdicts = st.apply_output_at(2, &Record::Out(b"s".to_vec()));
        assert_eq!(verdicts, vec![(1, Verdict::Confirmed)]);
        assert_eq!(st.pending_count(), 0);
    }
}
