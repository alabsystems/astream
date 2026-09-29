//! Speculative local echo + reconciliation (rung 2.5: the smoothness layer).
//!
//! On a high-latency link, waiting for the server to echo each keystroke feels
//! laggy. The [`Predictor`] paints a printable keystroke **immediately** (faint,
//! "unconfirmed") on top of the authoritative screen — before the byte
//! round-trips — then reconciles each prediction against the real `/out` once it
//! arrives.
//!
//! Two properties make this safe to be fast:
//!
//! * **Predictions are local and disposable.** They never touch the log (the
//!   Relaxed path); losing them loses nothing of record.
//! * **They can never corrupt the screen.** After [`reconcile`](Predictor::reconcile),
//!   the [`view`](Predictor::view) equals the pure authoritative fold — every
//!   prediction is either confirmed (it matched) or rolled back to ground truth.
//!   This holds for *any* prediction whatsoever, which is what lets the predictor
//!   guess aggressively without risk.
//!
//! The predictor is deliberately **conservative**: it predicts only a run of
//! ASCII-printable bytes echoed at the cursor (cooked-mode typing) and abstains
//! on anything else — control bytes, escape sequences, the cases a full-screen
//! app (vim, less) would handle unpredictably. Precise per-keystroke confirmation
//! timing (matching each `/out` chunk to the keystroke it answers via a
//! `caused_by` offset) is a later refinement; reconciliation here is positional.
//!
//! Positional verdicts read the authoritative cell: a matching glyph confirms, a
//! cell painted with anything else (a different glyph, or a coloured erase)
//! contradicts, a never-painted blank is undecided (not echoed so far). A
//! predicted **space** is the one glyph a never-painted cell already matches, so
//! it is confirmed only once the authoritative output proves the cell was
//! *traversed*: the cursor has moved past it, **or** a glyph was painted
//! strictly to its right on the same row. The second disjunct is what a repaint
//! needs — a bare `CR`, a `CUP` home, a zle/readline line redraw all echo the
//! space and then put the cursor back at or before it, and without it every such
//! echoed space would be reported `Lost` (and, on the watermark path, stall the
//! walk). Limitation: a repaint that jumps *over* the cell (absolute positioning,
//! then a glyph further right) can still confirm a space that was never echoed —
//! a blank cell carries no "was painted" bit. That residue is strictly narrower
//! than confirming every matching blank, which is what a lost space keystroke
//! being reported `Confirmed` and never retransmitted would mean.

use crate::record::Record;
use crate::screen::{attr, Cell, Color, Folder, Screen};

/// Whether the authoritative output has demonstrably *traversed* `(row, col)`:
/// the cursor sits beyond it, or a glyph was painted strictly to its right on
/// the same row (`line_text` is right-trimmed, so a longer line than
/// `col + 1` chars means a non-blank cell further right). Only a predicted
/// space needs this — every other glyph is its own proof of echo.
fn traversed(screen: &Screen, row: u16, col: u16) -> bool {
    screen.cursor() > (row, col) || screen.line_text(row).chars().count() > col as usize + 1
}

/// The positional verdict for one prediction against the authoritative screen
/// right now, or `None` while it is still undecided (the output has not reached
/// that cell). Shared by every positional retirement path so they cannot drift.
fn verdict_now(screen: &Screen, p: &Prediction) -> Option<Verdict> {
    let cell = screen.cell(p.row, p.col)?;
    if cell.ch == p.ch && (p.ch != ' ' || traversed(screen, p.row, p.col)) {
        // The glyph is there — and for a space (indistinguishable from a blank
        // cell) the output traversed the cell, so it really was echoed: the
        // cursor passed it, or a repaint painted a glyph to its right.
        Some(Verdict::Confirmed)
    } else if *cell != Cell::BLANK {
        // Painted with something else: a different glyph, or an erase that
        // carried a background colour (bce) over the predicted cell.
        Some(Verdict::Contradicted)
    } else {
        None
    }
}

/// The disposition of a prediction once the authoritative output has been folded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The authoritative output painted exactly what was predicted.
    Confirmed,
    /// The authoritative output painted something different at that cell.
    Contradicted,
    /// The authoritative output never painted that cell (the keystroke was not
    /// echoed — e.g. lost, or consumed without echo).
    Lost,
}

#[derive(Debug, Clone)]
struct Prediction {
    client_seq: u64,
    row: u16,
    col: u16,
    ch: char,
    /// The engine in-offset of the keystroke this predicts — set by
    /// [`Predictor::predict_at`], so an echo carrying a `caused_by` in-offset can
    /// retire exactly the prediction it answers, regardless of arrival order.
    in_offset: Option<u64>,
}

/// A client-side speculative-echo overlay over the authoritative screen.
pub struct Predictor {
    base: Folder,
    preds: Vec<Prediction>,
    in_watermark: Option<u64>,
}

impl Predictor {
    /// A predictor over a blank authoritative screen of the given size.
    pub fn new(cols: u16, rows: u16) -> Predictor {
        Predictor {
            base: Folder::new(cols, rows),
            preds: Vec::new(),
            in_watermark: None,
        }
    }

    /// Speculatively echo an input proposal. Predicts only when every byte is
    /// ASCII-printable (cooked-mode typing); otherwise abstains and returns
    /// `false`, leaving the overlay untouched. Predicted glyphs are placed at the
    /// cursor, after any still-outstanding predictions.
    pub fn predict(&mut self, client_seq: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, None, bytes)
    }

    /// Like [`predict`](Self::predict), but stamps each predicted glyph with the
    /// engine **in-offset** of the keystroke, so [`apply_output_caused`](Self::apply_output_caused)
    /// can retire it by exact causal match even when echoes reorder.
    pub fn predict_at(&mut self, client_seq: u64, in_offset: u64, bytes: &[u8]) -> bool {
        self.enqueue(client_seq, Some(in_offset), bytes)
    }

    fn enqueue(&mut self, client_seq: u64, in_offset: Option<u64>, bytes: &[u8]) -> bool {
        if bytes.is_empty() || !bytes.iter().all(|b| (0x20..=0x7e).contains(b)) {
            return false;
        }
        let (cols, _) = self.base.screen().dims();
        // Continue right after the last still-outstanding prediction — which may
        // already have WRAPPED to a later row, so the next cell is not simply
        // `cursor col + preds.len()`.
        let (mut row, mut col) = match self.preds.last() {
            Some(p) => (p.row, p.col.saturating_add(1)),
            None => self.base.screen().cursor(),
        };
        for &b in bytes {
            if col >= cols {
                col = 0;
                row = row.saturating_add(1);
            }
            self.preds.push(Prediction {
                client_seq,
                row,
                col,
                ch: b as char,
                in_offset,
            });
            col = col.saturating_add(1);
        }
        true
    }

    /// Fold one authoritative output (or resize) record into the base screen.
    pub fn apply_output(&mut self, record: &Record) {
        self.base.apply(record);
    }

    /// The highest authoritative out-offset retired so far.
    pub fn in_watermark(&self) -> Option<u64> {
        self.in_watermark
    }

    /// Verified-speculation v1: fold an authoritative output record carrying its
    /// engine **out-offset** (`watermark`), and retire predictions incrementally
    /// against the advanced authoritative state. The watermark is a plain `u64`
    /// (the engine passes `Offset.0`) so this crate stays zero-dependency, and it
    /// is a **different numbering domain** from the per-client `client_seq`.
    ///
    /// Walking the prediction queue from the front: a confirmed prediction (the
    /// authoritative cell now matches — for a space, with the cell shown
    /// traversed) retires; the first contradicted prediction (the cell painted
    /// with something else) retires *and squashes the whole speculative tail*
    /// (everything queued after it was built on a now-invalid state); an
    /// undecided prediction (a never-painted cell) stops the walk. An out-of-order (non-advancing) watermark is
    /// rejected — it neither advances nor retires. Returns each affected
    /// `(client_seq, verdict)`.
    ///
    /// Retirement is by **monotone out-offset progress, not by causal link**;
    /// exact `caused_by` retirement (which `Out` chunk a keystroke produced) is a
    /// later rung. The safety theorem is preserved: the authoritative screen is a
    /// pure fold of the recorded output, untouched by any prediction.
    pub fn apply_output_at(&mut self, watermark: u64, record: &Record) -> Vec<(u64, Verdict)> {
        if let Some(w) = self.in_watermark {
            if watermark <= w {
                return Vec::new(); // out-of-order watermark: reject, do not advance
            }
        }
        self.in_watermark = Some(watermark);
        self.base.apply(record);

        let mut verdicts = Vec::new();
        let mut confirmed = 0usize;
        let mut contradicted = false;
        for p in &self.preds {
            match verdict_now(self.base.screen(), p) {
                Some(Verdict::Confirmed) => {
                    verdicts.push((p.client_seq, Verdict::Confirmed));
                    confirmed += 1;
                }
                Some(_) => {
                    verdicts.push((p.client_seq, Verdict::Contradicted));
                    contradicted = true;
                    break;
                }
                None => break, // undecided: the authoritative output has not reached it
            }
        }
        if contradicted {
            // Squash the whole tail after the contradiction (speculated on a bad path).
            for p in &self.preds[confirmed + 1..] {
                verdicts.push((p.client_seq, Verdict::Lost));
            }
            self.preds.clear();
        } else {
            self.preds.drain(0..confirmed);
        }
        verdicts
    }

    /// Verified-speculation v2: retire by **exact `caused_by` causal match**, not
    /// position. Fold the authoritative output, then retire the one prediction
    /// whose recorded in-offset equals the in-offset this `Out` answers (decoded
    /// engine-side from `caused_by`, passed as a plain `u64`), deciding its verdict
    /// by comparing the **`Out`'s printable bytes** to the predicted char — not a
    /// screen-cell lookup. This is correct even when echoes **reorder or batch**,
    /// where the positional [`apply_output_at`](Self::apply_output_at) mis-assigns
    /// the cell at the cursor to the wrong keystroke. An `Out` with no `caused_by`
    /// (or no matching prediction) retires nothing. Returns the affected
    /// `(client_seq, verdict)`.
    ///
    /// The safety theorem is preserved: the authoritative screen is still a pure
    /// fold of the recorded output, untouched by any prediction. Under reorder that
    /// screen is the fold of the arrival-order stream — `caused_by` corrects the
    /// verdict assignment, not the screen's order-sensitivity.
    pub fn apply_output_caused(
        &mut self,
        _out_offset: u64,
        in_offset_for_out: Option<u64>,
        record: &Record,
    ) -> Vec<(u64, Verdict)> {
        self.base.apply(record);
        let (Some(in_off), Record::Out(bytes)) = (in_offset_for_out, record) else {
            return Vec::new();
        };
        let Some(pos) = self.preds.iter().position(|p| p.in_offset == Some(in_off)) else {
            return Vec::new();
        };
        let p = self.preds.remove(pos);
        // A predicted glyph is always ASCII-printable (see `enqueue`), so it is
        // among the Out's printable bytes iff that byte occurs in the Out at all.
        let verdict = if bytes.contains(&(p.ch as u8)) {
            Verdict::Confirmed
        } else {
            Verdict::Contradicted
        };
        vec![(p.client_seq, verdict)]
    }

    /// The authoritative screen, with no predictions overlaid.
    pub fn authoritative(&self) -> &Screen {
        self.base.screen()
    }

    /// What the user sees: the authoritative screen with the still-unconfirmed
    /// predictions painted on top (faint).
    pub fn view(&self) -> Screen {
        let mut screen = self.base.screen().clone();
        for p in &self.preds {
            screen.set_cell(
                p.row,
                p.col,
                Cell {
                    ch: p.ch,
                    fg: Color::Default,
                    bg: Color::Default,
                    attrs: attr::FAINT,
                },
            );
        }
        screen
    }

    /// Reconcile every outstanding prediction against the authoritative screen
    /// and clear them. Returns each prediction's `client_seq` and its verdict: a
    /// still-undecided prediction (its cell never painted — a space over a cell
    /// nothing traversed included) is `Lost`. After this call
    /// [`view`](Self::view) equals the authoritative screen.
    pub fn reconcile(&mut self) -> Vec<(u64, Verdict)> {
        let verdicts = self
            .preds
            .iter()
            .map(|p| {
                let verdict = verdict_now(self.base.screen(), p).unwrap_or(Verdict::Lost);
                (p.client_seq, verdict)
            })
            .collect();
        self.preds.clear();
        verdicts
    }
}
