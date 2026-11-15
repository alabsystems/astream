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
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "predict_island.rs"]
mod predict_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{echo_causal_watermark_select, echo_watermark_monotone};
#[cfg(clean_islands)]
pub use predict_island::{echo_causal_watermark_select, echo_watermark_monotone};

contract_fn! {
    /// Kernel-certified check that a new authoritative out-offset `new_wm` strictly
    /// advances past `cur_wm` (`cur_wm < new_wm`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `watermark_advances_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn watermark_advances(cur_wm: u64, new_wm: u64) -> bool
    clauses [ensures result == (cur_wm < new_wm)]
    {
        cur_wm < new_wm
    }
}

/// Multi-condition speculative-echo causal watermark admission kernel:
/// advances `cur_wm` to `max(cur_wm, cand_wm)` when the authoritative `Out`'s
/// `caused_by` offset `in_off` matches `pred_in_off`, or retains `cur_wm` otherwise.
///
/// Hand-written plain Rust, not compiled from Clean: it restates
/// `Astream.Term.TlaSpeculativeEcho.echo_admit_causal_watermark_isl`, the island's
/// composition of the Clean-Origin (`I5`) functions [`echo_causal_watermark_select`] and
/// [`echo_watermark_monotone`], and the `predict` suite holds it to that composition over a
/// grid of boundary operands.
#[must_use]
pub const fn echo_admit_causal_watermark(
    in_off: u64,
    pred_in_off: u64,
    cur_wm: u64,
    cand_wm: u64,
) -> u64 {
    let next_wm = if cur_wm < cand_wm { cand_wm } else { cur_wm };
    if in_off == pred_in_off {
        next_wm
    } else {
        cur_wm
    }
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

const fn slice_contains_byte(mut bytes: &[u8], needle: u8) -> bool {
    while let &[b, ref tail @ ..] = bytes {
        if b == needle {
            return true;
        }
        bytes = tail;
    }
    false
}

/// Row-text lengths are valid only during one immutable verdict pass. Keep
/// the current row inline; a second queried row lazily uses a sparse directory.
/// Revisited rows retain the exact scalar-count result without a persistent
/// screen cache or a viewport-sized allocation for ordinary single-row typing.
#[derive(Default)]
struct RowTextLengths {
    current: Option<(u16, usize)>,
    previous: BTreeMap<u16, usize>,
}

impl RowTextLengths {
    fn get(&mut self, screen: &Screen, row: u16) -> usize {
        if let Some((cached_row, count)) = self.current {
            if cached_row == row {
                return count;
            }
        }
        let count = match self.previous.get(&row) {
            Some(&count) => count,
            None => {
                #[cfg(test)]
                positional_work::scanned(false, screen, row);
                // Preserve line_text's wide/spacer, combining and Unicode
                // trim_end semantics; this is a scalar count, not a column.
                screen.line_text(row).chars().count()
            }
        };
        if let Some((old_row, old_count)) = self.current.replace((row, count)) {
            self.previous.insert(old_row, old_count);
        }
        count
    }
}

/// Whether output traversed a position. Cursor progress remains the first,
/// allocation-free proof; only matching spaces need the row-text fallback.
fn traversed(screen: &Screen, row: u16, col: u16, lengths: &mut RowTextLengths) -> bool {
    screen.cursor() > (row, col) || lengths.get(screen, row) > (col as usize).saturating_add(1)
}

fn verdict_now(screen: &Screen, p: &Prediction, lengths: &mut RowTextLengths) -> Option<Verdict> {
    let cell = screen.cell(p.row, p.col)?;
    if cell.ch == p.ch && (p.ch != ' ' || traversed(screen, p.row, p.col, lengths)) {
        Some(Verdict::Confirmed)
    } else if *cell != Cell::BLANK {
        Some(Verdict::Contradicted)
    } else {
        None
    }
}

// Frozen positional helpers remain independent of the memoized callsites.
/// Whether the authoritative output has demonstrably *traversed* `(row, col)`:
/// the cursor sits beyond it, or a glyph was painted strictly to its right on
/// the same row (`line_text` is right-trimmed, so a longer line than
/// `col + 1` chars means a non-blank cell further right). Only a predicted
/// space needs this — every other glyph is its own proof of echo.
#[cfg(test)]
fn legacy_traversed(screen: &Screen, row: u16, col: u16) -> bool {
    screen.cursor() > (row, col) || {
        positional_work::scanned(true, screen, row);
        screen.line_text(row).chars().count() > (col as usize).saturating_add(1)
    }
}

/// The positional verdict for one prediction against the authoritative screen
/// right now, or `None` while it is still undecided (the output has not reached
/// that cell). Shared by every positional retirement path so they cannot drift.
#[cfg(test)]
fn legacy_verdict_now(screen: &Screen, p: &Prediction) -> Option<Verdict> {
    let cell = screen.cell(p.row, p.col)?;
    if cell.ch == p.ch && (p.ch != ' ' || legacy_traversed(screen, p.row, p.col)) {
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

#[cfg(test)]
mod positional_work {
    use super::Screen;
    use std::cell::Cell;
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(super) struct Work {
        pub(super) legacy_rows: usize,
        pub(super) memoized_rows: usize,
        pub(super) legacy_cells: usize,
        pub(super) memoized_cells: usize,
    }
    thread_local! { static WORK: Cell<Work> = const { Cell::new(Work {
        legacy_rows: 0, memoized_rows: 0, legacy_cells: 0, memoized_cells: 0,
    }) }; }
    pub(super) fn scanned(legacy: bool, screen: &Screen, row: u16) {
        let (cols, rows) = screen.dims();
        let cells = if row < rows { cols as usize } else { 0 };
        WORK.with(|work| {
            let mut value = work.get();
            if legacy {
                value.legacy_rows += 1;
                value.legacy_cells += cells;
            } else {
                value.memoized_rows += 1;
                value.memoized_cells += cells;
            }
            work.set(value);
        });
    }
    pub(super) fn capture<T>(f: impl FnOnce() -> T) -> (T, Work) {
        WORK.with(|work| work.set(Work::default()));
        let value = f();
        let work = WORK.with(|work| work.replace(Work::default()));
        (value, work)
    }
}

#[cfg(test)]
#[path = "positional_space_tests.rs"]
mod positional_space_tests;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

// Small typing queues avoid tree/index setup. Larger causal queues pay one
// bounded-size index per active slot, with one tree entry per distinct cause.
const CAUSAL_INDEX_MIN: usize = 256;
const COMPACT_MIN: usize = 64;
const RETAIN_EMPTY: usize = 64;
const NO_NEXT: usize = usize::MAX;

fn causal_index_min() -> usize {
    #[cfg(test)]
    {
        work::index_min()
    }
    #[cfg(not(test))]
    {
        CAUSAL_INDEX_MIN
    }
}

#[derive(Default)]
struct CausalIndex {
    // First/last pending glyph for a cause; duplicate offsets retire in FIFO order.
    by_offset: BTreeMap<u64, (usize, usize)>,
    next: Vec<usize>,
}

impl CausalIndex {
    fn push_slot(&mut self, cause: Option<u64>, at: usize) -> bool {
        #[cfg(test)]
        if work::index_reservation_fails() {
            return false;
        }
        // Geometric growth keeps repeated enqueues amortized linear. Failure
        // discards this optional metadata, never the authoritative pending glyphs.
        if self.next.try_reserve(1).is_err() {
            return false;
        }
        self.next.push(NO_NEXT);
        if let Some(cause) = cause {
            self.link(cause, at);
        }
        true
    }

    fn link(&mut self, cause: u64, at: usize) {
        match self.by_offset.entry(cause) {
            Entry::Occupied(mut entry) => {
                let (_, tail) = entry.get_mut();
                if let Some(next) = self.next.get_mut(*tail) {
                    *next = at;
                }
                *tail = at;
            }
            Entry::Vacant(entry) => {
                entry.insert((at, at));
            }
        }
    }

    /// Every removal is either the global front or a cause's first occurrence,
    /// so it is always the first live glyph of its cause.
    fn unlink_head(&mut self, cause: u64, at: usize) {
        let next = self.next.get(at).copied().unwrap_or(NO_NEXT);
        if let Entry::Occupied(mut entry) = self.by_offset.entry(cause) {
            #[cfg(test)]
            assert_eq!(entry.get().0, at, "only causal heads can be retired");
            if next == NO_NEXT {
                entry.remove();
            } else {
                entry.get_mut().0 = next;
            }
        }
    }
}

/// Pending glyphs stay in insertion order. Retired slots become tombstones;
/// prefixes are skipped and dead suffixes are popped without copying survivors.
/// Half-dead buffers compact in place, charging that work to prior retirements.
#[derive(Default)]
struct Pending {
    slots: Vec<Option<Prediction>>,
    head: usize,
    live: usize,
    tagged: usize,
    causal: Option<CausalIndex>,
}

impl Pending {
    fn iter(&self) -> impl Iterator<Item = &Prediction> {
        self.slots.iter().skip(self.head).filter_map(Option::as_ref)
    }

    fn front(&self) -> Option<&Prediction> {
        self.slots.get(self.head)?.as_ref()
    }

    fn last(&self) -> Option<&Prediction> {
        self.slots.last()?.as_ref()
    }

    fn push(&mut self, prediction: Prediction) {
        let at = self.slots.len();
        self.slots.push(Some(prediction));
        self.live = self.live.saturating_add(1);
        if prediction.in_offset.is_some() {
            self.tagged = self.tagged.saturating_add(1);
        }
        if let Some(index) = &mut self.causal {
            if !index.push_slot(prediction.in_offset, at) {
                self.causal = None;
            }
        }
    }

    fn clear(&mut self) {
        if self.slots.capacity() > RETAIN_EMPTY {
            self.slots = Vec::new();
        } else {
            self.slots.clear();
        }
        self.head = 0;
        self.live = 0;
        self.tagged = 0;
        self.causal = None;
    }

    fn rebuild_index(&mut self) {
        let mut index = self.causal.take().unwrap_or_default();
        if !prepare_causal_links(&mut index.next, self.slots.len()) {
            return; // self.causal remains None: ordered lookup is still exact.
        }
        index.by_offset.clear();
        for (at, slot) in self.slots.iter().enumerate().skip(self.head) {
            #[cfg(test)]
            work::index_slot();
            if let Some(cause) = slot.as_ref().and_then(|p| p.in_offset) {
                index.link(cause, at);
            }
        }
        self.causal = Some(index);
    }

    fn pop_front(&mut self) -> Option<Prediction> {
        self.take_head_at(self.head)
    }

    fn take_cause(&mut self, cause: u64) -> Option<Prediction> {
        // Ordered echoes and repeated offsets normally hit the global front.
        // It is necessarily the first glyph of its cause, so no index is needed.
        if self.front().is_some_and(|p| p.in_offset == Some(cause)) {
            return self.pop_front();
        }
        if self.tagged == 0 {
            return None;
        }
        if self.causal.is_none() && self.live >= causal_index_min() {
            self.rebuild_index();
        }
        let at = if let Some(index) = &self.causal {
            index.by_offset.get(&cause).map(|&(first, _)| first)
        } else {
            self.slots
                .iter()
                .enumerate()
                .skip(self.head)
                .find_map(|(at, slot)| {
                    #[cfg(test)]
                    work::lookup_slot();
                    slot.as_ref()
                        .filter(|p| p.in_offset == Some(cause))
                        .map(|_| at)
                })
        }?;
        self.take_head_at(at)
    }

    fn take_head_at(&mut self, at: usize) -> Option<Prediction> {
        let prediction = self.slots.get_mut(at)?.take()?;
        self.live = self.live.saturating_sub(1);
        if let Some(cause) = prediction.in_offset {
            self.tagged = self.tagged.saturating_sub(1);
            if let Some(index) = &mut self.causal {
                index.unlink_head(cause, at);
            }
        }
        if self.live == 0 {
            self.clear();
            return Some(prediction);
        }
        // Physically remove trailing holes. A new append cannot make us scan the
        // same dead suffix again, and last() always finds the last live anchor.
        while self.slots.last().is_some_and(Option::is_none) {
            let _ = self.slots.pop();
            #[cfg(test)]
            work::trimmed_slot();
        }
        if let Some(index) = &mut self.causal {
            index.next.truncate(self.slots.len());
        }
        while self.slots.get(self.head).is_some_and(Option::is_none) {
            self.head = self.head.saturating_add(1);
            #[cfg(test)]
            work::skipped_slot();
        }
        let dead = self.slots.len().saturating_sub(self.live);
        if self.slots.len() >= COMPACT_MIN && dead >= self.live {
            #[cfg(test)]
            work::compacted_slots(self.slots.len());
            self.slots.retain(Option::is_some);
            self.head = 0;
            if self.causal.is_some() {
                self.rebuild_index();
            }
        }
        shrink_pending(&mut self.slots);
        if let Some(index) = &mut self.causal {
            shrink_pending(&mut index.next);
        }
        Some(prediction)
    }
}

/// Reserve optional per-slot links before filling them. A failed reservation
/// leaves prediction storage untouched and falls back to ordered causal lookup.
fn prepare_causal_links(links: &mut Vec<usize>, len: usize) -> bool {
    #[cfg(test)]
    if work::index_reservation_fails() {
        return false;
    }
    links.clear();
    if links.try_reserve_exact(len).is_err() {
        return false;
    }
    for _ in 0..len {
        links.push(NO_NEXT);
    }
    true
}

fn shrink_pending<T>(buffer: &mut Vec<T>) {
    if buffer.capacity() > RETAIN_EMPTY && buffer.len() <= buffer.capacity() / 4 {
        buffer.shrink_to(buffer.len().saturating_mul(2).max(16));
    }
}

#[cfg(test)]
mod work {
    use std::cell::Cell;
    thread_local! {
        static COUNTS: Cell<[usize; 5]> = const { Cell::new([0; 5]) };
        static FAIL_INDEX_RESERVATION: Cell<bool> = const { Cell::new(false) };
        static ENABLED: Cell<bool> = const { Cell::new(true) };
        static INDEX_MIN: Cell<usize> = const { Cell::new(super::CAUSAL_INDEX_MIN) };
    }
    fn add(kind: usize, n: usize) {
        if !ENABLED.with(Cell::get) {
            return;
        }
        COUNTS.with(|counts| {
            let mut value = counts.get();
            value[kind] = value[kind].saturating_add(n);
            counts.set(value);
        });
    }
    pub(super) fn index_slot() {
        add(0, 1);
    }
    pub(super) fn lookup_slot() {
        add(1, 1);
    }
    pub(super) fn trimmed_slot() {
        add(2, 1);
    }
    pub(super) fn skipped_slot() {
        add(3, 1);
    }
    pub(super) fn compacted_slots(n: usize) {
        add(4, n);
    }
    pub(super) fn disable() {
        ENABLED.with(|enabled| enabled.set(false));
    }
    pub(super) fn index_min() -> usize {
        INDEX_MIN.with(Cell::get)
    }
    pub(super) fn set_index_min(min: usize) {
        INDEX_MIN.with(|value| value.set(min));
    }
    pub(super) fn index_reservation_fails() -> bool {
        FAIL_INDEX_RESERVATION.with(Cell::get)
    }
    pub(super) fn fail_index_reservation(fail: bool) {
        FAIL_INDEX_RESERVATION.with(|value| value.set(fail));
    }
    pub(super) fn take() -> [usize; 5] {
        COUNTS.with(|counts| counts.replace([0; 5]))
    }
}

/// A client-side speculative-echo overlay over the authoritative screen.
pub struct Predictor {
    base: Folder,
    preds: Pending,
    in_watermark: Option<u64>,
}

impl Predictor {
    /// A predictor over a blank authoritative screen of the given size.
    pub fn new(cols: u16, rows: u16) -> Predictor {
        Predictor {
            base: Folder::new(cols, rows),
            preds: Pending::default(),
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
        if !all_ascii_printable(bytes) {
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
        let mut rest = bytes;
        while let &[b, ref tail @ ..] = rest {
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
            rest = tail;
        }
        true
    }

    /// Fold one authoritative output (or resize) record into the base screen.
    pub fn apply_output(&mut self, record: &Record) {
        self.base.apply(record);
    }

    /// The highest authoritative out-offset retired so far.
    #[must_use]
    pub const fn in_watermark(&self) -> Option<u64> {
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
        let next_wm = match self.in_watermark {
            Some(w) => {
                if !watermark_advances(w, watermark) {
                    return Vec::new(); // out-of-order watermark: reject, do not advance
                }
                if w < watermark {
                    watermark
                } else {
                    w
                }
            }
            None => watermark,
        };
        self.in_watermark = Some(next_wm);
        self.base.apply(record);

        let mut verdicts = Vec::new();
        let mut lengths = RowTextLengths::default();
        while let Some(prediction) = self.preds.front() {
            let client_seq = prediction.client_seq;
            match verdict_now(self.base.screen(), prediction, &mut lengths) {
                Some(Verdict::Confirmed) => {
                    verdicts.push((client_seq, Verdict::Confirmed));
                    let _ = self.preds.pop_front();
                }
                Some(_) => {
                    verdicts.push((client_seq, Verdict::Contradicted));
                    let _ = self.preds.pop_front();
                    for tail in self.preds.iter() {
                        verdicts.push((tail.client_seq, Verdict::Lost));
                    }
                    self.preds.clear();
                    break;
                }
                None => break,
            }
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
        out_offset: u64,
        in_offset_for_out: Option<u64>,
        record: &Record,
    ) -> Vec<(u64, Verdict)> {
        self.base.apply(record);
        let (Some(in_off), Record::Out(bytes)) = (in_offset_for_out, record) else {
            return Vec::new();
        };
        let Some(p) = self.preds.take_cause(in_off) else {
            return Vec::new();
        };
        if let Some(pred_in_off) = p.in_offset {
            let cur_wm = self.in_watermark.unwrap_or(out_offset);
            self.in_watermark = Some(echo_admit_causal_watermark(
                in_off,
                pred_in_off,
                cur_wm,
                out_offset,
            ));
        }
        // A predicted glyph is always ASCII-printable (see `enqueue`), so it is
        // among the Out's printable bytes iff that byte occurs in the Out at all.
        let verdict = if slice_contains_byte(bytes, p.ch as u8) {
            Verdict::Confirmed
        } else {
            Verdict::Contradicted
        };
        vec![(p.client_seq, verdict)]
    }

    /// The authoritative screen, with no predictions overlaid.
    #[must_use]
    pub const fn authoritative(&self) -> &Screen {
        self.base.screen()
    }

    /// What the user sees: the authoritative screen with the still-unconfirmed
    /// predictions painted on top (faint).
    pub fn view(&self) -> Screen {
        let mut screen = self.base.screen().clone();
        for p in self.preds.iter() {
            screen.set_cell(
                p.row,
                p.col,
                Cell {
                    ch: p.ch,
                    fg: Color::Default,
                    bg: Color::Default,
                    fg_rgb: None,
                    bg_rgb: None,
                    attrs: attr::FAINT,
                    ..Cell::BLANK
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
        let mut verdicts = Vec::new();
        let screen = self.base.screen();
        let mut lengths = RowTextLengths::default();
        for p in self.preds.iter() {
            let verdict = verdict_now(screen, p, &mut lengths).unwrap_or(Verdict::Lost);
            verdicts.push((p.client_seq, verdict));
        }
        self.preds.clear();
        verdicts
    }
}

#[cfg(test)]
mod pending_tests {
    use super::*;

    // The pre-optimization implementation: dense Vec, suffix copies, and linear
    // causal search. Shared scalar screen/verdict kernels are intentionally unchanged.
    pub struct LegacyPredictor {
        base: Folder,
        preds: Vec<Prediction>,
        in_watermark: Option<u64>,
    }

    impl LegacyPredictor {
        /// A predictor over a blank authoritative screen of the given size.
        pub fn new(cols: u16, rows: u16) -> LegacyPredictor {
            LegacyPredictor {
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
            if !all_ascii_printable(bytes) {
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
            let mut rest = bytes;
            while let &[b, ref tail @ ..] = rest {
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
                rest = tail;
            }
            true
        }

        /// Fold one authoritative output (or resize) record into the base screen.
        pub fn apply_output(&mut self, record: &Record) {
            self.base.apply(record);
        }

        /// The highest authoritative out-offset retired so far.
        #[must_use]
        pub const fn in_watermark(&self) -> Option<u64> {
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
            let next_wm = match self.in_watermark {
                Some(w) => {
                    if !watermark_advances(w, watermark) {
                        return Vec::new(); // out-of-order watermark: reject, do not advance
                    }
                    if w < watermark {
                        watermark
                    } else {
                        w
                    }
                }
                None => watermark,
            };
            self.in_watermark = Some(next_wm);
            self.base.apply(record);

            let mut verdicts = Vec::new();
            let mut confirmed = 0usize;
            let mut contradicted = false;
            for p in &self.preds {
                match legacy_verdict_now(self.base.screen(), p) {
                    Some(Verdict::Confirmed) => {
                        verdicts.push((p.client_seq, Verdict::Confirmed));
                        confirmed = confirmed.saturating_add(1);
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
                for p in self.preds.get(confirmed.saturating_add(1)..).unwrap_or(&[]) {
                    verdicts.push((p.client_seq, Verdict::Lost));
                }
                self.preds.clear();
            } else if confirmed >= self.preds.len() {
                self.preds.clear();
            } else if confirmed > 0 {
                let mut kept = Vec::new();
                if let Some(tail) = self.preds.get(confirmed..) {
                    kept.extend_from_slice(tail);
                }
                self.preds = kept;
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
            out_offset: u64,
            in_offset_for_out: Option<u64>,
            record: &Record,
        ) -> Vec<(u64, Verdict)> {
            self.base.apply(record);
            let (Some(in_off), Record::Out(bytes)) = (in_offset_for_out, record) else {
                return Vec::new();
            };
            let mut found_pos = None;
            for (idx, p) in self.preds.iter().enumerate() {
                if p.in_offset == Some(in_off) {
                    found_pos = Some(idx);
                    break;
                }
            }
            let Some(pos) = found_pos else {
                return Vec::new();
            };
            let Some(p) = self.preds.get(pos).copied() else {
                return Vec::new();
            };
            let mut kept = Vec::new();
            if let Some(head) = self.preds.get(..pos) {
                kept.extend_from_slice(head);
            }
            if let Some(tail) = self.preds.get(pos.saturating_add(1)..) {
                kept.extend_from_slice(tail);
            }
            self.preds = kept;
            if let Some(pred_in_off) = p.in_offset {
                let cur_wm = self.in_watermark.unwrap_or(out_offset);
                self.in_watermark = Some(echo_admit_causal_watermark(
                    in_off,
                    pred_in_off,
                    cur_wm,
                    out_offset,
                ));
            }
            // A predicted glyph is always ASCII-printable (see `enqueue`), so it is
            // among the Out's printable bytes iff that byte occurs in the Out at all.
            let verdict = if slice_contains_byte(bytes, p.ch as u8) {
                Verdict::Confirmed
            } else {
                Verdict::Contradicted
            };
            vec![(p.client_seq, verdict)]
        }

        /// The authoritative screen, with no predictions overlaid.
        #[must_use]
        pub const fn authoritative(&self) -> &Screen {
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
                        fg_rgb: None,
                        bg_rgb: None,
                        attrs: attr::FAINT,
                        ..Cell::BLANK
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
            let mut verdicts = Vec::new();
            let screen = self.base.screen();
            for p in &self.preds {
                let verdict = legacy_verdict_now(screen, p).unwrap_or(Verdict::Lost);
                verdicts.push((p.client_seq, verdict));
            }
            self.preds.clear();
            verdicts
        }
    }

    fn check_pending(pending: &Pending) {
        let live: Vec<_> = pending.slots.iter().flatten().copied().collect();
        assert_eq!(pending.iter().copied().collect::<Vec<_>>(), live);
        assert_eq!(pending.live, live.len());
        assert_eq!(
            pending.tagged,
            live.iter().filter(|p| p.in_offset.is_some()).count()
        );
        assert_eq!(pending.front(), live.first());
        assert_eq!(pending.last(), live.last());
        if !live.is_empty() {
            assert!(pending.slots.last().unwrap().is_some());
            assert_eq!(
                pending.slots.iter().position(Option::is_some),
                Some(pending.head)
            );
            assert!(pending.slots.len() < COMPACT_MIN || pending.slots.len() < 2 * pending.live);
        } else {
            assert_eq!(pending.head, 0);
            assert!(pending.slots.is_empty());
            assert!(pending.slots.capacity() <= RETAIN_EMPTY);
            assert!(pending.causal.is_none());
        }
        if let Some(index) = &pending.causal {
            assert_eq!(index.next.len(), pending.slots.len());
            let mut expected: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
            for (at, p) in pending.slots.iter().enumerate() {
                if let Some(cause) = p.as_ref().and_then(|p| p.in_offset) {
                    expected.entry(cause).or_default().push(at);
                }
            }
            assert_eq!(index.by_offset.len(), expected.len());
            for (cause, positions) in expected {
                let &(first, last) = index.by_offset.get(&cause).unwrap();
                assert_eq!(Some(&first), positions.first());
                assert_eq!(Some(&last), positions.last());
                let mut actual = Vec::new();
                let mut at = first;
                while at != NO_NEXT {
                    assert!(actual.len() < pending.live);
                    actual.push(at);
                    at = index.next[at];
                }
                assert_eq!(actual, positions);
            }
        }
    }

    fn compare(actual: &Predictor, reference: &LegacyPredictor) {
        assert_eq!(
            actual.preds.iter().copied().collect::<Vec<_>>(),
            reference.preds
        );
        assert_eq!(actual.in_watermark(), reference.in_watermark());
        assert_eq!(actual.authoritative(), reference.authoritative());
        assert_eq!(actual.view(), reference.view());
        check_pending(&actual.preds);
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn cause(&mut self) -> u64 {
            match self.next() % 32 {
                0 => u64::MAX,
                n => n % 8,
            }
        }
        fn record(&mut self) -> Record {
            match self.next() % 12 {
                0 => Record::Resize {
                    cols: 1 + (self.next() % 16) as u16,
                    rows: 1 + (self.next() % 8) as u16,
                },
                1 => Record::In {
                    bytes: b"ignored".to_vec(),
                    client_id: 3,
                    client_seq: self.next(),
                },
                2 => Record::Exit { code: 7 },
                n => {
                    let bytes: &[u8] = match n {
                        3 => b"",
                        4 => b" ",
                        5 => b"abc",
                        6 => b"xyz ",
                        7 => b"\r\n",
                        8 => b"\x1b[2J\x1b[H",
                        9 => b"\x1b[31mQ\x1b[0m",
                        10 => b"\x1b[?1049hALT",
                        _ => b"\x1b[?1049l",
                    };
                    Record::Out(bytes.to_vec())
                }
            }
        }
    }

    #[test]
    fn pending_queue_matches_the_original_vec_across_mixed_retirement_paths() {
        for seed in 1..=100u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            let mut actual = Predictor::new(12, 4);
            let mut reference = LegacyPredictor::new(12, 4);
            for step in 0..400u64 {
                match rng.next() % 12 {
                    n @ 0..=5 => {
                        let bytes = match rng.next() % 7 {
                            0 => Vec::new(),
                            1 => b"\r\n".to_vec(),
                            2 => b"\x1b[A".to_vec(),
                            3 => vec![b'a'; 80],
                            4 => b" ".to_vec(),
                            5 => b"abc xyz".to_vec(),
                            _ => b"q".to_vec(),
                        };
                        let client = rng.next() % 8;
                        if n % 2 == 0 {
                            assert_eq!(
                                actual.predict(client, &bytes),
                                reference.predict(client, &bytes)
                            );
                        } else {
                            let cause = rng.cause();
                            assert_eq!(
                                actual.predict_at(client, cause, &bytes),
                                reference.predict_at(client, cause, &bytes)
                            );
                        }
                    }
                    6 | 7 => {
                        let cause = (rng.next() % 5 != 0).then(|| rng.cause());
                        let offset = rng.next() % 200;
                        let record = rng.record();
                        assert_eq!(
                            actual.apply_output_caused(offset, cause, &record),
                            reference.apply_output_caused(offset, cause, &record)
                        );
                    }
                    8 | 9 => {
                        let watermark = if step % 2 == 0 { step } else { rng.next() % 20 };
                        let record = rng.record();
                        assert_eq!(
                            actual.apply_output_at(watermark, &record),
                            reference.apply_output_at(watermark, &record)
                        );
                    }
                    10 => {
                        let record = rng.record();
                        actual.apply_output(&record);
                        reference.apply_output(&record);
                    }
                    _ => assert_eq!(actual.reconcile(), reference.reconcile()),
                }
                compare(&actual, &reference);
            }
            assert_eq!(actual.reconcile(), reference.reconcile());
            compare(&actual, &reference);
        }
    }

    #[test]
    fn duplicate_causes_and_last_live_anchor_survive_compaction_and_tail_reuse() {
        let mut actual = Predictor::new(40, 8);
        let mut reference = LegacyPredictor::new(40, 8);
        for i in 0..256u64 {
            let cause = if i % 4 == 0 { u64::MAX } else { i };
            actual.predict_at(i, cause, b"xy");
            reference.predict_at(i, cause, b"xy");
        }
        let record = Record::Out(b"x".to_vec());
        for cause in (1..256u64).rev().filter(|i| i % 4 != 0) {
            for _ in 0..2 {
                assert_eq!(
                    actual.apply_output_caused(5, Some(cause), &record),
                    reference.apply_output_caused(5, Some(cause), &record)
                );
            }
        }
        compare(&actual, &reference);
        assert!(actual.preds.causal.is_some());
        for _ in 0..1000 {
            actual.predict_at(900, 900, b"z");
            reference.predict_at(900, 900, b"z");
            assert_eq!(
                actual.apply_output_caused(6, Some(900), &record),
                reference.apply_output_caused(6, Some(900), &record)
            );
            compare(&actual, &reference);
        }
        for _ in 0..128 {
            assert_eq!(
                actual.apply_output_caused(u64::MAX, Some(u64::MAX), &record),
                reference.apply_output_caused(u64::MAX, Some(u64::MAX), &record)
            );
        }
        compare(&actual, &reference);
        assert_eq!(actual.in_watermark(), Some(u64::MAX));
        assert_eq!(actual.reconcile(), reference.reconcile());
        assert!(actual.preds.causal.is_none());
        assert!(actual.preds.slots.capacity() <= RETAIN_EMPTY);
    }

    fn prediction(i: usize, tagged: bool) -> Prediction {
        Prediction {
            client_seq: i as u64,
            row: 0,
            col: 0,
            ch: 'x',
            in_offset: tagged.then_some(i as u64),
        }
    }

    #[test]
    fn large_reverse_and_fifo_retirements_have_linear_slot_work_and_release_memory() {
        const N: usize = 16_384;
        for reverse in [false, true] {
            let mut pending = Pending::default();
            for i in 0..N {
                pending.push(prediction(i, true));
            }
            let _ = work::take();
            for i in 0..N {
                let cause = if reverse { N - 1 - i } else { i };
                assert_eq!(
                    pending.take_cause(cause as u64).unwrap().client_seq,
                    cause as u64
                );
                if !reverse {
                    assert!(pending.causal.is_none(), "FIFO retirement needs no index");
                }
            }
            let [indexed, scanned, trimmed, skipped, compacted] = work::take();
            assert!(indexed <= 3 * N, "indexed {indexed}");
            assert_eq!(scanned, 0);
            assert!(trimmed <= N);
            assert!(skipped <= N);
            assert!(compacted <= 2 * N);
            check_pending(&pending);
        }
        let mut pending = Pending::default();
        for i in 0..N {
            pending.push(prediction(i, false));
        }
        let _ = work::take();
        for _ in 0..N {
            assert!(pending.take_cause(0).is_none());
        }
        assert_eq!(work::take(), [0; 5]);
        assert!(
            pending.causal.is_none(),
            "untagged queues never allocate an index"
        );
        pending.clear();
        check_pending(&pending);
    }

    #[test]
    fn mixed_queues_do_not_rebuild_an_empty_causal_index_on_each_new_tag() {
        let mut pending = Pending::default();
        for i in 0..4096 {
            pending.push(prediction(i, false));
        }
        let _ = work::take();
        for i in 0..4096 {
            pending.push(prediction(i, true));
            assert_eq!(pending.take_cause(i as u64).unwrap().client_seq, i as u64);
        }
        let [indexed, scanned, trimmed, skipped, compacted] = work::take();
        assert_eq!(indexed, 4097);
        assert_eq!(scanned, 0);
        assert_eq!(trimmed, 4096);
        assert_eq!(skipped, 0);
        assert_eq!(compacted, 0);
        check_pending(&pending);
    }

    #[test]
    fn failed_optional_index_reservation_keeps_every_prediction_and_exact_retirement() {
        assert!(!prepare_causal_links(&mut Vec::new(), usize::MAX));
        struct FailReservation;
        impl Drop for FailReservation {
            fn drop(&mut self) {
                work::fail_index_reservation(false);
            }
        }
        let mut actual = Predictor::new(40, 8);
        let mut reference = LegacyPredictor::new(40, 8);
        for i in 0..256u64 {
            actual.predict_at(i, i % 8, b"xy");
            reference.predict_at(i, i % 8, b"xy");
        }
        let record = Record::Out(b"x".to_vec());
        work::fail_index_reservation(true);
        let guard = FailReservation;
        for cause in (0..8).rev() {
            assert_eq!(
                actual.apply_output_caused(3, Some(cause), &record),
                reference.apply_output_caused(3, Some(cause), &record)
            );
            assert!(actual.preds.causal.is_none());
            compare(&actual, &reference);
        }
        drop(guard);
        // Setup may succeed on a later call without changing the remaining order.
        assert_eq!(
            actual.apply_output_caused(4, Some(7), &record),
            reference.apply_output_caused(4, Some(7), &record)
        );
        assert!(actual.preds.causal.is_some());
        work::fail_index_reservation(true);
        let guard = FailReservation;
        assert_eq!(
            actual.predict_at(900, 900, b"tail"),
            reference.predict_at(900, 900, b"tail")
        );
        assert!(
            actual.preds.causal.is_none(),
            "append growth can also discard only the cache"
        );
        assert_eq!(
            actual.apply_output_caused(5, Some(900), &record),
            reference.apply_output_caused(5, Some(900), &record)
        );
        compare(&actual, &reference);
        drop(guard);
        assert_eq!(actual.reconcile(), reference.reconcile());
        compare(&actual, &reference);
    }

    fn legacy_retire(queue: &mut Vec<Prediction>, cause: u64) -> Option<Prediction> {
        let pos = queue.iter().position(|p| p.in_offset == Some(cause))?;
        let result = queue[pos];
        let mut kept = Vec::new();
        kept.extend_from_slice(&queue[..pos]);
        kept.extend_from_slice(&queue[pos + 1..]);
        *queue = kept;
        Some(result)
    }

    #[test]
    #[ignore = "manual prediction-retirement CPU and metadata comparison"]
    fn pending_retirement_benchmark() {
        use std::hint::black_box;
        use std::time::Instant;
        work::disable();
        for threshold in [64usize, 128, 256] {
            work::set_index_min(threshold);
            for n in [1usize, 8, 32, 64, 128, 256, 512, 4096, 16_384] {
                for shape in ["fifo", "reverse", "duplicate", "mixed"] {
                    let values: Vec<_> = (0..n)
                        .map(|i| {
                            let mut p = prediction(i, true);
                            if shape == "duplicate" {
                                p.in_offset = Some(7);
                            }
                            if shape == "mixed" && i % 4 == 3 {
                                p.in_offset = None;
                            }
                            p
                        })
                        .collect();
                    let mut causes: Vec<_> = values.iter().filter_map(|p| p.in_offset).collect();
                    if shape == "reverse" || shape == "mixed" {
                        causes.reverse();
                    }
                    let batches = if n <= 512 { 64 } else { 1 };
                    let mut times = [0u128; 3];
                    let mut old_times = [0u128; 3];
                    for run in 0..3 {
                        let mut pending_queues: Vec<_> = (0..batches)
                            .map(|_| {
                                let mut pending = Pending::default();
                                for &p in &values {
                                    pending.push(p);
                                }
                                pending
                            })
                            .collect();
                        let mut old_queues = vec![values.clone(); batches];
                        let mut timed_pending = || {
                            let start = Instant::now();
                            for pending in &mut pending_queues {
                                for &cause in &causes {
                                    black_box(pending.take_cause(black_box(cause)).unwrap());
                                }
                            }
                            times[run] = start.elapsed().as_nanos() / batches as u128;
                        };
                        let mut timed_old = || {
                            let start = Instant::now();
                            for old in &mut old_queues {
                                for &cause in &causes {
                                    black_box(
                                        legacy_retire(black_box(old), black_box(cause)).unwrap(),
                                    );
                                }
                            }
                            old_times[run] = start.elapsed().as_nanos() / batches as u128;
                        };
                        if run % 2 == 0 {
                            timed_pending();
                            timed_old();
                        } else {
                            timed_old();
                            timed_pending();
                        }
                        for (pending, old) in pending_queues.iter().zip(&old_queues) {
                            assert_eq!(pending.iter().copied().collect::<Vec<_>>(), *old);
                        }
                    }
                    times.sort_unstable();
                    old_times.sort_unstable();
                    let mut pending = Pending::default();
                    for &p in &values {
                        pending.push(p);
                    }
                    // Report the induced indexed-state cost, even when the timed FIFO
                    // front fast path never needs an index. Tree allocator overhead is
                    // deliberately not estimated as payload bytes.
                    let _ = pending.take_cause(u64::MAX);
                    let slot_bytes =
                        pending.slots.capacity() * std::mem::size_of::<Option<Prediction>>();
                    let (next_bytes, keys, tree_payload) =
                        pending.causal.as_ref().map_or((0, 0, 0), |index| {
                            (
                                index.next.capacity() * std::mem::size_of::<usize>(),
                                index.by_offset.len(),
                                index.by_offset.len()
                                    * std::mem::size_of::<(u64, (usize, usize))>(),
                            )
                        });
                    println!("PREDICTION threshold={threshold} shape={shape} n={n} pending_ns={} old_ns={} speedup={:.2} slot_bytes={slot_bytes} indexed_next_bytes={next_bytes} indexed_cause_keys={keys} tree_payload_bytes={tree_payload} old_prediction_payload_bytes={} tree_allocator_overhead=unmeasured", times[1], old_times[1], old_times[1] as f64 / times[1].max(1) as f64, n * std::mem::size_of::<Prediction>());
                }
            }
        }
        work::set_index_min(CAUSAL_INDEX_MIN);
    }
}
