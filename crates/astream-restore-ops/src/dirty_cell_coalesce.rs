// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Row-major dirty-span coalescer bounding incremental crash-restore flush IOPS
//! (`Astream.Restore.TlaDirtyCellCoalesce`).

#[cfg(clean_islands)]
#[path = "dirty_cell_coalesce_island.rs"]
mod dirty_cell_coalesce_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn dirty_spans_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn dirty_flush_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use dirty_cell_coalesce_island::{dirty_flush_seq_advance, dirty_spans_clamp};

/// Maximum disjoint dirty spans tracked before coalescing into a full-screen write.
pub const MAX_DIRTY_SPANS: u64 = 64;

contract_fn! {
    /// Verified span-budget check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `dirty_budget_within_isl`.
    #[must_use]
    pub const fn dirty_budget_within(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Half-open linear cell interval `[start_cell, end_cell)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DirtyCellSpan {
    pub start_cell: u64,
    pub end_cell: u64,
}

/// Incremental dirty-cell tracker merging adjacent/overlapping writes.
#[derive(Debug, Clone, Default)]
pub struct DirtySpanCoalescer {
    max_spans: u64,
    flush_seq: u64,
    full_dirty: bool,
    spans: Vec<DirtyCellSpan>,
}

impl DirtySpanCoalescer {
    #[must_use]
    pub const fn new(max_spans: u64) -> Self {
        let c = dirty_spans_clamp(max_spans, MAX_DIRTY_SPANS);
        Self {
            max_spans: if c == 0 { 1 } else { c },
            flush_seq: 0,
            full_dirty: false,
            spans: Vec::new(),
        }
    }

    pub fn mark_dirty(&mut self, start_cell: u64, end_cell: u64) {
        if end_cell <= start_cell || self.full_dirty {
            return;
        }
        let incoming = DirtyCellSpan {
            start_cell,
            end_cell,
        };
        let old_spans = core::mem::take(&mut self.spans);
        let mut sorted: Vec<DirtyCellSpan> = Vec::new();
        let mut inserted = false;
        for existing in old_spans {
            if !inserted && incoming.start_cell <= existing.start_cell {
                sorted.push(incoming);
                inserted = true;
            }
            sorted.push(existing);
        }
        if !inserted {
            sorted.push(incoming);
        }

        let mut merged: Vec<DirtyCellSpan> = Vec::new();
        for s in sorted {
            if let Some(last) = merged.last_mut() {
                if s.start_cell <= last.end_cell {
                    if s.end_cell > last.end_cell {
                        last.end_cell = s.end_cell;
                    }
                    continue;
                }
            }
            merged.push(s);
        }
        self.spans = merged;
        if !dirty_budget_within(self.max_spans, self.spans.len() as u64) {
            self.full_dirty = true;
            self.spans.clear();
        }
    }

    /// Drains coalesced spans (or `None` when escalated to a single sequential full-grid write).
    pub fn drain_flush_batch(&mut self) -> (u64, Option<Vec<DirtyCellSpan>>) {
        self.flush_seq = dirty_flush_seq_advance(self.flush_seq, self.flush_seq.saturating_add(1));
        if self.full_dirty {
            self.full_dirty = false;
            (self.flush_seq, None)
        } else {
            let out = core::mem::take(&mut self.spans);
            (self.flush_seq, Some(out))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalescer_merges_overlapping_cell_ranges_and_escalates_past_span_cap() {
        let mut c = DirtySpanCoalescer::new(2);
        c.mark_dirty(10, 20);
        c.mark_dirty(18, 30);
        c.mark_dirty(50, 60);
        let (seq, batch) = c.drain_flush_batch();
        assert_eq!(seq, 1);
        assert_eq!(
            batch.unwrap(),
            vec![
                DirtyCellSpan {
                    start_cell: 10,
                    end_cell: 30
                },
                DirtyCellSpan {
                    start_cell: 50,
                    end_cell: 60
                },
            ]
        );
        // 3 disjoint spans exceed cap=2 -> escalates to None (full write)!
        c.mark_dirty(0, 2);
        c.mark_dirty(10, 12);
        c.mark_dirty(20, 22);
        assert_eq!(c.drain_flush_batch(), (2, None));
    }
}
