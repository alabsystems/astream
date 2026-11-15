//! The perception layer: read a folded screen as **text** and **structured
//! query**, reconstructed from the recorded `Out` log at **any offset**.
//!
//! These are the cheap modalities an orchestrator agent reasons over (the
//! image/animation modalities live in [`crate::screen`] / [`render`](crate::render)).
//! Everything here is a pure projection of [`frame`] — the screen folded through
//! a chosen offset — so "what did this terminal look like at offset K, and where
//! is the word `error`?" is a query, not a screenshot to OCR.

use crate::record::Record;
use crate::screen::{fold, Screen};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "perceive_island.rs"]
mod perceive_island;
#[cfg(not(clean_islands))]
pub use crate::twins::perceive_clamp_take_count;
#[cfg(clean_islands)]
pub use perceive_island::perceive_clamp_take_count;

contract_fn! {
    /// Kernel-certified bounds check that a screen row index `row` lies strictly
    /// within the grid height `rows` (`row < rows`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `perceive_row_in_bounds_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn perceive_row_in_bounds(row: u16, rows: u16) -> bool
    clauses [ensures result == (row < rows)]
    {
        row < rows
    }
}

/// The screen as of offset `k`: fold of `records[0..=k]` (later records are not
/// applied). This is what makes every read below time-addressable.
pub fn frame(cols: u16, rows: u16, records: &[Record], k: usize) -> Screen {
    let req = k.saturating_add(1);
    let take = if req <= records.len() {
        req
    } else {
        records.len()
    };
    fold(cols, rows, records.get(..take).unwrap_or(&[]))
}

/// The screen as lines of text (trailing blanks trimmed per row).
pub fn text(screen: &Screen) -> Vec<String> {
    let (_, rows) = screen.dims();
    let mut out = Vec::with_capacity(rows as usize);
    let mut r = 0u16;
    while perceive_row_in_bounds(r, rows) {
        out.push(screen.line_text(r));
        r = r.saturating_add(1);
    }
    out
}

/// A maximal run of consecutive non-empty rows — a text region. (Prompt-aware
/// command/output blocks need shell heuristics; this is the deterministic,
/// program-agnostic base: contiguous non-empty regions.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// First row of the region (0-based).
    pub top: u16,
    /// Last row of the region (0-based, inclusive).
    pub bottom: u16,
    /// The region's lines.
    pub lines: Vec<String>,
}

/// Partition the screen into [`Block`]s — the contiguous non-empty regions.
pub fn blocks(screen: &Screen) -> Vec<Block> {
    let lines = text(screen);
    let mut out = Vec::new();
    let mut start: Option<u16> = None;
    for (i, line) in lines.iter().enumerate() {
        let r = i as u16;
        if line.is_empty() {
            if let Some(s) = start.take() {
                out.push(Block {
                    top: s,
                    bottom: r.saturating_sub(1),
                    lines: lines.get(s as usize..r as usize).unwrap_or(&[]).to_vec(),
                });
            }
        } else if start.is_none() {
            start = Some(r);
        }
    }
    if let Some(s) = start {
        out.push(Block {
            top: s,
            bottom: (lines.len() as u16).saturating_sub(1),
            lines: lines.get(s as usize..).unwrap_or(&[]).to_vec(),
        });
    }
    out
}

/// One search hit: the cell where a match begins and its length in characters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hit {
    /// Row of the match (0-based).
    pub row: u16,
    /// Starting character column of the match (0-based).
    pub col: u16,
    /// Match length in characters.
    pub len: u16,
}

/// The **non-overlapping** occurrences of `needle` in the screen text, scanned
/// left to right per row, as character-column [`Hit`]s — the scan resumes after
/// each match, so `aa` in `aaa` is one hit at column 0, not two. Empty needle
/// finds nothing.
pub fn search(screen: &Screen, needle: &str) -> Vec<Hit> {
    if needle.is_empty() {
        return Vec::new();
    }
    let len = needle.chars().count() as u16;
    let mut out = Vec::new();
    for (r, line) in text(screen).iter().enumerate() {
        let mut from = 0usize; // byte offset into `line`
        let mut col = 0u16; // character column of `from`
        while let Some(rem) = line.get(from..) {
            let Some(pos) = rem.find(needle) else {
                break;
            };
            // Count only the characters skipped since the last hit, so a row full
            // of matches is scanned once, not once per match.
            let prefix_chars = match line.get(from..from.saturating_add(pos)) {
                Some(s) => s.chars().count() as u16,
                None => 0,
            };
            col = col.saturating_add(prefix_chars);
            out.push(Hit {
                row: r as u16,
                col,
                len,
            });
            col = col.saturating_add(len);
            from = from.saturating_add(pos).saturating_add(needle.len());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn out(s: &[u8]) -> Record {
        Record::Out(s.to_vec())
    }

    #[test]
    fn text_and_search_read_the_folded_screen() {
        let recs = vec![out(b"\x1b[2Jhello world\r\nerror here\r\n")];
        let s = frame(40, 4, &recs, 0);
        assert_eq!(text(&s)[0], "hello world");
        assert_eq!(text(&s)[1], "error here");
        let hits = search(&s, "error");
        assert_eq!(
            hits,
            vec![Hit {
                row: 1,
                col: 0,
                len: 5
            }]
        );
        assert!(search(&s, "absent").is_empty());
        // 'o' appears in "hello world" at cols 4 and 7.
        let os = search(&s, "o");
        assert_eq!(os.iter().filter(|h| h.row == 0).count(), 2);
    }

    #[test]
    fn blocks_are_the_contiguous_non_empty_regions() {
        // rows: "a","b","", "c"  -> two blocks: [0..1] and [3..3]
        let recs = vec![out(b"a\r\nb\r\n\r\nc")];
        let s = frame(10, 5, &recs, 0);
        let bs = blocks(&s);
        assert_eq!(bs.len(), 2);
        assert_eq!((bs[0].top, bs[0].bottom), (0, 1));
        assert_eq!(bs[0].lines, vec!["a".to_string(), "b".to_string()]);
        assert_eq!((bs[1].top, bs[1].bottom), (3, 3));
    }
}
