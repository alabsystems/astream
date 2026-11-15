// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fine-grained per-byte PTY write->echo causal attribution across overlapping in-flight
//! inputs (`docs/ROADMAP.md` line 179, `Astream.Term.TlaOverlapEcho`).
//!
//! When multiple un-echoed PTY writes overlap in flight (`drive_input` / `predict_at` at
//! `in_offset = 10`, `11`, `12` before the kernel `termios` line discipline echoes any of
//! them), coarse `last_in_offset` attribution stamps every echoed `Out` chunk with only the
//! newest `in_offset`, and single-entry `apply_output_caused` retires at most one byte.
//!
//! [`InFlightEchoQueue`] maintains a bounded FIFO of un-echoed input bytes (`<= MAX_IN_FLIGHT_ECHO_BYTES`,
//! certified by [`echo_queue_within_cap`] and Clean-origin [`echo_queue_len_clamp`]) along
//! with each byte's expected POSIX `termios` cooked/ECHOCTL/ONLCR echo expansion, and
//! attributes arbitrary split or coalesced PTY `Out` chunks back to the exact sequence of
//! `(in_offset, client_seq)` writes they echo, advancing `last_retired_in_offset`
//! monotonically via Clean-origin [`echo_matched_advance`].

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "overlap_echo_island.rs"]
mod overlap_echo_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{echo_matched_advance, echo_queue_len_clamp};
#[cfg(clean_islands)]
pub use overlap_echo_island::{echo_matched_advance, echo_queue_len_clamp};

contract_fn! {
    /// Kernel-certified check that the queued in-flight byte count fits within `cap`
    /// (`queued <= cap`), linked via `clean-kernel-defeq` to `echo_queue_within_cap_isl`.
    #[must_use]
    pub const fn echo_queue_within_cap(queued: usize, cap: usize) -> bool
    clauses [ensures result == (queued <= cap)]
    {
        queued <= cap
    }
}

/// Maximum number of un-echoed input bytes retained in [`InFlightEchoQueue`].
pub const MAX_IN_FLIGHT_ECHO_BYTES: usize = 4096;

/// Expected POSIX `termios` (`ECHO | ECHOE | ECHOCTL | ONLCR`) echo expansion for one input byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExpectedEcho {
    bytes: [u8; 3],
    len: u8,
}

impl ExpectedEcho {
    /// Empty echo (used for escape-sequence bytes that produce no direct line-discipline echo).
    pub const NONE: Self = Self {
        bytes: [0; 3],
        len: 0,
    };

    /// Expected echo slice (`0..=3` bytes).
    #[must_use]
    pub const fn as_slice(&self) -> &[u8] {
        match self.len {
            0 => &[],
            1 => match self.bytes.first_chunk::<1>() {
                Some(c) => c,
                None => &[],
            },
            2 => match self.bytes.first_chunk::<2>() {
                Some(c) => c,
                None => &[],
            },
            _ => &self.bytes,
        }
    }

    /// Derive the standard cooked-mode (`ECHO | ECHOE | ECHOCTL | ONLCR`) echo for `input_byte`.
    #[must_use]
    pub const fn cooked_for_byte(input_byte: u8) -> Self {
        if matches!(input_byte, 0x20..=0x7e) {
            Self {
                bytes: [input_byte, 0, 0],
                len: 1,
            }
        } else if input_byte == b'\r' || input_byte == b'\n' {
            Self {
                bytes: [b'\r', b'\n', 0],
                len: 2,
            }
        } else if input_byte == 0x7f || input_byte == 0x08 {
            // Cooked `ECHOE` rubout (`BS SP BS`).
            Self {
                bytes: [0x08, b' ', 0x08],
                len: 3,
            }
        } else if input_byte == b'\t' {
            Self {
                bytes: [b'\t', 0, 0],
                len: 1,
            }
        } else if input_byte < 0x20 && input_byte != 0x1b {
            // `ECHOCTL` caret notation (`^A` .. `^_`).
            Self {
                bytes: [b'^', input_byte.wrapping_add(0x40), 0],
                len: 2,
            }
        } else {
            Self::NONE
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct InFlightByte {
    in_offset: u64,
    client_seq: u64,
    input_byte: u8,
    expected: ExpectedEcho,
    matched_echo_pos: u8,
    is_last_of_write: bool,
}

/// Contiguous attributed slice of a PTY `Out` chunk matched to one `(in_offset, client_seq)` write.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttributedEchoSpan {
    /// Engine `In` offset that caused this echoed byte range.
    pub in_offset: u64,
    /// Client sequence number of the originating input proposal.
    pub client_seq: u64,
    /// Start..end byte indices inside the `Out` chunk attributed to `in_offset`.
    pub out_range: (usize, usize),
    /// Number of input bytes from `in_offset` whose expected echo completed in this span.
    pub completed_input_bytes: usize,
    /// `true` iff the final byte of the `in_offset` write completed its echo in this span.
    pub write_completed: bool,
}

/// Result of attributing one PTY `Out` chunk against [`InFlightEchoQueue`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EchoAttribution {
    /// Ordered causal spans within `out_bytes` across one or more overlapping writes.
    pub spans: Vec<AttributedEchoSpan>,
    /// Number of leading bytes in `out_bytes` accounted for as line-discipline echoes.
    pub echoed_out_bytes: usize,
    /// Monotone highest `in_offset` echoed in this chunk (suitable for `CausedBy` stamping).
    pub highest_in_offset: Option<u64>,
    /// Earliest `in_offset` echoed in this chunk.
    pub earliest_in_offset: Option<u64>,
}

/// Bounded per-byte FIFO tracking overlapping un-echoed PTY writes and attributing echoes.
#[derive(Debug, Clone)]
pub struct InFlightEchoQueue {
    entries: VecDeque<InFlightByte>,
    cap: usize,
    last_retired_in_offset: Option<u64>,
}

impl Default for InFlightEchoQueue {
    fn default() -> Self {
        Self::new()
    }
}

impl InFlightEchoQueue {
    /// Create a queue with [`MAX_IN_FLIGHT_ECHO_BYTES`] capacity.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: VecDeque::new(),
            cap: MAX_IN_FLIGHT_ECHO_BYTES,
            last_retired_in_offset: None,
        }
    }

    /// Create a queue with an explicit capacity clamped to `[1, MAX_IN_FLIGHT_ECHO_BYTES]`.
    #[must_use]
    pub fn with_capacity_cap(cap: usize) -> Self {
        let bounded = echo_queue_len_clamp(cap as u64, MAX_IN_FLIGHT_ECHO_BYTES as u64) as usize;
        let effective = if bounded == 0 { 1 } else { bounded };
        Self {
            entries: VecDeque::new(),
            cap: effective,
            last_retired_in_offset: None,
        }
    }

    /// Number of un-echoed input bytes currently in flight (`<= self.capacity_cap()`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether no un-echoed input bytes remain in flight.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Configured capacity ceiling (`<= MAX_IN_FLIGHT_ECHO_BYTES`).
    #[must_use]
    pub const fn capacity_cap(&self) -> usize {
        self.cap
    }

    /// Highest `in_offset` retired by echo attribution so far.
    #[must_use]
    pub const fn last_retired_in_offset(&self) -> Option<u64> {
        self.last_retired_in_offset
    }

    /// Clear all pending un-echoed bytes (e.g. on no-echo password mode or TUI altscreen).
    pub fn clear(&mut self) {
        self.entries.clear();
        self.trim_storage();
    }

    // Removing a prefix advances the ring head without copying unread entries.
    fn discard_prefix(&mut self, count: usize) {
        for _ in 0..count {
            let _ = self.entries.pop_front();
        }
    }

    fn trim_storage(&mut self) {
        let len = self.entries.len();
        let capacity = self.entries.capacity();
        if len == 0 && capacity > 16 {
            self.entries = VecDeque::new();
        } else if capacity > 64 && len <= capacity / 4 {
            // Quarter-full hysteresis bounds retained paste memory while charging
            // only linear survivor movement over a FIFO drain. Ordinary prefix
            // removal still advances the ring head without copying survivors.
            #[cfg(test)]
            storage_work::moved(len);
            self.entries.shrink_to(len.saturating_mul(2).max(16));
        }
    }

    /// Record an in-flight PTY write `(in_offset, client_seq, bytes)`.
    ///
    /// Escape sequences (`ESC ...`) produce no direct line-discipline echo and are skipped
    /// wherever they appear in `bytes`; if the queue reaches `self.cap`, the oldest un-echoed
    /// prefix is dropped so memory stays strictly bounded (`echo_queue_within_cap(self.len(), self.cap)`).
    pub fn push_input(&mut self, in_offset: u64, client_seq: u64, bytes: &[u8]) -> usize {
        if bytes.is_empty() {
            return 0;
        }
        let mut echoable_count = 0usize;
        let mut scan_idx = 0usize;
        while let Some(&b) = bytes.get(scan_idx) {
            if b == 0x1b {
                scan_idx = skip_input_escape(bytes, scan_idx.saturating_add(1));
                continue;
            }
            let exp = ExpectedEcho::cooked_for_byte(b);
            if exp.len > 0 {
                echoable_count = echoable_count.saturating_add(1);
            }
            scan_idx = scan_idx.saturating_add(1);
        }
        if echoable_count == 0 {
            return 0;
        }
        // Keep only the suffix that fits in `self.cap` if a single burst exceeds `self.cap`.
        let skip_echoable = echoable_count.saturating_sub(self.cap);
        let to_add = echoable_count.saturating_sub(skip_echoable);
        let max_keep = self.cap.saturating_sub(to_add);
        if self.entries.len() > max_keep {
            let drop_n = self.entries.len().saturating_sub(max_keep);
            self.discard_prefix(drop_n);
        }
        let mut added = 0usize;
        let mut seen_echoable = 0usize;
        let mut idx = 0usize;
        while let Some(&b) = bytes.get(idx) {
            if b == 0x1b {
                idx = skip_input_escape(bytes, idx.saturating_add(1));
                continue;
            }
            let exp = ExpectedEcho::cooked_for_byte(b);
            if exp.len > 0 {
                seen_echoable = seen_echoable.saturating_add(1);
                if seen_echoable > skip_echoable
                    && echo_queue_within_cap(self.entries.len().saturating_add(1), self.cap)
                {
                    self.entries.push_back(InFlightByte {
                        in_offset,
                        client_seq,
                        input_byte: b,
                        expected: exp,
                        matched_echo_pos: 0,
                        is_last_of_write: seen_echoable == echoable_count,
                    });
                    added = added.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        added
    }

    /// Attribute a PTY `Out` byte chunk against the FIFO of overlapping in-flight writes.
    ///
    /// Handles:
    /// - **Coalesced echoes** where one `Out` chunk (`"abcd"`) answers multiple writes
    ///   (`in_offset = 10` `"ab"` and `in_offset = 11` `"cd"`), emitting one
    ///   [`AttributedEchoSpan`] per write in exact causal order.
    /// - **Split / multi-byte echoes** where an `Out` chunk splits mid-write (`"ab"` + `"c"`)
    ///   or mid-expansion (`"\r"` + `"\n"` for `ONLCR`, `"^"` + `"C"` for `ECHOCTL`, or
    ///   `"\x08 "` + `"\x08"` for `ECHOE`).
    /// - **Raw newline fallback** where `\n` echoes as bare `\n` (`!ONLCR`) as well as `\r\n`.
    pub fn attribute_output(&mut self, out_bytes: &[u8]) -> EchoAttribution {
        let mut spans: Vec<AttributedEchoSpan> = Vec::new();
        let mut out_idx = 0usize;
        let mut head = 0usize;
        let mut earliest: Option<u64> = None;
        let mut highest: Option<u64> = None;

        while out_idx < out_bytes.len() && head < self.entries.len() {
            let (Some(&out_b), Some(&entry)) = (out_bytes.get(out_idx), self.entries.get(head))
            else {
                break;
            };
            let exp_slice = entry.expected.as_slice();
            let pos = entry.matched_echo_pos as usize;
            let Some(&want_b) = exp_slice.get(pos) else {
                head = head.saturating_add(1);
                continue;
            };

            let (matched, completed_entry) = if out_b == want_b {
                let next_pos = pos.saturating_add(1);
                (true, next_pos >= exp_slice.len())
            } else if (entry.input_byte == b'\n' || entry.input_byte == b'\r')
                && pos == 0
                && out_b == b'\n'
            {
                // Raw / non-ONLCR line discipline echoed bare LF for CR/LF input.
                (true, true)
            } else if (entry.input_byte == 0x7f || entry.input_byte == 0x08)
                && pos == 0
                && out_b == b'^'
                && out_bytes
                    .get(out_idx.saturating_add(1))
                    .is_none_or(|&next| next == b'?')
            {
                // The caret prefix can end a PTY read. Remember it just as we
                // remember a partial CRLF or rubout; a known wrong continuation
                // still rejects this fallback before consuming its prefix.
                if let Some(slot) = self.entries.get_mut(head) {
                    slot.expected = ExpectedEcho {
                        bytes: [b'^', b'?', 0],
                        len: 2,
                    };
                }
                (true, false)
            } else {
                (false, false)
            };

            if !matched {
                break;
            }

            if earliest.is_none() {
                earliest = Some(entry.in_offset);
            }
            highest = Some(match highest {
                Some(cur) => echo_matched_advance(cur, entry.in_offset),
                None => entry.in_offset,
            });
            self.last_retired_in_offset = Some(match self.last_retired_in_offset {
                Some(cur) => echo_matched_advance(cur, entry.in_offset),
                None => entry.in_offset,
            });

            let next_out_idx = out_idx.saturating_add(1);
            let done_input_inc = usize::from(completed_entry);
            let write_done = completed_entry && entry.is_last_of_write;

            if let Some(last_span) = spans.last_mut() {
                if last_span.in_offset == entry.in_offset
                    && last_span.client_seq == entry.client_seq
                    && last_span.out_range.1 == out_idx
                {
                    last_span.out_range.1 = next_out_idx;
                    last_span.completed_input_bytes = last_span
                        .completed_input_bytes
                        .saturating_add(done_input_inc);
                    if write_done {
                        last_span.write_completed = true;
                    }
                } else {
                    spans.push(AttributedEchoSpan {
                        in_offset: entry.in_offset,
                        client_seq: entry.client_seq,
                        out_range: (out_idx, next_out_idx),
                        completed_input_bytes: done_input_inc,
                        write_completed: write_done,
                    });
                }
            } else {
                spans.push(AttributedEchoSpan {
                    in_offset: entry.in_offset,
                    client_seq: entry.client_seq,
                    out_range: (out_idx, next_out_idx),
                    completed_input_bytes: done_input_inc,
                    write_completed: write_done,
                });
            }

            if completed_entry {
                head = head.saturating_add(1);
            } else if let Some(slot) = self.entries.get_mut(head) {
                slot.matched_echo_pos = entry.matched_echo_pos.saturating_add(1);
            }
            out_idx = next_out_idx;
        }

        if head > 0 {
            self.discard_prefix(head);
            self.trim_storage();
        }

        EchoAttribution {
            spans,
            echoed_out_bytes: out_idx,
            highest_in_offset: highest,
            earliest_in_offset: earliest,
        }
    }
}

fn skip_input_escape(slice: &[u8], after_esc: usize) -> usize {
    let Some(&intro) = slice.get(after_esc) else {
        return after_esc;
    };
    if intro == b'[' {
        let mut p = after_esc.saturating_add(1);
        while let Some(&c) = slice.get(p) {
            if matches!(c, 0x40..=0x7e) {
                return p.saturating_add(1);
            }
            if matches!(c, 0x20..=0x3f) {
                p = p.saturating_add(1);
            } else {
                return p;
            }
        }
        return p;
    }
    if intro == b']' || intro == b'P' || intro == b'X' || intro == b'^' || intro == b'_' {
        let mut p = after_esc.saturating_add(1);
        while let Some(&c) = slice.get(p) {
            if c == 0x07 {
                return p.saturating_add(1);
            }
            if c == 0x1b {
                if slice.get(p.saturating_add(1)) == Some(&b'\\') {
                    return p.saturating_add(2);
                }
                return p;
            }
            p = p.saturating_add(1);
        }
        return p;
    }
    let mut p = after_esc;
    while let Some(&c) = slice.get(p) {
        if matches!(c, 0x20..=0x2f) {
            p = p.saturating_add(1);
        } else {
            break;
        }
    }
    if matches!(slice.get(p), Some(&(0x30..=0x7e))) {
        p.saturating_add(1)
    } else {
        p
    }
}

#[cfg(test)]
mod storage_work {
    use std::cell::Cell;
    thread_local! {
        static MOVED: Cell<usize> = const { Cell::new(0) };
    }
    pub(super) fn moved(n: usize) {
        MOVED.with(|count| count.set(count.get().saturating_add(n)));
    }
    pub(super) fn take() -> usize {
        MOVED.with(|count| count.replace(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesced_overlapping_writes_attribute_exact_per_write_spans() {
        let mut q = InFlightEchoQueue::new();
        assert_eq!(q.push_input(10, 1, b"ab"), 2);
        assert_eq!(q.push_input(11, 2, b"cd"), 2);
        assert_eq!(q.push_input(12, 3, b"\n"), 1);

        // Coalesced echo `"abcd\r\n$ "` attributes `[0..2)` -> 10, `[2..4)` -> 11, `[4..6)` -> 12,
        // stopping cleanly before the shell prompt `"$ "`!
        let att = q.attribute_output(b"abcd\r\n$ ");
        assert_eq!(att.echoed_out_bytes, 6);
        assert_eq!(att.earliest_in_offset, Some(10));
        assert_eq!(att.highest_in_offset, Some(12));
        assert_eq!(q.last_retired_in_offset(), Some(12));
        assert!(q.is_empty());
        assert_eq!(
            att.spans,
            vec![
                AttributedEchoSpan {
                    in_offset: 10,
                    client_seq: 1,
                    out_range: (0, 2),
                    completed_input_bytes: 2,
                    write_completed: true,
                },
                AttributedEchoSpan {
                    in_offset: 11,
                    client_seq: 2,
                    out_range: (2, 4),
                    completed_input_bytes: 2,
                    write_completed: true,
                },
                AttributedEchoSpan {
                    in_offset: 12,
                    client_seq: 3,
                    out_range: (4, 6),
                    completed_input_bytes: 1,
                    write_completed: true,
                },
            ]
        );
    }

    #[test]
    fn split_echoctl_and_echoe_chunks_resume_across_boundaries() {
        let mut q = InFlightEchoQueue::with_capacity_cap(8);
        assert_eq!(q.push_input(20, 1, b"\x03\x7f"), 2); // ^C (2 bytes) + BS SP BS (3 bytes)

        let a1 = q.attribute_output(b"^");
        assert_eq!(a1.echoed_out_bytes, 1);
        assert_eq!(a1.spans[0].completed_input_bytes, 0);
        assert!(!a1.spans[0].write_completed);
        assert_eq!(q.len(), 2);

        let a2 = q.attribute_output(b"C\x08 ");
        assert_eq!(a2.echoed_out_bytes, 3);
        assert_eq!(a2.spans[0].completed_input_bytes, 1);
        assert!(!a2.spans[0].write_completed);
        assert_eq!(q.len(), 1);

        let a3 = q.attribute_output(b"\x08");
        assert_eq!(a3.echoed_out_bytes, 1);
        assert_eq!(a3.spans[0].completed_input_bytes, 1);
        assert!(a3.spans[0].write_completed);
        assert!(q.is_empty());
    }

    #[test]
    fn embedded_escape_sequences_are_skipped_without_polluting_echo_queue() {
        let mut q = InFlightEchoQueue::new();
        assert_eq!(q.push_input(1, 1, b"\x1b[A"), 0);
        assert_eq!(q.push_input(2, 2, b"ls\x1b[D!"), 3);
        let att = q.attribute_output(b"ls!");
        assert_eq!(att.echoed_out_bytes, 3);
        assert_eq!(att.spans.len(), 1);
        assert!(att.spans[0].write_completed);
        assert!(q.is_empty());
    }

    #[test]
    fn capacity_cap_evicts_oldest_prefix_without_remove_panics() {
        let mut q = InFlightEchoQueue::with_capacity_cap(4);
        assert_eq!(q.push_input(1, 1, b"abc"), 3);
        assert_eq!(q.push_input(2, 2, b"de"), 2);
        assert_eq!(q.len(), 4);
        let att = q.attribute_output(b"bcde");
        assert_eq!(att.echoed_out_bytes, 4);
        assert_eq!(att.earliest_in_offset, Some(1));
        assert_eq!(att.highest_in_offset, Some(2));
        assert!(q.is_empty());

        assert_eq!(q.push_input(3, 3, b"uvwxyz"), 4);
        assert_eq!(q.len(), 4);
        let att2 = q.attribute_output(b"wxyz");
        assert_eq!(att2.echoed_out_bytes, 4);
        assert!(att2.spans[0].write_completed);
        assert!(q.is_empty());
    }

    #[test]
    fn caret_erase_echo_keeps_attribution_across_every_chunk_partition() {
        // Each bit chooses a boundary in the same output stream. This covers
        // the split between ^ and ?, plus coalescing either half with another
        // write or with the CRLF expansion following it.
        let output = b"a^?b\r\n";
        let owners = [10, 12, 12, 14, 14, 14];
        for erase in [0x7f, 0x08] {
            for boundaries in 0..1usize << (output.len() - 1) {
                let mut q = InFlightEchoQueue::new();
                q.push_input(10, 1, b"a");
                q.push_input(12, 2, &[erase]);
                q.push_input(14, 3, b"b\n");
                let mut completed = [0usize; 3];
                let mut finished = [0usize; 3];
                let mut from = 0;
                for to in 1..=output.len() {
                    if to < output.len() && boundaries & (1 << (to - 1)) == 0 {
                        continue;
                    }
                    let chunk = &output[from..to];
                    let att = q.attribute_output(chunk);
                    assert_eq!(att.echoed_out_bytes, chunk.len());
                    assert_eq!(att.earliest_in_offset, Some(owners[from]));
                    assert_eq!(att.highest_in_offset, Some(owners[to - 1]));
                    assert_eq!(q.last_retired_in_offset(), Some(owners[to - 1]));
                    let mut covered = 0;
                    for span in att.spans {
                        assert_eq!(span.out_range.0, covered);
                        for &owner in &owners[from + span.out_range.0..from + span.out_range.1] {
                            assert_eq!(span.in_offset, owner);
                        }
                        let idx = match span.in_offset {
                            10 => 0,
                            12 => 1,
                            14 => 2,
                            other => panic!("unexpected owner {other}"),
                        };
                        assert_eq!(span.client_seq, idx as u64 + 1);
                        completed[idx] += span.completed_input_bytes;
                        finished[idx] += usize::from(span.write_completed);
                        covered = span.out_range.1;
                    }
                    assert_eq!(covered, chunk.len());
                    // Empty reads neither consume a pending prefix nor advance
                    // its completion bookkeeping.
                    let entries = q.entries.clone();
                    let empty = q.attribute_output(b"");
                    assert_eq!(empty.echoed_out_bytes, 0);
                    assert!(empty.spans.is_empty());
                    assert_eq!(q.entries, entries);
                    from = to;
                }
                assert_eq!(completed, [1, 1, 2]);
                assert_eq!(finished, [1, 1, 1]);
                assert!(q.is_empty());
            }
        }
    }

    #[test]
    fn caret_erase_fallback_rejects_a_known_wrong_continuation() {
        let mut q = InFlightEchoQueue::new();
        q.push_input(7, 9, b"\x7f");
        let original = q.entries.clone();
        let att = q.attribute_output(b"^X");
        assert_eq!(att.echoed_out_bytes, 0);
        assert!(att.spans.is_empty());
        assert_eq!(q.entries, original);
        assert_eq!(q.last_retired_in_offset(), None);
        let att = q.attribute_output(b"\x08 \x08");
        assert_eq!(att.echoed_out_bytes, 3);
        assert_eq!(att.spans[0].completed_input_bytes, 1);
        assert!(att.spans[0].write_completed);
        assert!(q.is_empty());
    }
}

#[cfg(test)]
mod deque_tests {
    use super::*;

    // The previous Vec storage is retained as a behavioral oracle and benchmark
    // reference. Both matchers include the later split-caret correction below;
    // all other matching ambiguity remains the same as the original queue.
    #[derive(Debug, Clone)]
    pub struct LegacyQueue {
        entries: Vec<InFlightByte>,
        moved: usize,
        cap: usize,
        last_retired_in_offset: Option<u64>,
    }

    impl Default for LegacyQueue {
        fn default() -> Self {
            Self::new()
        }
    }

    impl LegacyQueue {
        /// Create a queue with [`MAX_IN_FLIGHT_ECHO_BYTES`] capacity.
        #[must_use]
        pub const fn new() -> Self {
            Self {
                entries: Vec::new(),
                moved: 0,
                cap: MAX_IN_FLIGHT_ECHO_BYTES,
                last_retired_in_offset: None,
            }
        }

        /// Create a queue with an explicit capacity clamped to `[1, MAX_IN_FLIGHT_ECHO_BYTES]`.
        #[must_use]
        pub fn with_capacity_cap(cap: usize) -> Self {
            let bounded =
                echo_queue_len_clamp(cap as u64, MAX_IN_FLIGHT_ECHO_BYTES as u64) as usize;
            let effective = if bounded == 0 { 1 } else { bounded };
            Self {
                entries: Vec::new(),
                moved: 0,
                cap: effective,
                last_retired_in_offset: None,
            }
        }

        /// Number of un-echoed input bytes currently in flight (`<= self.capacity_cap()`).
        #[must_use]
        pub fn len(&self) -> usize {
            self.entries.len()
        }

        /// Whether no un-echoed input bytes remain in flight.
        #[must_use]
        pub fn is_empty(&self) -> bool {
            self.entries.is_empty()
        }

        /// Configured capacity ceiling (`<= MAX_IN_FLIGHT_ECHO_BYTES`).
        #[must_use]
        pub const fn capacity_cap(&self) -> usize {
            self.cap
        }

        /// Highest `in_offset` retired by echo attribution so far.
        #[must_use]
        pub const fn last_retired_in_offset(&self) -> Option<u64> {
            self.last_retired_in_offset
        }

        /// Clear all pending un-echoed bytes (e.g. on no-echo password mode or TUI altscreen).
        pub fn clear(&mut self) {
            self.entries.clear();
        }

        /// Record an in-flight PTY write `(in_offset, client_seq, bytes)`.
        ///
        /// Escape sequences (`ESC ...`) produce no direct line-discipline echo and are skipped
        /// wherever they appear in `bytes`; if the queue reaches `self.cap`, the oldest un-echoed
        /// prefix is dropped so memory stays strictly bounded (`echo_queue_within_cap(self.len(), self.cap)`).
        pub fn push_input(&mut self, in_offset: u64, client_seq: u64, bytes: &[u8]) -> usize {
            if bytes.is_empty() {
                return 0;
            }
            let mut echoable_count = 0usize;
            let mut scan_idx = 0usize;
            while let Some(&b) = bytes.get(scan_idx) {
                if b == 0x1b {
                    scan_idx = skip_input_escape(bytes, scan_idx.saturating_add(1));
                    continue;
                }
                let exp = ExpectedEcho::cooked_for_byte(b);
                if exp.len > 0 {
                    echoable_count = echoable_count.saturating_add(1);
                }
                scan_idx = scan_idx.saturating_add(1);
            }
            if echoable_count == 0 {
                return 0;
            }
            // Keep only the suffix that fits in `self.cap` if a single burst exceeds `self.cap`.
            let skip_echoable = echoable_count.saturating_sub(self.cap);
            let to_add = echoable_count.saturating_sub(skip_echoable);
            let max_keep = self.cap.saturating_sub(to_add);
            if self.entries.len() > max_keep {
                let drop_n = self.entries.len().saturating_sub(max_keep);
                let mut trimmed = Vec::new();
                if let Some(tail) = self.entries.get(drop_n..) {
                    trimmed.extend_from_slice(tail);
                }
                self.moved = self.moved.saturating_add(trimmed.len());
                self.entries = trimmed;
            }
            let mut added = 0usize;
            let mut seen_echoable = 0usize;
            let mut idx = 0usize;
            while let Some(&b) = bytes.get(idx) {
                if b == 0x1b {
                    idx = skip_input_escape(bytes, idx.saturating_add(1));
                    continue;
                }
                let exp = ExpectedEcho::cooked_for_byte(b);
                if exp.len > 0 {
                    seen_echoable = seen_echoable.saturating_add(1);
                    if seen_echoable > skip_echoable
                        && echo_queue_within_cap(self.entries.len().saturating_add(1), self.cap)
                    {
                        self.entries.push(InFlightByte {
                            in_offset,
                            client_seq,
                            input_byte: b,
                            expected: exp,
                            matched_echo_pos: 0,
                            is_last_of_write: seen_echoable == echoable_count,
                        });
                        added = added.saturating_add(1);
                    }
                }
                idx = idx.saturating_add(1);
            }
            added
        }

        /// Attribute a PTY `Out` byte chunk against the FIFO of overlapping in-flight writes.
        ///
        /// Handles:
        /// - **Coalesced echoes** where one `Out` chunk (`"abcd"`) answers multiple writes
        ///   (`in_offset = 10` `"ab"` and `in_offset = 11` `"cd"`), emitting one
        ///   [`AttributedEchoSpan`] per write in exact causal order.
        /// - **Split / multi-byte echoes** where an `Out` chunk splits mid-write (`"ab"` + `"c"`)
        ///   or mid-expansion (`"\r"` + `"\n"` for `ONLCR`, `"^"` + `"C"` for `ECHOCTL`, or
        ///   `"\x08 "` + `"\x08"` for `ECHOE`).
        /// - **Raw newline fallback** where `\n` echoes as bare `\n` (`!ONLCR`) as well as `\r\n`.
        pub fn attribute_output(&mut self, out_bytes: &[u8]) -> EchoAttribution {
            let mut spans: Vec<AttributedEchoSpan> = Vec::new();
            let mut out_idx = 0usize;
            let mut head = 0usize;
            let mut earliest: Option<u64> = None;
            let mut highest: Option<u64> = None;

            while out_idx < out_bytes.len() && head < self.entries.len() {
                let (Some(&out_b), Some(&entry)) = (out_bytes.get(out_idx), self.entries.get(head))
                else {
                    break;
                };
                let exp_slice = entry.expected.as_slice();
                let pos = entry.matched_echo_pos as usize;
                let Some(&want_b) = exp_slice.get(pos) else {
                    head = head.saturating_add(1);
                    continue;
                };

                let (matched, completed_entry) = if out_b == want_b {
                    let next_pos = pos.saturating_add(1);
                    (true, next_pos >= exp_slice.len())
                } else if (entry.input_byte == b'\n' || entry.input_byte == b'\r')
                    && pos == 0
                    && out_b == b'\n'
                {
                    // Raw / non-ONLCR line discipline echoed bare LF for CR/LF input.
                    (true, true)
                } else if (entry.input_byte == 0x7f || entry.input_byte == 0x08)
                    && pos == 0
                    && out_b == b'^'
                    && out_bytes
                        .get(out_idx.saturating_add(1))
                        .is_none_or(|&next| next == b'?')
                {
                    // `ECHOCTL` without `ECHOE` echoed `^?` for DEL; rewrite expected to `^?`.
                    if let Some(slot) = self.entries.get_mut(head) {
                        slot.expected = ExpectedEcho {
                            bytes: [b'^', b'?', 0],
                            len: 2,
                        };
                    }
                    (true, false)
                } else {
                    (false, false)
                };

                if !matched {
                    break;
                }

                if earliest.is_none() {
                    earliest = Some(entry.in_offset);
                }
                highest = Some(match highest {
                    Some(cur) => echo_matched_advance(cur, entry.in_offset),
                    None => entry.in_offset,
                });
                self.last_retired_in_offset = Some(match self.last_retired_in_offset {
                    Some(cur) => echo_matched_advance(cur, entry.in_offset),
                    None => entry.in_offset,
                });

                let next_out_idx = out_idx.saturating_add(1);
                let done_input_inc = usize::from(completed_entry);
                let write_done = completed_entry && entry.is_last_of_write;

                if let Some(last_span) = spans.last_mut() {
                    if last_span.in_offset == entry.in_offset
                        && last_span.client_seq == entry.client_seq
                        && last_span.out_range.1 == out_idx
                    {
                        last_span.out_range.1 = next_out_idx;
                        last_span.completed_input_bytes = last_span
                            .completed_input_bytes
                            .saturating_add(done_input_inc);
                        if write_done {
                            last_span.write_completed = true;
                        }
                    } else {
                        spans.push(AttributedEchoSpan {
                            in_offset: entry.in_offset,
                            client_seq: entry.client_seq,
                            out_range: (out_idx, next_out_idx),
                            completed_input_bytes: done_input_inc,
                            write_completed: write_done,
                        });
                    }
                } else {
                    spans.push(AttributedEchoSpan {
                        in_offset: entry.in_offset,
                        client_seq: entry.client_seq,
                        out_range: (out_idx, next_out_idx),
                        completed_input_bytes: done_input_inc,
                        write_completed: write_done,
                    });
                }

                if completed_entry {
                    head = head.saturating_add(1);
                } else if let Some(slot) = self.entries.get_mut(head) {
                    slot.matched_echo_pos = entry.matched_echo_pos.saturating_add(1);
                }
                out_idx = next_out_idx;
            }

            if head > 0 {
                let mut remaining = Vec::new();
                if let Some(tail) = self.entries.get(head..) {
                    remaining.extend_from_slice(tail);
                }
                self.moved = self.moved.saturating_add(remaining.len());
                self.entries = remaining;
            }

            EchoAttribution {
                spans,
                echoed_out_bytes: out_idx,
                highest_in_offset: highest,
                earliest_in_offset: earliest,
            }
        }
    }

    fn assert_same(queue: &InFlightEchoQueue, legacy: &LegacyQueue) {
        assert_eq!(queue.len(), legacy.len());
        assert_eq!(queue.is_empty(), legacy.is_empty());
        assert_eq!(queue.capacity_cap(), legacy.capacity_cap());
        assert_eq!(
            queue.last_retired_in_offset(),
            legacy.last_retired_in_offset()
        );
        assert!(echo_queue_within_cap(queue.len(), queue.capacity_cap()));
        assert_eq!(
            queue.entries.iter().copied().collect::<Vec<_>>(),
            legacy.entries
        );
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
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    #[test]
    fn deque_matches_vec_for_overlapping_split_echoes_escape_skips_and_cap_pressure() {
        const BYTES: &[u8] = b"abc xyz\r\n\t\x03\x7f\x08\x1b[A\x1b]t\x07\xff";
        for cap in [
            0,
            1,
            2,
            3,
            7,
            8,
            31,
            64,
            MAX_IN_FLIGHT_ECHO_BYTES,
            usize::MAX,
        ] {
            for seed in 1..=32 {
                let mut rng = Rng(seed * 0x9e37_79b9);
                let mut queue = InFlightEchoQueue::with_capacity_cap(cap);
                let mut legacy = LegacyQueue::with_capacity_cap(cap);
                for _ in 0..600 {
                    match rng.below(12) {
                        0..=5 => {
                            let len = rng.below(80);
                            let bytes: Vec<_> =
                                (0..len).map(|_| BYTES[rng.below(BYTES.len())]).collect();
                            let offset = match rng.below(8) {
                                0 => 0,
                                1 => u64::MAX,
                                _ => rng.next(),
                            };
                            let seq = rng.next();
                            assert_eq!(
                                queue.push_input(offset, seq, &bytes),
                                legacy.push_input(offset, seq, &bytes)
                            );
                        }
                        6..=10 => {
                            let mut out = Vec::new();
                            if rng.below(4) > 0 {
                                let take = rng.below(8) + 1;
                                for entry in legacy.entries.iter().take(take) {
                                    if entry.matched_echo_pos == 0
                                        && matches!(entry.input_byte, b'\r' | b'\n')
                                        && rng.below(3) == 0
                                    {
                                        out.push(b'\n');
                                    } else if entry.matched_echo_pos == 0
                                        && matches!(entry.input_byte, 0x7f | 0x08)
                                        && rng.below(3) == 0
                                    {
                                        out.extend_from_slice(b"^?");
                                    } else {
                                        out.extend_from_slice(
                                            &entry.expected.as_slice()
                                                [entry.matched_echo_pos as usize..],
                                        );
                                    }
                                }
                                if !out.is_empty() && rng.below(2) == 0 {
                                    out.truncate(1 + rng.below(out.len()));
                                }
                            } else {
                                out.push(BYTES[rng.below(BYTES.len())]);
                            }
                            if rng.below(8) == 0 {
                                out.extend_from_slice(b"$ ");
                            }
                            assert_eq!(queue.attribute_output(&out), legacy.attribute_output(&out));
                        }
                        _ => {
                            queue.clear();
                            legacy.clear();
                        }
                    }
                    assert_same(&queue, &legacy);
                }
            }
        }
        assert_same(&InFlightEchoQueue::default(), &LegacyQueue::default());
    }

    #[test]
    fn ring_wrap_and_cap_eviction_keep_surviving_entries_at_the_same_address() {
        let mut queue = InFlightEchoQueue::with_capacity_cap(7);
        let mut legacy = LegacyQueue::with_capacity_cap(7);
        queue.push_input(1, 1, b"aaaa");
        legacy.push_input(1, 1, b"aaaa");
        let mut wrapped = false;
        for n in 0..32 {
            assert_eq!(
                queue.push_input(n + 2, n + 2, b"b"),
                legacy.push_input(n + 2, n + 2, b"b")
            );
            let survivor = queue.entries.back().unwrap() as *const InFlightByte;
            let byte = legacy.entries[0].input_byte;
            assert_eq!(
                queue.attribute_output(&[byte]),
                legacy.attribute_output(&[byte])
            );
            assert_eq!(
                queue.entries.back().unwrap() as *const InFlightByte,
                survivor
            );
            assert_same(&queue, &legacy);
            wrapped |= !queue.entries.as_slices().1.is_empty();
        }
        assert!(wrapped, "exercise both physical ring slices");
        assert_eq!(
            queue.push_input(40, 40, b"ccc"),
            legacy.push_input(40, 40, b"ccc")
        );
        assert_eq!(queue.len(), 7);
        let survivors: Vec<_> = queue
            .entries
            .iter()
            .skip(4)
            .map(|p| p as *const InFlightByte)
            .collect();
        let moved_before = legacy.moved;
        assert_eq!(
            queue.push_input(41, 41, b"dddd"),
            legacy.push_input(41, 41, b"dddd")
        );
        assert_eq!(legacy.moved - moved_before, 3);
        for (idx, pointer) in survivors.into_iter().enumerate() {
            assert_eq!(
                queue.entries.get(idx).unwrap() as *const InFlightByte,
                pointer
            );
        }
        assert_same(&queue, &legacy);
    }

    #[test]
    fn bytewise_fifo_has_linear_shrink_work_and_releases_large_empty_buffers() {
        const N: usize = MAX_IN_FLIGHT_ECHO_BYTES;
        let mut queue = InFlightEchoQueue::new();
        let mut legacy = LegacyQueue::new();
        let input = vec![b'x'; N];
        queue.push_input(1, 1, &input);
        legacy.push_input(1, 1, &input);
        let _ = storage_work::take();
        let mut shrink_moves = 0usize;
        for remaining in (0..N).rev() {
            let final_byte = queue.entries.back().unwrap() as *const InFlightByte;
            assert_eq!(queue.attribute_output(b"x"), legacy.attribute_output(b"x"));
            assert_eq!(queue.len(), remaining);
            let moved = storage_work::take();
            shrink_moves += moved;
            if remaining > 0 && moved == 0 {
                assert_eq!(
                    queue.entries.back().unwrap() as *const InFlightByte,
                    final_byte
                );
            }
            assert!(queue.entries.capacity() <= remaining.saturating_mul(4).max(64));
        }
        assert!(
            shrink_moves < N,
            "amortized shrinking moved {shrink_moves} survivors"
        );
        assert_eq!(legacy.moved, N * (N - 1) / 2);
        assert_eq!(queue.entries.capacity(), 0);
        assert_eq!(queue.last_retired_in_offset(), Some(1));
        queue.push_input(2, 2, &input);
        queue.clear();
        assert_eq!(queue.entries.capacity(), 0);
        assert_eq!(queue.last_retired_in_offset(), Some(1));
    }

    #[test]
    #[ignore = "manual echo FIFO and cap-eviction CPU benchmark"]
    fn echo_queue_microbench() {
        use std::hint::black_box;
        use std::time::Instant;
        for n in [1usize, 8, 64, 256, 1024, MAX_IN_FLIGHT_ECHO_BYTES] {
            for shape in ["fifo", "evict"] {
                let input = vec![b'x'; n];
                // Keep timer noise out of tiny bursts by timing the same 4096
                // operations across pre-filled independent queues on both sides.
                let repeats = MAX_IN_FLIGHT_ECHO_BYTES / n;
                let mut deque_ns = [0u128; 3];
                let mut vec_ns = [0u128; 3];
                let mut moved = 0usize;
                let mut deque_held = 0usize;
                let mut legacy_held = 0usize;
                for run in 0..3 {
                    let mut queues: Vec<_> = (0..repeats)
                        .map(|_| {
                            let mut queue = InFlightEchoQueue::with_capacity_cap(n);
                            queue.push_input(1, 1, &input);
                            queue
                        })
                        .collect();
                    let mut legacies: Vec<_> = (0..repeats)
                        .map(|_| {
                            let mut legacy = LegacyQueue::with_capacity_cap(n);
                            legacy.push_input(1, 1, &input);
                            legacy
                        })
                        .collect();
                    let mut time_deque = || {
                        let start = Instant::now();
                        for queue in &mut queues {
                            for i in 0..n {
                                if shape == "fifo" {
                                    black_box(queue.attribute_output(black_box(b"x")));
                                } else {
                                    black_box(queue.push_input(
                                        i as u64 + 2,
                                        i as u64 + 2,
                                        black_box(b"x"),
                                    ));
                                }
                            }
                        }
                        deque_ns[run] = start.elapsed().as_nanos();
                    };
                    let mut time_vec = || {
                        let start = Instant::now();
                        for legacy in &mut legacies {
                            for i in 0..n {
                                if shape == "fifo" {
                                    black_box(legacy.attribute_output(black_box(b"x")));
                                } else {
                                    black_box(legacy.push_input(
                                        i as u64 + 2,
                                        i as u64 + 2,
                                        black_box(b"x"),
                                    ));
                                }
                            }
                        }
                        vec_ns[run] = start.elapsed().as_nanos();
                    };
                    if run % 2 == 0 {
                        time_deque();
                        time_vec();
                    } else {
                        time_vec();
                        time_deque();
                    }
                    for (queue, legacy) in queues.iter().zip(&legacies) {
                        assert_same(queue, legacy);
                    }
                    moved = legacies.iter().map(|q| q.moved).sum();
                    deque_held =
                        queues.iter().map(|q| q.entries.capacity()).sum::<usize>() / repeats;
                    legacy_held =
                        legacies.iter().map(|q| q.entries.capacity()).sum::<usize>() / repeats;
                }
                deque_ns.sort_unstable();
                vec_ns.sort_unstable();
                println!(
                    "ECHO_QUEUE shape={shape} bytes={n} bursts={repeats} operations={} deque_ns={} vec_ns={} speedup={:.2} vec_survivors_copied={moved} deque_held_bytes_per_queue={} vec_held_bytes_per_queue={} entry_bytes={}",
                    n * repeats, deque_ns[1], vec_ns[1], vec_ns[1] as f64 / deque_ns[1].max(1) as f64,
                    deque_held * std::mem::size_of::<InFlightByte>(),
                    legacy_held * std::mem::size_of::<InFlightByte>(),
                    std::mem::size_of::<InFlightByte>()
                );
            }
        }
    }
}
