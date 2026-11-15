// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::collapsible_if, clippy::manual_is_ascii_check)]

//! Opt-in sticky producer gap fencing on refused batches (`DESIGN-aterm-fabric.md` §14
//! Open Question 7 & §15).
//!
//! By default (`OpenOptions::sticky_batch_refusal == false`), a transient append or
//! flush failure rolls back only the refused batch while allowing subsequent pipelined
//! writes from the same producer on a later batch to commit (`broker.poisoned-refusal`
//! negative control; `aterm` `a_refused_batch_lands_the_publish_sent_after_it`). Because
//! of that, a producer whose records must land in strict send order has to keep at most
//! **one** write in flight per sender (`Bridge::settle_sender`).
//!
//! When `OpenOptions::sticky_batch_refusal` is `true`, the broker OFFERS the fence, and a
//! connection that asks for it (`Request::FenceGaps`) is fenced for the rest of its life. A
//! connection that never asks is served as above: a client that predates the ask lifts no
//! fence either, so a refusal it does not retry next would fence everything it writes after
//! it. For the connections that asked, the broker maintains a bounded
//! per-`(conn_id, producer_id)` [`StickyFenceTable`]:
//! - Whenever a `Publish` or `ProcessAndProduce` for `(conn_id, producer_id, seq)` is
//!   refused (either op-level during staging, or batch-wide on commit/quorum failure),
//!   `fence_seq` is latched to `min(fence_seq, seq)` via [`sticky_fence_min_seq`].
//! - Any pipelined request with `req_seq > fence_seq` on `(conn_id, producer_id)` is
//!   refused in send order (`ERR gap-fenced=<fence_seq>: ...`) via
//!   [`sticky_fence_admits`], preventing out-of-order commits.
//! - Retrying `req_seq <= fence_seq` (the idempotent dedup retry every producer already
//!   performs after a refusal) is **admitted**, and once its batch commits, the fence on
//!   `(conn_id, producer_id)` clears automatically so pipelined successors behind the
//!   retry commit in order. Reconnecting also starts with a fresh `conn_id`.
//! - A producer that will not send the refused write again next (one refused for good, or
//!   a write it gives up) lifts every fence its connection holds with
//!   `Request::ClearGapFences` once it has read the answer to every write it sent: the
//!   broker answers it after every write sent before it ([`StickyFenceTable::drop_conn`],
//!   as a close does), so the lift reaches none of them. A close queues its lift on the
//!   broker writer after every write the connection decoded, so cleanup cannot overtake a
//!   pipelined successor whose acknowledgement the closing client did not read.
//! - Every `Hello` answered while the option is on says so (`REQUEST_GAP_FENCES` in its
//!   request set), so a producer reads whether it may ask before it keeps several writes in
//!   flight that a refused one must hold back.

use std::collections::HashMap;

#[cfg(clean_islands)]
#[path = "sticky_fence_island.rs"]
mod sticky_fence_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{sticky_fence_min_seq, sticky_fence_seq_allowed};
#[cfg(clean_islands)]
pub use sticky_fence_island::{sticky_fence_min_seq, sticky_fence_seq_allowed};

/// Three-parameter sticky-fence admission kernel matching `sticky_fence_admits_code_isl`
/// in `sticky_fence_island.rs`, composed over the Clean-origin [`sticky_fence_seq_allowed`].
#[must_use]
pub const fn sticky_fence_admits_code(fenced: u64, fence_seq: u64, req_seq: u64) -> u64 {
    if 0 < fenced {
        sticky_fence_seq_allowed(fence_seq, req_seq)
    } else {
        1
    }
}

/// Maximum number of concurrent `(conn_id, producer_id)` gap fences tracked in memory.
pub const MAX_STICKY_FENCES: usize = 4096;

/// Prefix of the refusal reason emitted when a pipelined write is rejected by an active
/// sticky gap fence (`"gap-fenced=<seq>: ..."`).
pub const GAP_FENCED_PREFIX: &str = "gap-fenced=";

contract_fn! {
    /// Kernel-certified sticky-fence table capacity guard (`len <= max_entries`).
    #[must_use]
    pub const fn sticky_fence_table_within_cap(len: u64, max_entries: u64) -> bool
    clauses [ensures result == (len <= max_entries)]
    {
        len <= max_entries
    }
}

/// Pure admission predicate backed by the Clean-origin [`sticky_fence_admits_code`] kernel.
#[must_use]
pub const fn sticky_fence_admits(fence_seq: Option<u64>, req_seq: u64) -> bool {
    match fence_seq {
        None => sticky_fence_admits_code(0, 0, req_seq) == 1,
        Some(f) => sticky_fence_admits_code(1, f, req_seq) == 1,
    }
}

/// Format the canonical `ERR_REFUSED` message for a request blocked by `fence_seq`.
#[must_use]
pub fn format_gap_fenced_msg(fence_seq: u64, req_seq: u64) -> String {
    format!(
        "{GAP_FENCED_PREFIX}{fence_seq}: prior pipelined write failed before sequence {req_seq}; resend from {fence_seq}"
    )
}

/// Parse the fenced `producer_seq` out of a broker refusal message formatted by
/// [`format_gap_fenced_msg`], returning `None` if `msg` is not a gap-fenced refusal.
#[must_use]
pub const fn parse_gap_fenced_seq(msg: &str) -> Option<u64> {
    let mut rest = msg.as_bytes();
    let mut pfx = GAP_FENCED_PREFIX.as_bytes();
    if rest.len() <= pfx.len() {
        return None;
    }
    while let &[pb, ref ptail @ ..] = pfx {
        let &[rb, ref rtail @ ..] = rest else {
            return None;
        };
        if rb != pb {
            return None;
        }
        pfx = ptail;
        rest = rtail;
    }
    let mut acc = 0u64;
    let mut has_digit = false;
    while let &[b, ref tail @ ..] = rest {
        if matches!(b, b'0'..=b'9') {
            let d = b.saturating_sub(b'0') as u64;
            let Some(mul) = acc.checked_mul(10) else {
                return None;
            };
            let Some(next) = mul.checked_add(d) else {
                return None;
            };
            acc = next;
            has_digit = true;
            rest = tail;
        } else if b == b':' || b == b' ' {
            break;
        } else {
            return None;
        }
    }
    if has_digit {
        Some(acc)
    } else {
        None
    }
}

/// Bounded `(conn_id, producer_id) -> fence_seq` table owned by the broker writer path.
#[derive(Debug, Clone, Default)]
pub struct StickyFenceTable {
    entries: HashMap<(u64, u64), u64>,
    overflow_fenced_conns: Vec<u64>,
}

impl StickyFenceTable {
    /// Construct an empty [`StickyFenceTable`].
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of active `(conn_id, producer_id)` fences.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether zero fences are active.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.overflow_fenced_conns.is_empty()
    }

    fn is_overflow_fenced(&self, conn_id: u64) -> bool {
        let mut i = 0usize;
        while i < self.overflow_fenced_conns.len() {
            if self.overflow_fenced_conns[i] == conn_id {
                return true;
            }
            i += 1;
        }
        false
    }

    /// Check whether `(conn_id, producer_id, req_seq)` may proceed, returning
    /// `Err(fence_seq)` when blocked by an active gap fence.
    pub fn check(&self, conn_id: u64, producer_id: u64, req_seq: u64) -> Result<(), u64> {
        if self.is_overflow_fenced(conn_id) {
            if !sticky_fence_admits(Some(0), req_seq) {
                return Err(0);
            }
        }
        let fence = match self.entries.get(&(conn_id, producer_id)) {
            Some(&f) => Some(f),
            None => None,
        };
        if sticky_fence_admits(fence, req_seq) {
            Ok(())
        } else {
            Err(fence.unwrap_or(0))
        }
    }

    /// Latch or tighten a gap fence at `failed_seq` for `(conn_id, producer_id)`.
    pub fn record_refusal(&mut self, conn_id: u64, producer_id: u64, failed_seq: u64) {
        if let Some(existing) = self.entries.get_mut(&(conn_id, producer_id)) {
            *existing = sticky_fence_min_seq(*existing, failed_seq);
            return;
        }
        let next_len = (self.entries.len() as u64).saturating_add(1);
        if sticky_fence_table_within_cap(next_len, MAX_STICKY_FENCES as u64) {
            self.entries.insert((conn_id, producer_id), failed_seq);
        } else if !self.is_overflow_fenced(conn_id)
            && self.overflow_fenced_conns.len() < MAX_STICKY_FENCES
        {
            // Fail closed even if a single connection exhausted MAX_STICKY_FENCES distinct producer_ids.
            self.overflow_fenced_conns.push(conn_id);
        }
    }

    /// Clear an active gap fence when a retry at `committed_seq <= fence_seq` commits.
    pub fn record_commit(&mut self, conn_id: u64, producer_id: u64, committed_seq: u64) {
        let should_clear = match self.entries.get(&(conn_id, producer_id)) {
            Some(&fence_seq) => committed_seq <= fence_seq,
            None => false,
        };
        if should_clear {
            self.entries.remove(&(conn_id, producer_id));
        }
    }

    /// Remove all fences associated with `conn_id` when that connection closes.
    pub fn drop_conn(&mut self, conn_id: u64) {
        let mut to_remove: Vec<(u64, u64)> = Vec::new();
        for &(cid, pid) in self.entries.keys() {
            if cid == conn_id {
                to_remove.push((cid, pid));
            }
        }
        while let Some(key) = to_remove.pop() {
            self.entries.remove(&key);
        }
        let mut kept: Vec<u64> = Vec::new();
        while let Some(cid) = self.overflow_fenced_conns.pop() {
            if cid != conn_id {
                kept.push(cid);
            }
        }
        self.overflow_fenced_conns = kept;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sticky_fence_blocks_pipelined_successors_until_retry_commits() {
        let mut table = StickyFenceTable::new();
        assert_eq!(table.check(1, 42, 10), Ok(()));

        // Batch 1 fails seq=10; pipelined seq=11 and seq=12 must be rejected!
        table.record_refusal(1, 42, 10);
        assert_eq!(table.check(1, 42, 11), Err(10));
        assert_eq!(table.check(1, 42, 12), Err(10));
        // Other producers on the same connection or same producer on another connection are unaffected.
        assert_eq!(table.check(1, 99, 11), Ok(()));
        assert_eq!(table.check(2, 42, 11), Ok(()));

        let msg = format_gap_fenced_msg(10, 11);
        assert_eq!(parse_gap_fenced_seq(&msg), Some(10));

        // Retry of seq=10 is admitted and clears the fence upon commit!
        assert_eq!(table.check(1, 42, 10), Ok(()));
        table.record_commit(1, 42, 10);
        assert_eq!(table.check(1, 42, 11), Ok(()));
        assert_eq!(table.check(1, 42, 12), Ok(()));
    }

    #[test]
    fn sticky_fence_tightens_to_minimum_and_drops_on_disconnect() {
        let mut table = StickyFenceTable::new();
        table.record_refusal(7, 100, 25);
        table.record_refusal(7, 100, 20);
        assert_eq!(table.check(7, 100, 21), Err(20));
        assert_eq!(table.check(7, 100, 20), Ok(()));

        table.drop_conn(7);
        assert!(table.is_empty());
        assert_eq!(table.check(7, 100, 25), Ok(()));
    }
}
