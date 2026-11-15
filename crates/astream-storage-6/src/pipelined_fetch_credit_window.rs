// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pipelined WAN `Fetch` credit window scheduler (`Astream.Broker.TlaPipelinedFetchCreditWindow`).
//!
//! Eliminates single-RTT stop-and-wait stalls on high-RTT LAN/Internet `Fetch` streams while
//! bounding in-flight broker send buffers to `max_window_chunks`.

#[cfg(clean_islands)]
#[path = "pipelined_fetch_credit_window_island.rs"]
mod pipelined_fetch_credit_window_island;
#[cfg(clean_islands)]
pub use pipelined_fetch_credit_window_island::{fetch_grant_seq_advance, fetch_window_clamp};

#[cfg(not(clean_islands))]
/// Clamp in-flight pipelined `Fetch` chunk credits to `max_window`.
#[must_use]
pub const fn fetch_window_clamp(cand_credits: u64, max_window: u64) -> u64 {
    if cand_credits < max_window {
        cand_credits
    } else {
        max_window
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the pipelined `Fetch` credit grant sequence number.
#[must_use]
pub const fn fetch_grant_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `available_credits` allows shipping at least one more pipelined `Fetch` chunk.
    #[must_use]
    pub const fn fetch_has_credit(available_credits: u64) -> bool
    clauses [ensures result == (0 < available_credits)]
    {
        0 < available_credits
    }
}

/// Pipelined credit tracker for WAN `Fetch` / `Tail` streaming.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PipelinedFetchCreditWindow {
    max_window_chunks: u64,
    available_credits: u64,
    grant_seq: u64,
    shipped_chunks: u64,
}

impl PipelinedFetchCreditWindow {
    #[must_use]
    pub const fn new(max_window_chunks: u64) -> Self {
        let cap = if max_window_chunks == 0 {
            16
        } else {
            max_window_chunks
        };
        Self {
            max_window_chunks: cap,
            available_credits: 0,
            grant_seq: 0,
            shipped_chunks: 0,
        }
    }

    #[must_use]
    pub const fn available_credits(&self) -> u64 {
        self.available_credits
    }

    #[must_use]
    pub const fn grant_seq(&self) -> u64 {
        self.grant_seq
    }

    /// Apply a client credit top-up (`seq` must strictly advance `grant_seq` to prevent replay).
    pub fn apply_credit_grant(&mut self, seq: u64, add_chunks: u64) -> bool {
        if seq <= self.grant_seq {
            return false;
        }
        self.grant_seq = fetch_grant_seq_advance(self.grant_seq, seq);
        let cand = self.available_credits.saturating_add(add_chunks);
        self.available_credits = fetch_window_clamp(cand, self.max_window_chunks);
        true
    }

    /// Consume one chunk credit when shipping a pipelined `Fetch` batch.
    pub fn try_consume_chunk(&mut self) -> bool {
        if !fetch_has_credit(self.available_credits) {
            return false;
        }
        self.available_credits = self.available_credits.saturating_sub(1);
        self.shipped_chunks = self.shipped_chunks.saturating_add(1);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_window_cap_and_rejects_replayed_grant_seq() {
        let mut win = PipelinedFetchCreditWindow::new(4);
        assert!(win.apply_credit_grant(1, 10));
        assert_eq!(win.available_credits(), 4);
        assert!(!win.apply_credit_grant(1, 2));
        assert!(win.try_consume_chunk());
        assert_eq!(win.available_credits(), 3);
    }
}
