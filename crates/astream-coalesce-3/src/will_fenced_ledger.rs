// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Producer-Sequence-Fenced Last Will Ledger.
//!
//! When an `aterm` daemon, worker, or fabric bridge registers a `Will` on an `asb` connection,
//! the broker appends that record if the connection closes without an explicit drop — EXCEPT
//! when fenced by any later record `(producer_id, later_seq)` from the same producer
//! (`will_seq <= latest_producer_seq`), e.g., when a reconnecting worker publishes a fresh
//! heartbeat on a new connection before its old half-open TCP socket times out.
//!
//! Backed by Clean TLA+ Island `Astream.Broker.TlaWillFenceLedger`
//! (`will_fenced_ledger_island.rs`), proving `activeWills <= maxConns` and
//! `fencedSeq <= highestProducerSeq`.

#[cfg(clean_islands)]
#[path = "will_fenced_ledger_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{will_active_clamp, will_seq_advance};

#[cfg(not(clean_islands))]
#[inline]
pub const fn will_active_clamp(active_wills: u64, max_conns: u64) -> u64 {
    if active_wills < max_conns {
        active_wills
    } else {
        max_conns
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn will_seq_advance(cur_seq: u64, observed_seq: u64) -> u64 {
    if cur_seq < observed_seq {
        observed_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// Kernel-certified check that a registered will at `will_seq` has been fenced by
    /// `latest_producer_seq` (`will_seq <= latest_producer_seq`).
    #[must_use]
    #[inline]
    pub const fn will_is_fenced_by_seq(will_seq: u64, latest_producer_seq: u64) -> bool
    clauses [ensures result == (will_seq <= latest_producer_seq)]
    {
        will_seq <= latest_producer_seq
    }
}

/// Inline connection-slot capacity for zero-allocation `WillFenceLedger`.
pub const MAX_WILL_LEDGER_SLOTS: usize = 64;

/// Registered connection-scoped Last Will descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PendingWillEntry {
    pub conn_id: u64,
    pub producer_id: u64,
    pub will_seq: u64,
    pub subject_hash: u64,
    pub active: bool,
}

impl PendingWillEntry {
    const EMPTY: Self = Self {
        conn_id: 0,
        producer_id: 0,
        will_seq: 0,
        subject_hash: 0,
        active: false,
    };
}

/// Per-producer monotone sequence watermark entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProducerWatermark {
    producer_id: u64,
    highest_seq: u64,
    occupied: bool,
}

impl ProducerWatermark {
    const EMPTY: Self = Self {
        producer_id: 0,
        highest_seq: 0,
        occupied: false,
    };
}

/// Outcome when a connection closes and its registered Last Will is evaluated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisconnectWillOutcome {
    /// Connection had no active Last Will registered.
    NoWillRegistered,
    /// Registered will was fenced by a newer or equal producer sequence (`will_seq <= highest_seq`).
    SuppressedByProducerFence {
        producer_id: u64,
        will_seq: u64,
        highest_seq: u64,
    },
    /// Registered will is unfenced and must be appended to the log (updating producer watermark).
    FireWill {
        producer_id: u64,
        will_seq: u64,
        subject_hash: u64,
    },
}

/// Bounded, TLA+-certified Last Will fencing ledger.
#[derive(Debug, Clone)]
pub struct WillFenceLedger {
    max_conns: u64,
    active_wills: u64,
    wills: [PendingWillEntry; MAX_WILL_LEDGER_SLOTS],
    watermarks: [ProducerWatermark; MAX_WILL_LEDGER_SLOTS],
}

impl WillFenceLedger {
    #[inline]
    pub const fn new(max_conns: usize) -> Self {
        let cap = if max_conns == 0 || max_conns > MAX_WILL_LEDGER_SLOTS {
            MAX_WILL_LEDGER_SLOTS as u64
        } else {
            max_conns as u64
        };
        Self {
            max_conns: cap,
            active_wills: 0,
            wills: [PendingWillEntry::EMPTY; MAX_WILL_LEDGER_SLOTS],
            watermarks: [ProducerWatermark::EMPTY; MAX_WILL_LEDGER_SLOTS],
        }
    }

    #[inline]
    pub const fn active_wills(&self) -> u64 {
        self.active_wills
    }

    #[inline]
    pub const fn max_conns(&self) -> u64 {
        self.max_conns
    }

    /// Looks up the highest committed `producer_seq` observed for `producer_id`.
    pub fn highest_seq_for(&self, producer_id: u64) -> Option<u64> {
        let mut cur: &[ProducerWatermark] = &self.watermarks;
        while let &[wm, ref rest @ ..] = cur {
            if wm.occupied && wm.producer_id == producer_id {
                return Some(wm.highest_seq);
            }
            cur = rest;
        }
        None
    }

    /// Advances the monotone sequence watermark for `producer_id` when a normal publish or
    /// previous will commits.
    pub fn observe_producer_publish(&mut self, producer_id: u64, seq: u64) -> bool {
        let mut free_slot: Option<usize> = None;
        let mut i = 0usize;
        let mut cur = self.watermarks.as_mut_slice();
        while let [wm, rest @ ..] = cur {
            if wm.occupied && wm.producer_id == producer_id {
                wm.highest_seq = will_seq_advance(wm.highest_seq, seq);
                return true;
            }
            if !wm.occupied && free_slot.is_none() {
                free_slot = Some(i);
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        if let Some(slot_idx) = free_slot {
            if let Some(slot) = self.watermarks.get_mut(slot_idx) {
                *slot = ProducerWatermark {
                    producer_id,
                    highest_seq: seq,
                    occupied: true,
                };
                return true;
            }
        }
        false
    }

    /// Registers or replaces the connection's Last Will if not already fenced and within `max_conns`.
    pub fn register_will(
        &mut self,
        conn_id: u64,
        producer_id: u64,
        will_seq: u64,
        subject_hash: u64,
    ) -> Result<(), &'static str> {
        if let Some(high) = self.highest_seq_for(producer_id) {
            if will_is_fenced_by_seq(will_seq, high) {
                return Err("will sequence already fenced by committed producer record");
            }
        }
        let mut free_slot: Option<usize> = None;
        let mut i = 0usize;
        let mut cur = self.wills.as_mut_slice();
        while let [w, rest @ ..] = cur {
            if w.active && w.conn_id == conn_id {
                *w = PendingWillEntry {
                    conn_id,
                    producer_id,
                    will_seq,
                    subject_hash,
                    active: true,
                };
                return Ok(());
            }
            if !w.active && free_slot.is_none() {
                free_slot = Some(i);
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        if self.active_wills >= self.max_conns {
            return Err("active will capacity exhausted");
        }
        let Some(slot_idx) = free_slot else {
            return Err("active will slot table full");
        };
        let Some(slot) = self.wills.get_mut(slot_idx) else {
            return Err("active will slot table full");
        };
        *slot = PendingWillEntry {
            conn_id,
            producer_id,
            will_seq,
            subject_hash,
            active: true,
        };
        self.active_wills = will_active_clamp(self.active_wills.saturating_add(1), self.max_conns);
        Ok(())
    }

    /// Explicitly drops a connection's Last Will on graceful detach (`WillDrop`).
    pub fn cancel_will(&mut self, conn_id: u64) -> bool {
        let mut cur = self.wills.as_mut_slice();
        while let [w, rest @ ..] = cur {
            if w.active && w.conn_id == conn_id {
                *w = PendingWillEntry::EMPTY;
                self.active_wills = self.active_wills.saturating_sub(1);
                return true;
            }
            cur = rest;
        }
        false
    }

    /// Evaluates and removes a connection's Last Will upon abrupt disconnect.
    pub fn on_disconnect(&mut self, conn_id: u64) -> DisconnectWillOutcome {
        let mut found: Option<PendingWillEntry> = None;
        let mut cur = self.wills.as_mut_slice();
        while let [w, rest @ ..] = cur {
            if w.active && w.conn_id == conn_id {
                found = Some(*w);
                *w = PendingWillEntry::EMPTY;
                self.active_wills = self.active_wills.saturating_sub(1);
                break;
            }
            cur = rest;
        }
        let Some(entry) = found else {
            return DisconnectWillOutcome::NoWillRegistered;
        };
        if let Some(high) = self.highest_seq_for(entry.producer_id) {
            if will_is_fenced_by_seq(entry.will_seq, high) {
                return DisconnectWillOutcome::SuppressedByProducerFence {
                    producer_id: entry.producer_id,
                    will_seq: entry.will_seq,
                    highest_seq: high,
                };
            }
        }
        let _ = self.observe_producer_publish(entry.producer_id, entry.will_seq);
        DisconnectWillOutcome::FireWill {
            producer_id: entry.producer_id,
            will_seq: entry.will_seq,
            subject_hash: entry.subject_hash,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reconnecting_producer_publish_fences_stale_connection_will() {
        let mut ledger = WillFenceLedger::new(8);
        assert!(ledger.observe_producer_publish(42, 10));
        // Registering seq 10 or lower is immediately rejected.
        assert!(ledger.register_will(1, 42, 10, 0xCAFE).is_err());

        // Conn 1 registers will at seq 11.
        assert!(ledger.register_will(1, 42, 11, 0xCAFE).is_ok());
        assert_eq!(ledger.active_wills(), 1);

        // Producer reconnects on Conn 2 and publishes seq 12 BEFORE Conn 1 times out!
        assert!(ledger.observe_producer_publish(42, 12));

        // When Conn 1 finally closes, its seq-11 will is suppressed!
        assert_eq!(
            ledger.on_disconnect(1),
            DisconnectWillOutcome::SuppressedByProducerFence {
                producer_id: 42,
                will_seq: 11,
                highest_seq: 12,
            }
        );
        assert_eq!(ledger.active_wills(), 0);
    }

    #[test]
    fn unfenced_will_fires_once_and_advances_producer_watermark() {
        let mut ledger = WillFenceLedger::new(4);
        assert!(ledger.register_will(9, 77, 1, 0xBEEF).is_ok());
        assert_eq!(
            ledger.on_disconnect(9),
            DisconnectWillOutcome::FireWill {
                producer_id: 77,
                will_seq: 1,
                subject_hash: 0xBEEF,
            }
        );
        assert_eq!(ledger.highest_seq_for(77), Some(1));
        assert_eq!(
            ledger.on_disconnect(9),
            DisconnectWillOutcome::NoWillRegistered
        );
    }
}
