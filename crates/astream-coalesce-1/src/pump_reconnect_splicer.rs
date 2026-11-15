// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Lineage-aware `aspump` reconnect & unquorumed-tail replay splicer (`astream-pump`).
//!
//! When `aspump` reconnects to a broker (or fails over to a newly promoted replica leader),
//! [`PumpReconnectSplicer`] compares the broker's reported `(LogIdentity, Lineage)` via
//! [`LogIdentity::continues`] against the pump's last acknowledged offset and bounded
//! in-flight ring:
//!
//! - **Same identity & generation:** resumes seamlessly from `acked_head` with zero replay.
//! - **Promoted generation continuing through `common_head`:** rewinds the outbound replay
//!   cursor to `min(common_head, acked_head)` via Clean-origin [`splice_cursor_clamp`] so
//!   any unquorumed tail frames truncated during failover are re-published with their
//!   original monotone `producer_seq` (idempotently deduped if already present!).
//! - **Disjoint log identity:** resets offset watermarks to `0` while keeping `producer_seq`
//!   monotone via [`splice_prod_seq_advance`].
//! - Zero closures (`0 mandated`), backed by Clean TLA+ island `Astream.Pump.TlaReconnectSplicer`.

use astream_wire::{Lineage, LogIdentity};

#[cfg(clean_islands)]
#[path = "pump_reconnect_splicer_island.rs"]
mod pump_reconnect_splicer_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn splice_cursor_clamp(common_head: u64, acked_head: u64) -> u64 {
    if common_head < acked_head {
        common_head
    } else {
        acked_head
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn splice_prod_seq_advance(cur_seq: u64, proposed_seq: u64) -> u64 {
    if cur_seq < proposed_seq {
        proposed_seq
    } else {
        cur_seq
    }
}
#[cfg(clean_islands)]
pub use pump_reconnect_splicer_island::{splice_cursor_clamp, splice_prod_seq_advance};

contract_fn! {
    /// Kernel-certified check that a failover `common_head` truncated acked/staged
    /// records below `acked_head` (`common_head < acked_head`), linked via
    /// `clean-kernel-defeq` to `splice_needs_rewind_isl`.
    #[must_use]
    pub const fn splice_needs_rewind(common_head: u64, acked_head: u64) -> bool
    clauses [ensures result == (common_head < acked_head)]
    {
        common_head < acked_head
    }
}

/// Decision computed when `aspump` attaches to a reconnected broker session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReconnectSplicePlan {
    /// First connection or identical `(id, generation)`: continue from `acked_head`.
    Seamless {
        resume_offset: u64,
        next_prod_seq: u64,
    },
    /// Failover within the same lineage: rewind to `replay_from_offset <= acked_head`
    /// and re-send any buffered outbound records whose assigned offset was `>= replay_from_offset`.
    RewindToCommon {
        replay_from_offset: u64,
        dropped_tail_records: u64,
        next_prod_seq: u64,
    },
    /// Disjoint new log identity: subscriber cursor resets to `0`, outbound `next_prod_seq`
    /// advances monotonically without reusing prior sequence numbers.
    FreshLog { next_prod_seq: u64 },
}

/// Buffered outbound frame retained until durable/lineage confirmation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplicerRetainedFrame {
    /// Monotone producer sequence number (`>= 1`).
    pub prod_seq: u64,
    /// Offset assigned by the previous leader (`u64::MAX` if never acked before disconnect).
    pub assigned_offset: u64,
    /// Encoded terminal record payload.
    pub payload: Vec<u8>,
}

/// Stateful lineage-aware reconnect splicer for `aspump`.
#[derive(Debug, Clone)]
pub struct PumpReconnectSplicer {
    known_identity: Option<LogIdentity>,
    acked_head: u64,
    replay_cursor: u64,
    prev_prod_seq: u64,
    next_prod_seq: u64,
    max_retained: usize,
    retained: Vec<SplicerRetainedFrame>,
}

impl PumpReconnectSplicer {
    /// Construct a [`PumpReconnectSplicer`] starting at `producer_seq = 1`.
    #[must_use]
    pub const fn new(max_retained: usize) -> Self {
        let cap = if max_retained == 0 { 1 } else { max_retained };
        Self {
            known_identity: None,
            acked_head: 0,
            replay_cursor: 0,
            prev_prod_seq: 1,
            next_prod_seq: 1,
            max_retained: cap,
            retained: Vec::new(),
        }
    }

    /// Next monotone producer sequence number (`>= 1`).
    #[must_use]
    pub const fn next_prod_seq(&self) -> u64 {
        self.next_prod_seq
    }

    /// Previous producer sequence number prior to the latest `stage_outbound` call.
    #[must_use]
    pub const fn prev_prod_seq(&self) -> u64 {
        self.prev_prod_seq
    }

    /// Current outbound replay offset cursor (`<= acked_head`).
    #[must_use]
    pub const fn replay_cursor(&self) -> u64 {
        self.replay_cursor
    }

    /// Last acknowledged broker offset under `known_identity`.
    #[must_use]
    pub const fn acked_head(&self) -> u64 {
        self.acked_head
    }

    /// Allocate the next monotone `prod_seq` and stage `payload` into the bounded retain ring.
    pub fn stage_outbound(&mut self, payload: Vec<u8>) -> u64 {
        let seq = self.next_prod_seq;
        self.prev_prod_seq = seq;
        self.next_prod_seq = splice_prod_seq_advance(seq, seq.saturating_add(1));
        if self.retained.len() >= self.max_retained && !self.retained.is_empty() {
            let mut next_vec = Vec::new();
            let mut skipped_first = false;
            for item in core::mem::take(&mut self.retained) {
                if !skipped_first {
                    skipped_first = true;
                } else {
                    next_vec.push(item);
                }
            }
            self.retained = next_vec;
        }
        self.retained.push(SplicerRetainedFrame {
            prod_seq: seq,
            assigned_offset: u64::MAX,
            payload,
        });
        seq
    }

    /// Record broker publish acknowledgment `(prod_seq, offset)` and optional durable floor
    /// (pruning retained frames strictly below `durable_floor`).
    pub fn record_ack(&mut self, prod_seq: u64, offset: u64, durable_floor: u64) {
        let next_head = offset.saturating_add(1);
        if next_head > self.acked_head {
            self.acked_head = next_head;
            self.replay_cursor = splice_cursor_clamp(self.acked_head, self.acked_head);
        }
        let mut cur = self.retained.as_mut_slice();
        while let [frame, rest @ ..] = cur {
            if frame.prod_seq == prod_seq {
                frame.assigned_offset = offset;
                break;
            }
            cur = rest;
        }
        let mut filtered = Vec::new();
        for frame in core::mem::take(&mut self.retained) {
            let off = frame.assigned_offset;
            if !(off != u64::MAX && off < durable_floor) {
                filtered.push(frame);
            }
        }
        self.retained = filtered;
    }

    /// Reconcile against a newly connected broker's `(server_id, server_lineage)` and return
    /// both the [`ReconnectSplicePlan`] and the ordered list of retained frames to re-send.
    pub fn reconcile_reconnect(
        &mut self,
        server_id: LogIdentity,
        server_lineage: &Lineage,
    ) -> (ReconnectSplicePlan, Vec<SplicerRetainedFrame>) {
        let Some(prev_id) = self.known_identity else {
            self.known_identity = Some(server_id);
            let resend = self.collect_resend_from(0);
            return (
                ReconnectSplicePlan::Seamless {
                    resume_offset: self.acked_head,
                    next_prod_seq: self.next_prod_seq,
                },
                resend,
            );
        };

        if prev_id == server_id {
            let resend = self.collect_resend_from(self.acked_head);
            return (
                ReconnectSplicePlan::Seamless {
                    resume_offset: self.acked_head,
                    next_prod_seq: self.next_prod_seq,
                },
                resend,
            );
        }

        if let Some(common_head) = server_id.continues(prev_id, server_lineage) {
            self.known_identity = Some(server_id);
            let clamped = splice_cursor_clamp(common_head, self.acked_head);
            let dropped = if splice_needs_rewind(common_head, self.acked_head) {
                self.acked_head.saturating_sub(clamped)
            } else {
                0
            };
            self.replay_cursor = clamped;
            self.acked_head = clamped;
            let resend = self.collect_resend_from(clamped);
            return (
                ReconnectSplicePlan::RewindToCommon {
                    replay_from_offset: clamped,
                    dropped_tail_records: dropped,
                    next_prod_seq: self.next_prod_seq,
                },
                resend,
            );
        }

        // Disjoint log: reset offset watermarks, re-send all unpruned retained frames.
        self.known_identity = Some(server_id);
        self.acked_head = 0;
        self.replay_cursor = 0;
        let resend = self.collect_resend_from(0);
        (
            ReconnectSplicePlan::FreshLog {
                next_prod_seq: self.next_prod_seq,
            },
            resend,
        )
    }

    fn collect_resend_from(&mut self, cutoff_offset: u64) -> Vec<SplicerRetainedFrame> {
        let mut out = Vec::new();
        for frame in &mut self.retained {
            if frame.assigned_offset >= cutoff_offset {
                frame.assigned_offset = u64::MAX;
                out.push(frame.clone());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splicer_rewinds_and_replays_only_unquorumed_tail_frames_across_leader_failover() {
        let mut sp = PumpReconnectSplicer::new(16);
        let gen0 = LogIdentity {
            id: [0x11; 16],
            generation: 0,
        };
        let empty_lin = Lineage::default();
        let _ = sp.reconcile_reconnect(gen0, &empty_lin);

        let s1 = sp.stage_outbound(b"out-0".to_vec());
        let s2 = sp.stage_outbound(b"out-1".to_vec());
        let s3 = sp.stage_outbound(b"out-2-unquorumed".to_vec());
        sp.record_ack(s1, 10, 0);
        sp.record_ack(s2, 11, 0);
        sp.record_ack(s3, 12, 10); // offset 12 acked locally before crash, common_head = 12!

        let gen1 = LogIdentity {
            id: [0x11; 16],
            generation: 1,
        };
        let lin1 = Lineage::from_steps(&[(1, 12)]).unwrap();
        let (plan, resend) = sp.reconcile_reconnect(gen1, &lin1);
        assert_eq!(
            plan,
            ReconnectSplicePlan::RewindToCommon {
                replay_from_offset: 12,
                dropped_tail_records: 1,
                next_prod_seq: 4,
            }
        );
        assert_eq!(resend.len(), 1);
        assert_eq!(resend[0].prod_seq, 3);
        assert_eq!(resend[0].payload, b"out-2-unquorumed");
    }
}
