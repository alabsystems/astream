// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WAN / TCP Keepalive Probe Scheduler & Half-Open Connection Deadline Budget.
//!
//! Over Wi-Fi roam, laptop sleep/wake, or stateful NAT gateways, `astream-broker` TCP clients
//! (`Client::keepalive_if_idle` / `KEEPALIVE_DEADLINE`) must emit periodic keepalive probes at
//! `ping_interval_ms <= deadline_ms / 3` and reap peers whose idle silence reaches
//! `deadline_ms` (`keepalive_peer_expired`) or `max_missed_pings`.
//!
//! Includes a slice-destructured 24-byte `"AKP1"` wire frame (`0` runtime bounds checks) and
//! Clean TLA+ Island `Astream.Wire.TlaKeepaliveDeadline` (`keepalive_probe_budget_island.rs`),
//! proving `pingIntervalMs <= deadlineMs` and `unansweredPings <= maxMissedPings`.

#[cfg(clean_islands)]
#[path = "keepalive_probe_budget_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{keepalive_interval_clamp, keepalive_missed_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn keepalive_interval_clamp(interval_ms: u64, deadline_ms: u64) -> u64 {
    if interval_ms < deadline_ms {
        interval_ms
    } else {
        deadline_ms
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn keepalive_missed_clamp(missed: u64, max_missed: u64) -> u64 {
    if missed < max_missed {
        missed
    } else {
        max_missed
    }
}

contract_fn! {
    /// Kernel-certified check whether peer silence `idle_ms` has reached `deadline_ms`.
    #[must_use]
    #[inline]
    pub const fn keepalive_peer_expired(idle_ms: u64, deadline_ms: u64) -> bool
    clauses [ensures result == (deadline_ms <= idle_ms)]
    {
        deadline_ms <= idle_ms
    }
}

/// Wire magic for 24-byte `"AKP1"` keepalive telemetry frames.
pub const KEEPALIVE_WIRE_MAGIC: [u8; 4] = *b"AKP1";

/// Fixed wire size of an `"AKP1"` keepalive frame (`4 + 4 + 8 + 8 = 24` bytes).
pub const KEEPALIVE_WIRE_LEN: usize = 24;

/// Default peer silence deadline (`15_000 ms`).
pub const DEFAULT_KEEPALIVE_DEADLINE_MS: u64 = 15_000;

/// Default maximum unanswered keepalive pings before declaring peer half-open (`3`).
pub const DEFAULT_MAX_MISSED_PINGS: u64 = 3;

/// Decision produced by `KeepaliveBudgetTracker::poll_at`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum KeepaliveAction {
    /// Connection is active and within budget; sleep for `next_wake_ms`.
    Healthy { next_wake_ms: u64 },
    /// Emit an outbound keepalive probe now.
    SendPing {
        ping_seq: u64,
        unanswered_pings: u64,
    },
    /// Peer exceeded `deadline_ms` or `max_missed_pings`; close socket and fire Last Will.
    PeerExpired { idle_ms: u64, unanswered_pings: u64 },
}

/// Stateful WAN keepalive scheduler certified by `TlaKeepaliveDeadline`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KeepaliveBudgetTracker {
    ping_interval_ms: u64,
    deadline_ms: u64,
    unanswered_pings: u64,
    max_missed_pings: u64,
    ping_seq: u64,
    last_rx_ms: u64,
    last_tx_ms: u64,
}

impl KeepaliveBudgetTracker {
    #[inline]
    pub const fn new(
        requested_interval_ms: u64,
        deadline_ms: u64,
        max_missed_pings: u64,
        now_ms: u64,
    ) -> Self {
        let dl = if deadline_ms < 300 { 300 } else { deadline_ms };
        let mm = if max_missed_pings == 0 {
            1
        } else {
            max_missed_pings
        };
        let raw_int = if requested_interval_ms == 0 {
            dl / 3
        } else {
            requested_interval_ms
        };
        let interval = keepalive_interval_clamp(raw_int, dl);
        Self {
            ping_interval_ms: interval,
            deadline_ms: dl,
            unanswered_pings: 0,
            max_missed_pings: mm,
            ping_seq: 0,
            last_rx_ms: now_ms,
            last_tx_ms: now_ms,
        }
    }

    #[inline]
    pub const fn ping_interval_ms(&self) -> u64 {
        self.ping_interval_ms
    }

    #[inline]
    pub const fn deadline_ms(&self) -> u64 {
        self.deadline_ms
    }

    #[inline]
    pub const fn unanswered_pings(&self) -> u64 {
        self.unanswered_pings
    }

    /// Records inbound traffic or pong from peer at `now_ms`, resetting unanswered count.
    #[inline]
    pub fn note_inbound(&mut self, now_ms: u64) {
        if now_ms > self.last_rx_ms {
            self.last_rx_ms = now_ms;
        }
        self.unanswered_pings = 0;
    }

    /// Records outbound application frame at `now_ms`, deferring unnecessary keepalive pings.
    #[inline]
    pub fn note_outbound(&mut self, now_ms: u64) {
        if now_ms > self.last_tx_ms {
            self.last_tx_ms = now_ms;
        }
    }

    /// Evaluates keepalive state at `now_ms`.
    pub fn poll_at(&mut self, now_ms: u64) -> KeepaliveAction {
        let rx_idle = now_ms.saturating_sub(self.last_rx_ms);
        if keepalive_peer_expired(rx_idle, self.deadline_ms) {
            return KeepaliveAction::PeerExpired {
                idle_ms: rx_idle,
                unanswered_pings: self.unanswered_pings,
            };
        }

        let tx_idle = now_ms.saturating_sub(self.last_tx_ms);
        if tx_idle >= self.ping_interval_ms {
            if self.unanswered_pings >= self.max_missed_pings {
                return KeepaliveAction::PeerExpired {
                    idle_ms: rx_idle,
                    unanswered_pings: self.unanswered_pings,
                };
            }
            let next_missed = self.unanswered_pings.saturating_add(1);
            self.unanswered_pings = keepalive_missed_clamp(next_missed, self.max_missed_pings);
            self.ping_seq = self.ping_seq.saturating_add(1);
            self.last_tx_ms = now_ms;
            return KeepaliveAction::SendPing {
                ping_seq: self.ping_seq,
                unanswered_pings: self.unanswered_pings,
            };
        }

        let until_ping = self.ping_interval_ms.saturating_sub(tx_idle);
        let until_expire = self.deadline_ms.saturating_sub(rx_idle);
        let next_wake_ms = if until_ping < until_expire {
            until_ping
        } else {
            until_expire
        };
        KeepaliveAction::Healthy { next_wake_ms }
    }

    /// Encodes a 24-byte `"AKP1"` keepalive frame (`magic[4] + missed_u32_le[4] + seq_u64_le[8] + tx_ms_u64_le[8]`).
    #[must_use]
    pub const fn encode_frame(&self) -> [u8; KEEPALIVE_WIRE_LEN] {
        let [m0, m1, m2, m3] = KEEPALIVE_WIRE_MAGIC;
        let u = self.unanswered_pings as u32;
        let s = self.ping_seq;
        let t = self.last_tx_ms;
        [
            m0,
            m1,
            m2,
            m3,
            (u & 0xff) as u8,
            ((u >> 8) & 0xff) as u8,
            ((u >> 16) & 0xff) as u8,
            ((u >> 24) & 0xff) as u8,
            (s & 0xff) as u8,
            ((s >> 8) & 0xff) as u8,
            ((s >> 16) & 0xff) as u8,
            ((s >> 24) & 0xff) as u8,
            ((s >> 32) & 0xff) as u8,
            ((s >> 40) & 0xff) as u8,
            ((s >> 48) & 0xff) as u8,
            ((s >> 56) & 0xff) as u8,
            (t & 0xff) as u8,
            ((t >> 8) & 0xff) as u8,
            ((t >> 16) & 0xff) as u8,
            ((t >> 24) & 0xff) as u8,
            ((t >> 32) & 0xff) as u8,
            ((t >> 40) & 0xff) as u8,
            ((t >> 48) & 0xff) as u8,
            ((t >> 56) & 0xff) as u8,
        ]
    }
}

/// Decodes `(unanswered_pings, ping_seq, sent_ms)` from a slice using total slice-pattern
/// destructuring (`0` runtime bounds checks).
#[must_use]
pub const fn decode_keepalive_frame(raw: &[u8]) -> Option<(u32, u64, u64)> {
    let [b'A', b'K', b'P', b'1', u0, u1, u2, u3, s0, s1, s2, s3, s4, s5, s6, s7, t0, t1, t2, t3, t4, t5, t6, t7] =
        *raw
    else {
        return None;
    };
    let missed = (u0 as u32) | ((u1 as u32) << 8) | ((u2 as u32) << 16) | ((u3 as u32) << 24);
    let seq = (s0 as u64)
        | ((s1 as u64) << 8)
        | ((s2 as u64) << 16)
        | ((s3 as u64) << 24)
        | ((s4 as u64) << 32)
        | ((s5 as u64) << 40)
        | ((s6 as u64) << 48)
        | ((s7 as u64) << 56);
    let sent_ms = (t0 as u64)
        | ((t1 as u64) << 8)
        | ((t2 as u64) << 16)
        | ((t3 as u64) << 24)
        | ((t4 as u64) << 32)
        | ((t5 as u64) << 40)
        | ((t6 as u64) << 48)
        | ((t7 as u64) << 56);
    Some((missed, seq, sent_ms))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schedules_pings_encodes_wire_frame_and_expires_half_open_peer() {
        let mut kt = KeepaliveBudgetTracker::new(5_000, 15_000, 2, 1_000);
        assert_eq!(
            kt.poll_at(3_000),
            KeepaliveAction::Healthy {
                next_wake_ms: 3_000
            }
        );
        assert_eq!(
            kt.poll_at(6_000),
            KeepaliveAction::SendPing {
                ping_seq: 1,
                unanswered_pings: 1,
            }
        );

        let wire = kt.encode_frame();
        assert_eq!(decode_keepalive_frame(&wire), Some((1, 1, 6_000)));
        assert_eq!(decode_keepalive_frame(&wire[..10]), None);

        // Peer replies at 7_000 -> resets unanswered_pings!
        kt.note_inbound(7_000);
        assert_eq!(kt.unanswered_pings(), 0);

        // Now peer vanishes completely: pings at 11_000 and 16_000, then expires at 22_000!
        assert_eq!(
            kt.poll_at(11_000),
            KeepaliveAction::SendPing {
                ping_seq: 2,
                unanswered_pings: 1,
            }
        );
        assert_eq!(
            kt.poll_at(16_000),
            KeepaliveAction::SendPing {
                ping_seq: 3,
                unanswered_pings: 2,
            }
        );
        assert_eq!(
            kt.poll_at(21_000),
            KeepaliveAction::PeerExpired {
                idle_ms: 14_000,
                unanswered_pings: 2,
            }
        );
    }
}
