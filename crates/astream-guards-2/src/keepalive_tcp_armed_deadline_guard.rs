// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! TCP-only opt-in `Keepalive` deadline & guarded-attach authorization guard
//! (`evidence/manifest.toml` `broker.keepalive`;
//! `Astream.Broker.TlaKeepaliveTcpArmedDeadlineGuard`).
//!
//! Enforces the request/reply `Keepalive` liveness & backward-compatibility contract:
//! - On a guarded broker (`cap_required == true`), `Keepalive` before `grant_attached == true`
//!   is refused `ERR_UNAUTHORIZED` (whole reply, deadline NOT armed),
//! - A connection is held to `deadline_ms` ONLY when BOTH `is_tcp == true` (Unix-domain sockets
//!   never time out on keepalive!) AND `armed == true` (TCP peers that never sent `Keepalive`
//!   stay open indefinitely across idle stretches),
//! - Each read on an armed TCP connection re-arms `deadline_ms` monotonically, and silence
//!   at or past `deadline_ms` ends the connection once and fires its will!

#[cfg(clean_islands)]
#[path = "keepalive_tcp_armed_deadline_guard_island.rs"]
mod keepalive_tcp_armed_deadline_guard_island;
#[cfg(clean_islands)]
pub use keepalive_tcp_armed_deadline_guard_island::{
    keepalive_deadline_advance_b148, keepalive_interval_clamp_b148,
};

/// Default broker keepalive deadline (`60_000 ms`).
pub const DEFAULT_KEEPALIVE_DEADLINE_MS: u64 = 60_000;

/// Maximum configurable keepalive deadline (`86_400_000 ms` = 24 hours).
pub const MAX_KEEPALIVE_DEADLINE_MS: u64 = 86_400_000;

#[cfg(not(clean_islands))]
/// Clamp configured keepalive deadline interval to `max_interval_ms`.
#[must_use]
pub const fn keepalive_interval_clamp_b148(cand_interval_ms: u64, max_interval_ms: u64) -> u64 {
    if cand_interval_ms < max_interval_ms {
        cand_interval_ms
    } else {
        max_interval_ms
    }
}

#[cfg(not(clean_islands))]
/// Advance armed connection keepalive deadline monotonically on each read.
#[must_use]
pub const fn keepalive_deadline_advance_b148(cur_deadline_ms: u64, cand_deadline_ms: u64) -> u64 {
    if cur_deadline_ms < cand_deadline_ms {
        cand_deadline_ms
    } else {
        cur_deadline_ms
    }
}

contract_fn! {
    /// True iff the connection is TCP, keepalive-armed, not yet closed, and `now_ms >= deadline_ms`.
    #[must_use]
    pub const fn tcp_keepalive_expired_b148(
        is_tcp: bool,
        armed: bool,
        closed: bool,
        now_ms: u64,
        deadline_ms: u64,
    ) -> bool
    clauses [ensures result == (is_tcp && armed && !closed && now_ms >= deadline_ms)]
    {
        is_tcp && armed && !closed && now_ms >= deadline_ms
    }
}

/// Decision for `Request::Keepalive`, incoming reads, and deadline sweeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeepaliveGuardDecision {
    RefusedUnauthorizedBeforeAttach,
    AnsweredMarkUnixNeverEnforced,
    ArmedOrRearmedTcpDeadline { deadline_ms: u64 },
    ConnectionStillAlive,
    ClosedDeadTcpAndFireWillOnce { expired_at_ms: u64 },
    AlreadyClosed,
}

/// Per-connection keepalive state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeepaliveConnectionGuard {
    is_tcp: bool,
    cap_required: bool,
    grant_attached: bool,
    interval_ms: u64,
    armed: bool,
    deadline_ms: u64,
    closed: bool,
}

impl KeepaliveConnectionGuard {
    #[must_use]
    pub const fn new(is_tcp: bool, cap_required: bool, interval_ms: u64) -> Self {
        let clamped = keepalive_interval_clamp_b148(interval_ms, MAX_KEEPALIVE_DEADLINE_MS);
        Self {
            is_tcp,
            cap_required,
            grant_attached: !cap_required,
            interval_ms: if clamped == 0 { 1 } else { clamped },
            armed: false,
            deadline_ms: 0,
            closed: false,
        }
    }

    pub fn on_grant_attached(&mut self) {
        self.grant_attached = true;
    }

    /// Handle `Request::Keepalive` at `now_ms`.
    pub fn on_keepalive_request(&mut self, now_ms: u64) -> KeepaliveGuardDecision {
        if self.closed {
            return KeepaliveGuardDecision::AlreadyClosed;
        }
        if self.cap_required && !self.grant_attached {
            return KeepaliveGuardDecision::RefusedUnauthorizedBeforeAttach;
        }
        if !self.is_tcp {
            return KeepaliveGuardDecision::AnsweredMarkUnixNeverEnforced;
        }
        self.armed = true;
        let cand = now_ms.saturating_add(self.interval_ms);
        self.deadline_ms = keepalive_deadline_advance_b148(self.deadline_ms, cand);
        KeepaliveGuardDecision::ArmedOrRearmedTcpDeadline {
            deadline_ms: self.deadline_ms,
        }
    }

    /// Re-arm deadline on any ordinary request read once armed.
    pub fn on_ordinary_read(&mut self, now_ms: u64) {
        if self.is_tcp && self.armed && !self.closed {
            let cand = now_ms.saturating_add(self.interval_ms);
            self.deadline_ms = keepalive_deadline_advance_b148(self.deadline_ms, cand);
        }
    }

    /// Poll whether this connection has missed its keepalive deadline at `now_ms`.
    pub fn poll_deadline(&mut self, now_ms: u64) -> KeepaliveGuardDecision {
        if self.closed {
            return KeepaliveGuardDecision::AlreadyClosed;
        }
        if tcp_keepalive_expired_b148(
            self.is_tcp,
            self.armed,
            self.closed,
            now_ms,
            self.deadline_ms,
        ) {
            self.closed = true;
            KeepaliveGuardDecision::ClosedDeadTcpAndFireWillOnce {
                expired_at_ms: now_ms,
            }
        } else {
            KeepaliveGuardDecision::ConnectionStillAlive
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_guarded_attach_exempts_unix_and_unarmed_tcp_and_fires_will_once_on_armed_tcp() {
        let mut guarded_tcp = KeepaliveConnectionGuard::new(true, true, 200);
        // Keepalive before attach -> ERR_UNAUTHORIZED and NOT armed!
        assert_eq!(
            guarded_tcp.on_keepalive_request(100),
            KeepaliveGuardDecision::RefusedUnauthorizedBeforeAttach
        );
        assert_eq!(
            guarded_tcp.poll_deadline(10_000),
            KeepaliveGuardDecision::ConnectionStillAlive
        );

        // Unix connection that sends Keepalive is answered Mark and NEVER cut!
        let mut unix_conn = KeepaliveConnectionGuard::new(false, false, 200);
        assert_eq!(
            unix_conn.on_keepalive_request(100),
            KeepaliveGuardDecision::AnsweredMarkUnixNeverEnforced
        );
        assert_eq!(
            unix_conn.poll_deadline(10_000),
            KeepaliveGuardDecision::ConnectionStillAlive
        );

        // Once attached and armed on TCP, silence past deadline closes & fires will exactly once!
        guarded_tcp.on_grant_attached();
        assert_eq!(
            guarded_tcp.on_keepalive_request(1_000),
            KeepaliveGuardDecision::ArmedOrRearmedTcpDeadline { deadline_ms: 1_200 }
        );
        assert_eq!(
            guarded_tcp.poll_deadline(1_200),
            KeepaliveGuardDecision::ClosedDeadTcpAndFireWillOnce {
                expired_at_ms: 1_200,
            }
        );
        assert_eq!(
            guarded_tcp.poll_deadline(1_300),
            KeepaliveGuardDecision::AlreadyClosed
        );
    }
}
