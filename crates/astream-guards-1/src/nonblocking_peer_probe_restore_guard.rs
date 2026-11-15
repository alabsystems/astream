// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Rate-limited non-blocking subscriber peer-gone probe & mandatory blocking-mode restore
//! (`evidence/manifest.toml` `broker.peer-probe-nonblocking`;
//! `Astream.Broker.TlaNonblockingPeerProbeRestoreGuard`).
//!
//! Enforces the `tail_loop` vanished-subscriber reaping contract:
//! - Probes at most once per `liveness_poll_ms` (`200` ms default), avoiding `60x` syscall storms
//!   when a subscriber scans past bursts of non-matching records,
//! - Toggles `set_nonblocking(true) -> read_1_byte -> set_nonblocking(false)` and guarantees the
//!   stream is ALWAYS restored to blocking mode before returning `PeerAliveWouldBlock`, so a later
//!   `64 x 60 KiB` batch delivery never drops mid-write with `WouldBlock`!

#[cfg(clean_islands)]
#[path = "nonblocking_peer_probe_restore_guard_island.rs"]
mod nonblocking_peer_probe_restore_guard_island;
#[cfg(clean_islands)]
pub use nonblocking_peer_probe_restore_guard_island::{
    peer_probes_count_advance_b146, probe_clock_advance_b146,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the tail-loop monotonic probe clock (`ms`).
#[must_use]
pub const fn probe_clock_advance_b146(cur_ms: u64, cand_ms: u64) -> u64 {
    if cur_ms < cand_ms {
        cand_ms
    } else {
        cur_ms
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `BrokerStats::peer_probes`.
#[must_use]
pub const fn peer_probes_count_advance_b146(cur_probes: u64, cand_probes: u64) -> u64 {
    if cur_probes < cand_probes {
        cand_probes
    } else {
        cur_probes
    }
}

contract_fn! {
    /// True iff `elapsed_since_last_probe_ms >= poll_interval_ms` and the socket was restored to
    /// blocking mode after the non-blocking probe.
    #[must_use]
    pub const fn probe_due_and_restored_blocking_b146(
        elapsed_since_last_probe_ms: u64,
        poll_interval_ms: u64,
        restored_blocking: bool,
    ) -> bool
    clauses [ensures result == (poll_interval_ms <= elapsed_since_last_probe_ms && restored_blocking)]
    {
        poll_interval_ms <= elapsed_since_last_probe_ms && restored_blocking
    }
}

/// Result of a rate-limited non-blocking subscriber liveness check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PeerProbeDecision {
    SkippedPollNotDue { peer_probes: u64 },
    PeerAliveSocketRestoredBlocking { peer_probes: u64 },
    ReapGoneSubscriber,
    AbortRestoreBlockingFailed,
}

/// Rate-limited subscriber peer-probe scheduler and blocking-restore guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubscriberPeerProbeGuard {
    last_probe_ms: u64,
    now_ms: u64,
    poll_interval_ms: u64,
    peer_probes: u64,
}

impl SubscriberPeerProbeGuard {
    #[must_use]
    pub const fn new(start_ms: u64, poll_interval_ms: u64) -> Self {
        Self {
            last_probe_ms: start_ms,
            now_ms: start_ms,
            poll_interval_ms,
            peer_probes: 0,
        }
    }

    #[must_use]
    pub const fn peer_probes(&self) -> u64 {
        self.peer_probes
    }

    pub fn maybe_probe(
        &mut self,
        cand_now_ms: u64,
        probe_saw_eof_or_unexpected_byte: bool,
        restore_blocking_succeeded: bool,
    ) -> PeerProbeDecision {
        self.now_ms = probe_clock_advance_b146(self.now_ms, cand_now_ms);
        let elapsed = self.now_ms.saturating_sub(self.last_probe_ms);
        if elapsed < self.poll_interval_ms {
            return PeerProbeDecision::SkippedPollNotDue {
                peer_probes: self.peer_probes,
            };
        }
        self.last_probe_ms = self.now_ms;
        let next_probes = self.peer_probes.saturating_add(1);
        self.peer_probes = peer_probes_count_advance_b146(self.peer_probes, next_probes);

        if probe_saw_eof_or_unexpected_byte {
            return PeerProbeDecision::ReapGoneSubscriber;
        }
        if !probe_due_and_restored_blocking_b146(
            elapsed,
            self.poll_interval_ms,
            restore_blocking_succeeded,
        ) {
            return PeerProbeDecision::AbortRestoreBlockingFailed;
        }
        PeerProbeDecision::PeerAliveSocketRestoredBlocking {
            peer_probes: self.peer_probes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_probes_under_non_matching_burst_and_reaps_closed_peer_when_poll_due() {
        let mut g = SubscriberPeerProbeGuard::new(1_000, 3_600_000);
        // 20 unmatched records within an hour's poll perform 0 probes!
        for step in 1..=20 {
            assert_eq!(
                g.maybe_probe(1_000 + step, false, true),
                PeerProbeDecision::SkippedPollNotDue { peer_probes: 0 }
            );
        }
        // Under a 200 ms poll, alive peer probes once and restores blocking, then closed peer reaps:
        let mut live = SubscriberPeerProbeGuard::new(0, 200);
        assert_eq!(
            live.maybe_probe(200, false, true),
            PeerProbeDecision::PeerAliveSocketRestoredBlocking { peer_probes: 1 }
        );
        assert_eq!(
            live.maybe_probe(400, true, true),
            PeerProbeDecision::ReapGoneSubscriber
        );
    }
}
