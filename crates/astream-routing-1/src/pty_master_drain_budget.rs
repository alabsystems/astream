// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fair PTY master burst-drain quantum scheduler (`Astream.Host.TlaPtyMasterDrainBudget`).
//!
//! Ensures high-volume child output (`yes`, `cat`, verbose compiler logs) yields deterministically
//! after `max_turn_bytes` or `max_turn_reads` so `astream-host` services `Resize`, `In` keystrokes,
//! and `SIGCHLD` exit reaping without starvation.

#[cfg(clean_islands)]
#[path = "pty_master_drain_budget_island.rs"]
mod pty_master_drain_budget_island;
#[cfg(clean_islands)]
pub use pty_master_drain_budget_island::{pty_drain_bytes_clamp, pty_drain_reads_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_drain_bytes_clamp(cand_bytes: u64, max_turn_bytes: u64) -> u64 {
    if cand_bytes < max_turn_bytes {
        cand_bytes
    } else {
        max_turn_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_drain_reads_clamp(cand_reads: u64, max_turn_reads: u64) -> u64 {
    if cand_reads < max_turn_reads {
        cand_reads
    } else {
        max_turn_reads
    }
}

contract_fn! {
    /// Verified check whether the current PTY drain quantum still has byte headroom
    /// (`drained_bytes < max_turn_bytes`), linked via `clean-kernel-defeq` to
    /// `pty_drain_within_turn_cap_isl`.
    #[must_use]
    pub const fn pty_drain_within_turn_cap(drained_bytes: u64, max_turn_bytes: u64) -> bool
    clauses [ensures result == (drained_bytes < max_turn_bytes)]
    {
        drained_bytes < max_turn_bytes
    }
}

/// Default per-quantum PTY drain byte cap (`256 KiB`).
pub const DEFAULT_PTY_TURN_BYTES: u64 = 256 * 1024;

/// Default per-quantum non-blocking `read()` syscall cap (`16`).
pub const DEFAULT_PTY_TURN_READS: u64 = 16;

/// Quantum scheduler for non-blocking PTY master `read()` bursts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyMasterDrainBudget {
    max_turn_bytes: u64,
    max_turn_reads: u64,
    drained_bytes: u64,
    read_calls: u64,
}

impl PtyMasterDrainBudget {
    #[must_use]
    pub const fn new(max_turn_bytes: u64, max_turn_reads: u64) -> Self {
        let cb = if max_turn_bytes == 0 {
            DEFAULT_PTY_TURN_BYTES
        } else {
            max_turn_bytes
        };
        let cr = if max_turn_reads == 0 {
            DEFAULT_PTY_TURN_READS
        } else {
            max_turn_reads
        };
        Self {
            max_turn_bytes: cb,
            max_turn_reads: cr,
            drained_bytes: 0,
            read_calls: 0,
        }
    }

    #[must_use]
    pub const fn drained_bytes(&self) -> u64 {
        self.drained_bytes
    }

    #[must_use]
    pub const fn read_calls(&self) -> u64 {
        self.read_calls
    }

    /// Whether another non-blocking `read()` may run before yielding to control-plane polling.
    #[must_use]
    pub const fn can_read_more(&self) -> bool {
        pty_drain_within_turn_cap(self.drained_bytes, self.max_turn_bytes)
            && self.read_calls < self.max_turn_reads
    }

    /// Account for one non-blocking `read()` returning `n_bytes`, returning `true` if another
    /// read may proceed in this quantum or `false` if the driver should yield to control polling.
    pub fn record_read(&mut self, n_bytes: usize) -> bool {
        let cand_b = self.drained_bytes.saturating_add(n_bytes as u64);
        let cand_r = self.read_calls.saturating_add(1);
        self.drained_bytes = pty_drain_bytes_clamp(cand_b, self.max_turn_bytes);
        self.read_calls = pty_drain_reads_clamp(cand_r, self.max_turn_reads);
        n_bytes > 0 && self.can_read_more()
    }

    /// Reset quantum counters after servicing control-plane `In` / `Resize` / `SIGCHLD` events.
    pub fn begin_next_quantum(&mut self) {
        self.drained_bytes = 0;
        self.read_calls = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yields_to_control_plane_on_byte_or_syscall_quantum() {
        let mut b = PtyMasterDrainBudget::new(8_192, 3);
        assert!(b.can_read_more());
        assert!(b.record_read(4_096));
        assert!(!b.record_read(4_096)); // 8_192 bytes reached -> yield!
        assert_eq!(b.drained_bytes(), 8_192);
        assert_eq!(b.read_calls(), 2);

        b.begin_next_quantum();
        assert!(b.record_read(100));
        assert!(b.record_read(100));
        assert!(!b.record_read(100)); // 3 syscalls reached -> yield!
        assert_eq!(b.read_calls(), 3);
    }
}
