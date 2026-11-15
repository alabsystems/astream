// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd` pre-exec deadlock detector (`Astream.Host.TlaSyspolicydHangDetector`).
//!
//! Models the `aterm ctl @self status` `syspolicyd=stuck` rule: when macOS's
//! code-assessment subsystem deadlocks, non-platform executables hang before
//! userland entry while Apple platform binaries (`/bin/*`, `/usr/bin/*`,
//! `/sbin/*`, `/usr/sbin/*`) continue starting normally. Once `Stuck` is latched
//! (irreversible until OS reboot), non-platform spawns fail fast without hanging
//! new worker tabs and emit `"NEEDS YOU: restart the Mac"`.

#[cfg(clean_islands)]
#[path = "syspolicyd_hang_detector_island.rs"]
mod syspolicyd_hang_detector_island;
#[cfg(clean_islands)]
pub use syspolicyd_hang_detector_island::{syspolicy_severity_advance, syspolicy_stalls_clamp};

/// Exact operator escalation banner required when `syspolicyd` has deadlocked.
pub const NEEDS_YOU_RESTART_MAC: &str = "NEEDS YOU: restart the Mac";

/// Default consecutive pre-start hang threshold to latch `SyspolicydState::Stuck`.
pub const DEFAULT_STUCK_THRESHOLD: u64 = 2;

/// Hard upper bound on tracked consecutive stall probes.
pub const MAX_STALL_PROBES: u64 = 16;

#[cfg(not(clean_islands))]
/// Monotonically advance latched `syspolicyd` severity (`0 = Healthy`, `1 = Suspect`, `2 = Stuck`).
#[must_use]
pub const fn syspolicy_severity_advance(cur_sev: u64, cand_sev: u64) -> u64 {
    if cur_sev < cand_sev {
        cand_sev
    } else {
        cur_sev
    }
}

#[cfg(not(clean_islands))]
/// Clamp consecutive pre-start stall counter to `max_probes`.
#[must_use]
pub const fn syspolicy_stalls_clamp(cand_stalls: u64, max_probes: u64) -> u64 {
    if cand_stalls < max_probes {
        cand_stalls
    } else {
        max_probes
    }
}

contract_fn! {
    /// True iff `stalls` has reached `stuck_threshold`.
    #[must_use]
    pub const fn syspolicy_is_stuck(stalls: u64, stuck_threshold: u64) -> bool
    clauses [ensures result == (stuck_threshold <= stalls)]
    {
        stuck_threshold <= stalls
    }
}

/// Assessed state of macOS `syspolicyd` execution gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydState {
    Healthy,
    Suspect,
    Stuck,
}

impl SyspolicydState {
    #[must_use]
    pub const fn as_status_token(self) -> &'static str {
        match self {
            Self::Healthy => "ok",
            Self::Suspect => "suspect",
            Self::Stuck => "stuck",
        }
    }
}

/// True iff `path` is in a macOS Apple-signed platform binary prefix exempt from `syspolicyd` deadlock.
#[must_use]
pub fn is_macos_platform_binary(path: &[u8]) -> bool {
    matches!(
        path,
        [b'/', b'b', b'i', b'n', b'/', _, ..]
            | [b'/', b's', b'b', b'i', b'n', b'/', _, ..]
            | [b'/', b'u', b's', b'r', b'/', b'b', b'i', b'n', b'/', _, ..]
            | [
                b'/',
                b'u',
                b's',
                b'r',
                b'/',
                b's',
                b'b',
                b'i',
                b'n',
                b'/',
                _,
                ..
            ]
    )
}

/// Pre-exec deadlock detector for `astream-host` process spawning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydHangDetector {
    severity: u64,
    non_platform_stalls: u64,
    platform_control_ok: bool,
    stuck_threshold: u64,
}

impl Default for SyspolicydHangDetector {
    fn default() -> Self {
        Self::new(DEFAULT_STUCK_THRESHOLD)
    }
}

impl SyspolicydHangDetector {
    #[must_use]
    pub const fn new(stuck_threshold: u64) -> Self {
        let thresh = if stuck_threshold == 0 {
            1
        } else if stuck_threshold < MAX_STALL_PROBES {
            stuck_threshold
        } else {
            MAX_STALL_PROBES
        };
        Self {
            severity: 0,
            non_platform_stalls: 0,
            platform_control_ok: false,
            stuck_threshold: thresh,
        }
    }

    #[must_use]
    pub const fn state(&self) -> SyspolicydState {
        if self.severity >= 2 {
            SyspolicydState::Stuck
        } else if self.severity == 1 {
            SyspolicydState::Suspect
        } else {
            SyspolicydState::Healthy
        }
    }

    #[must_use]
    pub const fn non_platform_stalls(&self) -> u64 {
        self.non_platform_stalls
    }

    /// Check whether spawning `program_path` is permitted or must stop immediately with `NEEDS YOU: restart the Mac`.
    pub fn check_pre_spawn(&self, program_path: &[u8]) -> Result<(), &'static str> {
        if self.state() == SyspolicydState::Stuck && !is_macos_platform_binary(program_path) {
            return Err(NEEDS_YOU_RESTART_MAC);
        }
        Ok(())
    }

    /// Record whether `program_path` entered userland before the pre-start timeout.
    pub fn record_spawn_outcome(&mut self, program_path: &[u8], hung_before_start: bool) {
        let is_platform = is_macos_platform_binary(program_path);
        if is_platform {
            if !hung_before_start {
                self.platform_control_ok = true;
                if syspolicy_is_stuck(self.non_platform_stalls, self.stuck_threshold) {
                    self.severity = syspolicy_severity_advance(self.severity, 2);
                }
            }
            return;
        }

        if hung_before_start {
            let cand = self.non_platform_stalls.saturating_add(1);
            self.non_platform_stalls = syspolicy_stalls_clamp(cand, MAX_STALL_PROBES);
            let cand_sev = if syspolicy_is_stuck(self.non_platform_stalls, self.stuck_threshold)
                && self.platform_control_ok
            {
                2
            } else {
                1
            };
            self.severity = syspolicy_severity_advance(self.severity, cand_sev);
        } else if self.state() != SyspolicydState::Stuck {
            // Once Stuck is latched, only a Mac restart clears it; Suspect resets stall count on clean start.
            self.non_platform_stalls = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latches_stuck_when_non_platform_hangs_and_platform_starts() {
        let mut det = SyspolicydHangDetector::new(2);
        assert_eq!(det.state(), SyspolicydState::Healthy);

        // First third-party binary hangs pre-start -> Suspect
        det.record_spawn_outcome(b"/opt/atpkg/bin/targo", true);
        assert_eq!(det.state(), SyspolicydState::Suspect);
        assert_eq!(det.check_pre_spawn(b"/opt/atpkg/bin/targo"), Ok(()));

        // Platform control binary (/bin/ps) starts cleanly
        det.record_spawn_outcome(b"/bin/ps", false);
        assert_eq!(det.state(), SyspolicydState::Suspect);

        // Second third-party binary hangs pre-start -> latches Stuck!
        det.record_spawn_outcome(b"/fixture-home/.local/bin/claude", true);
        assert_eq!(det.state(), SyspolicydState::Stuck);
        assert_eq!(det.state().as_status_token(), "stuck");

        // Non-platform binaries are now refused with exact NEEDS YOU banner; platform binaries still allowed
        assert_eq!(
            det.check_pre_spawn(b"/opt/atpkg/bin/targo"),
            Err("NEEDS YOU: restart the Mac")
        );
        assert_eq!(det.check_pre_spawn(b"/usr/bin/true"), Ok(()));
    }
}
