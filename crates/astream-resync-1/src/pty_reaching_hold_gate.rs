// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Scope-blind `is_pty_reaching` drive-hold gate & `hold_on_bridge_lost` drop guard
//! (`docs/DESIGN-aterm-fabric.md` §5.3 lines 1321–1334 & 1395–1416, aterm `394daf4643` & `bd42460f7`;
//! `Astream.Host.TlaPtyReachingHoldGate`).
//!
//! Enforces `aterm-gui-fabric`'s three-seam structural hold discipline:
//! - Refuses session-targeted PTY-reaching verbs (`send`, `paste`, `focus`, `close`, `restart`, etc.)
//!   when the target session is held (`ERR halted <human_reason>`),
//! - Refuses sessionless PTY-reaching verbs (`invoke`, `tab`) whenever ANY session on the instance
//!   is held (`held_sessions_count > 0`),
//! - Exempts non-PTY communication verbs (`post`, `inbox seen`, `meta set`, `lease`) so a halted
//!   agent can still ask `"why am I halted?"` and raise `attention=`,
//! - On bridge disconnect (`bd42460f7`), leaves sessions running with `hold_advisory=fabric-lost`
//!   unless `hold_on_bridge_lost == true`, while keeping any pre-existing fleet hold sticky!

#[cfg(clean_islands)]
#[path = "pty_reaching_hold_gate_island.rs"]
mod pty_reaching_hold_gate_island;
#[cfg(clean_islands)]
pub use pty_reaching_hold_gate_island::{hold_reason_len_clamp_b133, hold_refused_advance_b133};

/// Maximum preserved human halt `reason=` byte length (`256`).
pub const MAX_HALT_REASON_BYTES: u64 = 256;

#[cfg(not(clean_islands))]
/// Clamp human halt `reason=` length to `max_reason_bytes`.
#[must_use]
pub const fn hold_reason_len_clamp_b133(cand_len: u64, max_reason_bytes: u64) -> u64 {
    if cand_len < max_reason_bytes {
        cand_len
    } else {
        max_reason_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of PTY-reaching verbs refused with `ERR halted`.
#[must_use]
pub const fn hold_refused_advance_b133(cur_refused: u64, cand_refused: u64) -> u64 {
    if cur_refused < cand_refused {
        cand_refused
    } else {
        cur_refused
    }
}

contract_fn! {
    /// True iff `held_sessions_count > 0` (blocks sessionless `invoke` / `tab` verbs).
    #[must_use]
    pub const fn hold_blocks_global_verb_b133(held_sessions_count: u64) -> bool
    clauses [ensures result == (held_sessions_count > 0)]
    {
        held_sessions_count > 0
    }
}

/// Control-socket verb reachability class (`fabric::is_pty_reaching`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SocketVerbClass {
    /// `post`, `inbox seen`, `meta set`, `lease`, `status` — never touches PTY, always exempt!
    NonPtyExempt,
    /// `send`, `key`, `paste`, `focus`, `resize`, `signal`, `restart`, `close`, `confirm`, etc.
    SessionPtyReaching { target_held: bool },
    /// `invoke` (e.g. `invoke Paste`), `tab` (`tab close`) — resolves no session, blocked if ANY session is held!
    InstanceWidePtyReaching,
}

/// Bridge-disconnect transition (`bd42460f7`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BridgeLostDisposition {
    /// Default (`hold_on_bridge_lost = false`): keep standing fleet holds sticky, mark `hold_advisory=fabric-lost`.
    AdvisoryOnlyKeepStandingFleetHolds,
    /// Opt-in (`hold_on_bridge_lost = true`): sweep `hold on reason=fabric-lost` across governed sessions.
    EnforceHoldSweepFabricLost,
}

/// Stateful endpoint hold gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PtyReachingHoldGate {
    hold_on_bridge_lost: bool,
    held_sessions_count: u64,
    reason_len_bytes: u64,
    refused_verbs: u64,
}

impl PtyReachingHoldGate {
    #[must_use]
    pub const fn new(hold_on_bridge_lost: bool) -> Self {
        Self {
            hold_on_bridge_lost,
            held_sessions_count: 0,
            reason_len_bytes: 0,
            refused_verbs: 0,
        }
    }

    #[must_use]
    pub const fn refused_verbs(&self) -> u64 {
        self.refused_verbs
    }

    /// Update active held-session count and human `reason=` length.
    pub fn set_fleet_hold_state(&mut self, held_sessions_count: u64, human_reason_len: u64) {
        self.held_sessions_count = held_sessions_count;
        self.reason_len_bytes = hold_reason_len_clamp_b133(human_reason_len, MAX_HALT_REASON_BYTES);
    }

    /// Check whether `verb` is admitted (`Ok(())`) or refused (`Err(clamped_reason_len)` -> `ERR halted <reason>`).
    pub fn check_verb(&mut self, verb: SocketVerbClass) -> Result<(), u64> {
        let blocked = match verb {
            SocketVerbClass::NonPtyExempt => false,
            SocketVerbClass::SessionPtyReaching { target_held } => target_held,
            SocketVerbClass::InstanceWidePtyReaching => {
                hold_blocks_global_verb_b133(self.held_sessions_count)
            }
        };
        if blocked {
            let cand = self.refused_verbs.saturating_add(1);
            self.refused_verbs = hold_refused_advance_b133(self.refused_verbs, cand);
            Err(self.reason_len_bytes)
        } else {
            Ok(())
        }
    }

    /// Determine drop-guard behavior when the `aterm-link` bridge connection drops.
    #[must_use]
    pub const fn on_bridge_lost(&self) -> BridgeLostDisposition {
        if self.hold_on_bridge_lost {
            BridgeLostDisposition::EnforceHoldSweepFabricLost
        } else {
            BridgeLostDisposition::AdvisoryOnlyKeepStandingFleetHolds
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_session_and_instance_pty_verbs_exempts_post_and_respects_advisory_bridge_loss() {
        let mut g = PtyReachingHoldGate::new(false);
        g.set_fleet_hold_state(1, 42);

        assert_eq!(g.check_verb(SocketVerbClass::NonPtyExempt), Ok(()));
        assert_eq!(
            g.check_verb(SocketVerbClass::SessionPtyReaching { target_held: false }),
            Ok(())
        );
        assert_eq!(
            g.check_verb(SocketVerbClass::SessionPtyReaching { target_held: true }),
            Err(42)
        );
        // `invoke Paste` / `tab close` refused while ANY session is held!
        assert_eq!(
            g.check_verb(SocketVerbClass::InstanceWidePtyReaching),
            Err(42)
        );
        assert_eq!(g.refused_verbs(), 2);
        assert_eq!(
            g.on_bridge_lost(),
            BridgeLostDisposition::AdvisoryOnlyKeepStandingFleetHolds
        );
    }
}
