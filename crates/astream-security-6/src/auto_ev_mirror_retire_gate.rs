// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `[fabric] log = "auto"` `ev` session-log mirror window & closed-session `mirror_retire_face` gate
//! (`docs/DESIGN-aterm-fabric.md` §3 lines 680–695; `Astream.Broker.TlaAutoEvMirrorRetireGate`).
//!
//! Enforces `aterm-link`'s `ev` mirror contract:
//! - Runs only when config is `auto` AND `Hello` advertises a prefix retention rule covering
//!   this node's `ev` faces (`broker_retains_ev == true`); otherwise reports `mirror=unretained`
//!   or `mirror=off`,
//! - Bounds mirrored bytes to `NODE_MIRROR_WINDOW_BYTES` (`64 MiB`, four nodes = `256 MiB` prefix rule),
//! - Retires a closed session's `ev` face from `Last` (`Client::retire_subject`) ONLY when the
//!   mirror is active and the session's final tail has landed on the bus!

#[cfg(clean_islands)]
#[path = "auto_ev_mirror_retire_gate_island.rs"]
mod auto_ev_mirror_retire_gate_island;
#[cfg(clean_islands)]
pub use auto_ev_mirror_retire_gate_island::{
    ev_mirror_retired_advance_b131, ev_mirror_window_clamp_b131,
};

/// Per-node session-log `ev` mirror byte window (`64 MiB`).
pub const NODE_MIRROR_WINDOW_BYTES: u64 = 64 * 1024 * 1024;

#[cfg(not(clean_islands))]
/// Clamp active node `ev` mirror bytes to `node_window_bytes`.
#[must_use]
pub const fn ev_mirror_window_clamp_b131(cand_bytes: u64, node_window_bytes: u64) -> u64 {
    if cand_bytes < node_window_bytes {
        cand_bytes
    } else {
        node_window_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of closed-session `ev` faces retired from `Last`.
#[must_use]
pub const fn ev_mirror_retired_advance_b131(cur_retired: u64, cand_retired: u64) -> u64 {
    if cur_retired < cand_retired {
        cand_retired
    } else {
        cur_retired
    }
}

contract_fn! {
    /// True iff `cfg_auto && broker_retains_ev`.
    #[must_use]
    pub const fn ev_mirror_active_b131(cfg_auto: bool, broker_retains_ev: bool) -> bool
    clauses [ensures result == (cfg_auto && broker_retains_ev)]
    {
        cfg_auto && broker_retains_ev
    }
}

/// Observable `aterm fabric status` mirror state.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MirrorStatusWord {
    /// `log = "off"`.
    Off,
    /// `log = "auto"`, but broker `Hello` advertises no prefix retention covering `ev`.
    Unretained,
    /// Actively mirroring within `NODE_MIRROR_WINDOW_BYTES`.
    Active,
}

/// Stateful `ev` mirror window and closed-session face-retirement gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AutoEvMirrorRetireGate {
    cfg_auto: bool,
    broker_retains_ev: bool,
    node_window_bytes: u64,
    mirrored_bytes: u64,
    retired_faces: u64,
}

impl AutoEvMirrorRetireGate {
    #[must_use]
    pub const fn new(cfg_auto: bool, broker_retains_ev: bool) -> Self {
        Self {
            cfg_auto,
            broker_retains_ev,
            node_window_bytes: NODE_MIRROR_WINDOW_BYTES,
            mirrored_bytes: 0,
            retired_faces: 0,
        }
    }

    #[must_use]
    pub const fn status_word(&self) -> MirrorStatusWord {
        if !self.cfg_auto {
            MirrorStatusWord::Off
        } else if ev_mirror_active_b131(self.cfg_auto, self.broker_retains_ev) {
            MirrorStatusWord::Active
        } else {
            MirrorStatusWord::Unretained
        }
    }

    #[must_use]
    pub const fn mirrored_bytes(&self) -> u64 {
        self.mirrored_bytes
    }

    #[must_use]
    pub const fn retired_faces(&self) -> u64 {
        self.retired_faces
    }

    /// Account a mirrored turn chunk into the 64 MiB node window; returns `false` if mirror is inactive.
    pub fn record_mirrored_chunk(&mut self, chunk_bytes: u64) -> bool {
        if !ev_mirror_active_b131(self.cfg_auto, self.broker_retains_ev) {
            return false;
        }
        let cand = self.mirrored_bytes.saturating_add(chunk_bytes);
        self.mirrored_bytes = ev_mirror_window_clamp_b131(cand, self.node_window_bytes);
        true
    }

    /// Decide whether a closed session's `ev` face should call `Client::retire_subject`.
    pub fn should_retire_closed_ev_face(&mut self, tail_landed_on_bus: bool) -> bool {
        if !tail_landed_on_bus || !ev_mirror_active_b131(self.cfg_auto, self.broker_retains_ev) {
            return false;
        }
        let cand = self.retired_faces.saturating_add(1);
        self.retired_faces = ev_mirror_retired_advance_b131(self.retired_faces, cand);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unretained_broker_reports_unretained_skips_mirror_and_never_retires_ev_face() {
        let mut unret = AutoEvMirrorRetireGate::new(true, false);
        assert_eq!(unret.status_word(), MirrorStatusWord::Unretained);
        assert!(!unret.record_mirrored_chunk(4_096));
        assert!(!unret.should_retire_closed_ev_face(true));
        assert_eq!(unret.retired_faces(), 0);

        let mut active = AutoEvMirrorRetireGate::new(true, true);
        assert_eq!(active.status_word(), MirrorStatusWord::Active);
        assert!(active.record_mirrored_chunk(NODE_MIRROR_WINDOW_BYTES + 512));
        assert_eq!(active.mirrored_bytes(), NODE_MIRROR_WINDOW_BYTES);
        assert!(!active.should_retire_closed_ev_face(false));
        assert!(active.should_retire_closed_ev_face(true));
        assert_eq!(active.retired_faces(), 1);
    }
}
