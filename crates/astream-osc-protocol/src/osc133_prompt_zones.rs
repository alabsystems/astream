// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Semantic shell integration (`OSC 133` FinalTerm zones: `A` prompt start -> `B` command input ->
//! `C` command execution output -> `D` command finished) tracking command boundaries in `aterm`
//! (`Astream.OscProto.TlaOsc133PromptZones`).

#[cfg(clean_islands)]
#[path = "osc133_prompt_zones_island.rs"]
mod osc133_prompt_zones_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_zone_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_cmd_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use osc133_prompt_zones_island::{osc_cmd_advance, osc_zone_clamp};

/// Highest `OSC 133` phase index (`0 = Idle/D`, `1 = PromptA`, `2 = InputB`, `3 = OutputC`).
pub const MAX_OSC133_PHASE: u64 = 3;

contract_fn! {
    /// Verified forward-zone transition check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `osc_zone_ordered_isl`.
    #[must_use]
    pub const fn osc_zone_ordered(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct Osc133Tracker {
    phase: u64,
    completed_commands: u64,
    last_exit_code: u64,
}

impl Osc133Tracker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            phase: 0,
            completed_commands: 0,
            last_exit_code: 0,
        }
    }

    pub fn mark_a_prompt(&mut self) {
        self.phase = osc_zone_clamp(1, MAX_OSC133_PHASE);
    }

    pub fn mark_b_input(&mut self) -> bool {
        if osc_zone_ordered(self.phase, 1) {
            self.phase = osc_zone_clamp(2, MAX_OSC133_PHASE);
            true
        } else {
            false
        }
    }

    pub fn mark_c_output(&mut self) -> bool {
        if osc_zone_ordered(self.phase, 2) {
            self.phase = osc_zone_clamp(3, MAX_OSC133_PHASE);
            true
        } else {
            false
        }
    }

    pub fn mark_d_done(&mut self, exit_code: u64) -> bool {
        let was_running = osc_zone_ordered(self.phase, 2);
        self.phase = 0;
        self.last_exit_code = osc_zone_clamp(exit_code, 255);
        if was_running {
            self.completed_commands = osc_cmd_advance(
                self.completed_commands,
                self.completed_commands.saturating_add(1),
            );
        }
        was_running
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_full_a_b_c_d_shell_command_lifecycle() {
        let mut t = Osc133Tracker::new();
        t.mark_a_prompt();
        assert!(t.mark_b_input());
        assert!(t.mark_c_output());
        assert!(t.mark_d_done(0));
    }
}
