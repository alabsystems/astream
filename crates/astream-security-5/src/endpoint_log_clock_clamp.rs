// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Endpoint lane-3 `LogClock::keep_below` lineage-move clamper
//! (`docs/DESIGN-aterm-fabric.md` §3 lines 510–532; `Astream.Wire.TlaEndpointLogClockClamp`).
//!
//! When the bridge tells a lane-3 endpoint `link log <new_id> continues=<f> was=<was_id>`:
//! - An endpoint already on `(log_id, new_gen)` forgets nothing (`KeepAll`),
//! - An endpoint on the same `log_id` with `was_gen <= ep_gen < new_gen` (including an
//!   endpoint left ahead of the bridge's witness by an earlier move) keeps queued replies,
//!   owed receipts, parked reads, and delivery dedup strictly below `f` (`KeepBelow(f)`) and
//!   retires `>= f`,
//! - An endpoint on lane `< 3`, on `None`, on a different `log_id`, or outside `[was_gen, new_gen]`
//!   forgets all held bus offsets (`ForgetAll`).
//!
//! Pure stack `no_std`, zero loops, zero `Display` (`0` `unknown` and `0` `runtime_checked` in `astream-wire`).

#[cfg(clean_islands)]
#[path = "endpoint_log_clock_clamp_island.rs"]
mod endpoint_log_clock_clamp_island;
#[cfg(clean_islands)]
pub use endpoint_log_clock_clamp_island::{
    ep_clock_frontier_clamp_b130, ep_clock_gen_advance_b130,
};

/// Minimum endpoint protocol lane supporting `continues=<f> was=<id>` clamping (`3`).
pub const LANE_ENDPOINT_CLAMP_MIN: u8 = 3;

#[cfg(not(clean_islands))]
/// Clamp held offset frontier to `continues_at`.
#[must_use]
pub const fn ep_clock_frontier_clamp_b130(cand_held: u64, continues_at: u64) -> u64 {
    if cand_held < continues_at {
        cand_held
    } else {
        continues_at
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance adopted generation on same-log continuation.
#[must_use]
pub const fn ep_clock_gen_advance_b130(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// True iff `was_gen <= ep_gen && ep_gen < new_gen`.
    #[must_use]
    pub const fn ep_gen_in_move_window_b130(was_gen: u64, ep_gen: u64, new_gen: u64) -> bool
    clauses [ensures result == (was_gen <= ep_gen && ep_gen < new_gen)]
    {
        was_gen <= ep_gen && ep_gen < new_gen
    }
}

/// Action an endpoint's `LogClock` takes on a `link log` announcement.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum EndpointClampDecision {
    /// Already on `new_id`: keep every held offset unchanged.
    KeepAll,
    /// Same log in `[was_gen, new_gen)` at lane >= 3: keep `< continues_at`, retire `>= continues_at`.
    KeepBelow { continues_at: u64 },
    /// Lane `< 3`, no prior log, foreign log, or generation outside `[was_gen, new_gen]`: forget everything.
    ForgetAll,
}

/// Pure stack endpoint `LogClock` state (`128`-bit log UUID split as `(hi, lo)` + `gen`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct EndpointLogClock {
    has_log: bool,
    log_hi: u64,
    log_lo: u64,
    generation: u64,
    held_frontier: u64,
}

impl Default for EndpointLogClock {
    fn default() -> Self {
        Self::new()
    }
}

impl EndpointLogClock {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            has_log: false,
            log_hi: 0,
            log_lo: 0,
            generation: 0,
            held_frontier: 0,
        }
    }

    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    #[must_use]
    pub const fn held_frontier(&self) -> u64 {
        self.held_frontier
    }

    /// Record a new local queued reply / owed receipt / delivery dedup watermark on the active log.
    pub fn observe_offset(&mut self, offset_plus_one: u64) {
        if self.has_log && offset_plus_one > self.held_frontier {
            self.held_frontier = offset_plus_one;
        }
    }

    /// Apply a `link log` transition announced by `aterm-link` at `lane`.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_link_log(
        &mut self,
        lane: u8,
        new_hi: u64,
        new_lo: u64,
        new_gen: u64,
        continues_and_was: Option<(u64, u64)>,
    ) -> EndpointClampDecision {
        let same_uuid = self.has_log && self.log_hi == new_hi && self.log_lo == new_lo;
        if same_uuid && self.generation == new_gen {
            return EndpointClampDecision::KeepAll;
        }
        if lane >= LANE_ENDPOINT_CLAMP_MIN && same_uuid {
            if let Some((continues_at, was_gen)) = continues_and_was {
                if was_gen < new_gen
                    && ep_gen_in_move_window_b130(was_gen, self.generation, new_gen)
                {
                    self.held_frontier =
                        ep_clock_frontier_clamp_b130(self.held_frontier, continues_at);
                    self.generation = ep_clock_gen_advance_b130(self.generation, new_gen);
                    return EndpointClampDecision::KeepBelow { continues_at };
                }
            }
        }
        self.has_log = true;
        self.log_hi = new_hi;
        self.log_lo = new_lo;
        self.generation = new_gen;
        self.held_frontier = 0;
        EndpointClampDecision::ForgetAll
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clamps_lane_3_chain_of_moves_keeps_same_gen_and_forgets_lane_2_or_foreign() {
        let mut clk = EndpointLogClock::new();
        // Initial attach adopts log (0xAA, 0xBB, gen=2) via ForgetAll.
        assert_eq!(
            clk.apply_link_log(3, 0xAA, 0xBB, 2, None),
            EndpointClampDecision::ForgetAll
        );
        clk.observe_offset(50);
        // Duplicate announcement of same generation keeps everything.
        assert_eq!(
            clk.apply_link_log(3, 0xAA, 0xBB, 2, Some((30, 1))),
            EndpointClampDecision::KeepAll
        );
        assert_eq!(clk.held_frontier(), 50);

        // Bridge was at gen=1, endpoint already at gen=2, new is gen=4 with continues=32 -> KeepBelow(32)!
        assert_eq!(
            clk.apply_link_log(3, 0xAA, 0xBB, 4, Some((32, 1))),
            EndpointClampDecision::KeepBelow { continues_at: 32 }
        );
        assert_eq!(clk.generation(), 4);
        assert_eq!(clk.held_frontier(), 32);

        // Lane 2 endpoint forgets all even on valid continuation.
        assert_eq!(
            clk.apply_link_log(2, 0xAA, 0xBB, 5, Some((20, 4))),
            EndpointClampDecision::ForgetAll
        );
        assert_eq!(clk.held_frontier(), 0);
    }
}
