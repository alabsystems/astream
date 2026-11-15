// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Log-Identity Lineage Splice & Checkpoint Rewind Planner
//! (`Astream.Engine.TlaLineageSplicePlanner`).
//!
//! When an Ordered/Relaxed broker recovers from a power loss or a Replicated follower promotes to
//! leader, the log's generation advances (`old_gen -> new_gen`) with a certified divergence
//! boundary `diverge_offset` up to which both generations agree byte-for-byte.
//!
//! [`LineageSplicePlanner`] computes the exact minimal recovery action for a stateful consumer
//! (`aterm-link`, `aspump`, `astream-engine` folder) currently folded up to `consumer_cursor`:
//! - Stale generations (`new_gen < witnessed_gen`) or mismatched `log_id`s are rejected.
//! - If [`lineage_cursor_within_diverge`]`(consumer_cursor, diverge_offset)` holds, the consumer
//!   never observed any lost uncommitted tail record and continues seamlessly from
//!   `consumer_cursor` with zero state rebuild!
//! - Otherwise (`consumer_cursor > diverge_offset`), selects the highest retained checkpoint at or
//!   below `diverge_offset` (or `FullResetFromBase` if none exists or rewind exceeds
//!   `max_rewind_dist`), clamping reported rewind distance via Clean-origin
//!   [`lineage_rewind_clamp`] and advancing `witnessed_gen` monotonically via Clean-origin
//!   [`lineage_gen_advance`].

#[cfg(clean_islands)]
#[path = "lineage_splice_island.rs"]
mod lineage_splice_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lineage_rewind_clamp(cand_dist: u64, max_dist: u64) -> u64 {
    if cand_dist < max_dist {
        cand_dist
    } else {
        max_dist
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lineage_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}
#[cfg(clean_islands)]
pub use lineage_splice_island::{lineage_gen_advance, lineage_rewind_clamp};

/// Default maximum replay distance from a retained checkpoint (`100_000` records).
pub const DEFAULT_MAX_LINEAGE_REWIND: u64 = 100_000;

contract_fn! {
    /// Kernel-certified check that `cursor <= diverge_offset`, linked via
    /// `clean-kernel-defeq` to `lineage_cursor_within_diverge_isl`.
    #[must_use]
    pub const fn lineage_cursor_within_diverge(cursor: u64, diverge_offset: u64) -> bool
    clauses [ensures result == (cursor <= diverge_offset)]
    {
        cursor <= diverge_offset
    }
}

/// Recovery decision produced by [`LineageSplicePlanner::plan_reconnect`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineageSplicePlan {
    /// Mismatched `log_id`: completely distinct log; consumer must discard state and reset.
    ForeignLogReset { new_generation: u64 },
    /// Server reported a generation strictly older than one already witnessed for this `log_id`.
    RejectStaleGeneration { server_gen: u64, witnessed_gen: u64 },
    /// `consumer_cursor <= diverge_offset` (or identical generation): resume directly at
    /// `consumer_cursor` without rewinding folded state.
    SeamlessContinue {
        resume_offset: u64,
        new_generation: u64,
    },
    /// Consumer folded speculative records beyond `diverge_offset`: restore `checkpoint_offset`
    /// (`<= diverge_offset`) and replay `checkpoint_offset .. diverge_offset` on the new lineage.
    RewindToCheckpoint {
        checkpoint_offset: u64,
        diverge_offset: u64,
        clamped_rewind_dist: u64,
        new_generation: u64,
    },
    /// No retained checkpoint `<= diverge_offset` within `max_rewind_dist`: rebuild from log base.
    FullRebuildFromZero {
        diverge_offset: u64,
        new_generation: u64,
    },
}

/// Stateful consumer lineage splice planner backed by `Astream.Engine.TlaLineageSplicePlanner`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineageSplicePlanner {
    log_id: [u8; 16],
    witnessed_gen: u64,
    last_rewind_dist: u64,
    max_rewind_dist: u64,
}

impl LineageSplicePlanner {
    /// Construct a planner pinned to `log_id` and `initial_gen`, with `max_rewind_dist`.
    #[must_use]
    pub const fn new(log_id: [u8; 16], initial_gen: u64, max_rewind_dist: u64) -> Self {
        Self {
            log_id,
            witnessed_gen: initial_gen,
            last_rewind_dist: 0,
            max_rewind_dist,
        }
    }

    /// Construct a planner with [`DEFAULT_MAX_LINEAGE_REWIND`].
    #[must_use]
    pub const fn with_defaults(log_id: [u8; 16], initial_gen: u64) -> Self {
        Self::new(log_id, initial_gen, DEFAULT_MAX_LINEAGE_REWIND)
    }

    /// Highest log generation witnessed for `log_id`.
    #[must_use]
    pub const fn witnessed_gen(&self) -> u64 {
        self.witnessed_gen
    }

    /// Clamped rewind distance from the most recent splice (`<= max_rewind_dist`).
    #[must_use]
    pub const fn last_rewind_dist(&self) -> u64 {
        self.last_rewind_dist
    }

    /// Plan recovery on reconnect given the broker's `(server_log_id, server_gen)`, optional
    /// common ancestor `diverge_offset` with `self.witnessed_gen`, current `consumer_cursor`, and
    /// retained local `checkpoint_offsets`.
    pub fn plan_reconnect(
        &mut self,
        server_log_id: [u8; 16],
        server_gen: u64,
        diverge_offset: Option<u64>,
        consumer_cursor: u64,
        checkpoint_offsets: &[u64],
    ) -> LineageSplicePlan {
        if server_log_id != self.log_id {
            self.log_id = server_log_id;
            self.witnessed_gen = server_gen;
            self.last_rewind_dist = 0;
            return LineageSplicePlan::ForeignLogReset {
                new_generation: server_gen,
            };
        }
        if server_gen < self.witnessed_gen {
            return LineageSplicePlan::RejectStaleGeneration {
                server_gen,
                witnessed_gen: self.witnessed_gen,
            };
        }
        if server_gen == self.witnessed_gen {
            self.last_rewind_dist = 0;
            return LineageSplicePlan::SeamlessContinue {
                resume_offset: consumer_cursor,
                new_generation: server_gen,
            };
        }

        let next_gen = lineage_gen_advance(self.witnessed_gen, server_gen);
        self.witnessed_gen = next_gen;

        let Some(div_off) = diverge_offset else {
            self.last_rewind_dist = lineage_rewind_clamp(consumer_cursor, self.max_rewind_dist);
            return LineageSplicePlan::FullRebuildFromZero {
                diverge_offset: 0,
                new_generation: next_gen,
            };
        };

        if lineage_cursor_within_diverge(consumer_cursor, div_off) {
            self.last_rewind_dist = 0;
            return LineageSplicePlan::SeamlessContinue {
                resume_offset: consumer_cursor,
                new_generation: next_gen,
            };
        }

        // Find highest checkpoint `<= div_off`.
        let mut best_ckpt: Option<u64> = None;
        let mut cur_ckpts = checkpoint_offsets;
        while let &[ck, ref rest @ ..] = cur_ckpts {
            if ck <= div_off {
                match best_ckpt {
                    Some(prev) if ck > prev => best_ckpt = Some(ck),
                    None => best_ckpt = Some(ck),
                    _ => {}
                }
            }
            cur_ckpts = rest;
        }

        match best_ckpt {
            Some(ckpt) => {
                let replay_span = div_off.saturating_sub(ckpt);
                let total_back = consumer_cursor.saturating_sub(ckpt);
                let clamped = lineage_rewind_clamp(total_back, self.max_rewind_dist);
                self.last_rewind_dist = clamped;
                if replay_span <= self.max_rewind_dist {
                    LineageSplicePlan::RewindToCheckpoint {
                        checkpoint_offset: ckpt,
                        diverge_offset: div_off,
                        clamped_rewind_dist: clamped,
                        new_generation: next_gen,
                    }
                } else {
                    LineageSplicePlan::FullRebuildFromZero {
                        diverge_offset: div_off,
                        new_generation: next_gen,
                    }
                }
            }
            None => {
                self.last_rewind_dist = lineage_rewind_clamp(consumer_cursor, self.max_rewind_dist);
                LineageSplicePlan::FullRebuildFromZero {
                    diverge_offset: div_off,
                    new_generation: next_gen,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seamless_when_cursor_below_diverge_and_rewinds_to_nearest_checkpoint_above() {
        let id = [0x42u8; 16];
        let mut p = LineageSplicePlanner::new(id, 1, 500);

        // Cursor at 180 <= diverge 200 -> seamless continue!
        assert_eq!(
            p.plan_reconnect(id, 2, Some(200), 180, &[0, 100, 150]),
            LineageSplicePlan::SeamlessContinue {
                resume_offset: 180,
                new_generation: 2,
            }
        );
        assert_eq!(p.witnessed_gen(), 2);

        // Stale server gen 1 is rejected!
        assert_eq!(
            p.plan_reconnect(id, 1, Some(100), 180, &[0, 100]),
            LineageSplicePlan::RejectStaleGeneration {
                server_gen: 1,
                witnessed_gen: 2,
            }
        );

        // Cursor at 240 > diverge 210 on gen 3 -> rewinds to checkpoint 200 (ignoring 230 > 210).
        assert_eq!(
            p.plan_reconnect(id, 3, Some(210), 240, &[0, 100, 200, 230]),
            LineageSplicePlan::RewindToCheckpoint {
                checkpoint_offset: 200,
                diverge_offset: 210,
                clamped_rewind_dist: 40,
                new_generation: 3,
            }
        );
    }
}
