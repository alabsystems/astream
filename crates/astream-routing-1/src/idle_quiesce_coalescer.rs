// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cosmetic-redraw-aware idle quiescence coalescer (`Astream.Pump.TlaIdleQuiesceCoalescer`).
//!
//! Suppresses duplicate `aspump` quiescence wakeups when a terminal redraws an identical screen
//! digest (such as TUI clock/cursor-blink refreshes) up to `max_suppressed` consecutive ticks,
//! while guaranteeing liveness once `max_suppressed` elapses or the screen digest changes.

#[cfg(clean_islands)]
#[path = "idle_quiesce_coalescer_island.rs"]
mod idle_quiesce_coalescer_island;
#[cfg(clean_islands)]
pub use idle_quiesce_coalescer_island::{quiesce_suppressed_clamp, quiesce_woken_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn quiesce_woken_advance(cur_woken: u64, cand_woken: u64) -> u64 {
    if cur_woken < cand_woken {
        cand_woken
    } else {
        cur_woken
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn quiesce_suppressed_clamp(cand_suppressed: u64, max_suppressed: u64) -> u64 {
    if cand_suppressed < max_suppressed {
        cand_suppressed
    } else {
        max_suppressed
    }
}

contract_fn! {
    /// Verified check whether `latest_offset` has moved strictly past `last_woken_offset`,
    /// linked via `clean-kernel-defeq` to `quiesce_has_unseen_output_isl`.
    #[must_use]
    pub const fn quiesce_has_unseen_output(last_woken_offset: u64, latest_offset: u64) -> bool
    clauses [ensures result == (last_woken_offset < latest_offset)]
    {
        last_woken_offset < latest_offset
    }
}

/// Coalescer decision on an idle debounce tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuiesceCoalesceVerdict {
    /// No new output offsets arrived since the last wake.
    NothingNew,
    /// Identical screen digest suppressed (`suppressed_ticks <= max_suppressed`).
    SuppressedCosmetic { suppressed_ticks: u64 },
    /// Agent should be woken at `wake_offset`.
    WakeAgent { wake_offset: u64 },
}

/// Stateful quiescence coalescer for `astream-pump`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdleQuiesceCoalescer {
    last_woken_offset: u64,
    last_woken_screen_digest: Option<u64>,
    suppressed_ticks: u64,
    max_suppressed: u64,
}

impl IdleQuiesceCoalescer {
    #[must_use]
    pub const fn new(max_suppressed: u64) -> Self {
        let cap = if max_suppressed == 0 {
            4
        } else {
            max_suppressed
        };
        Self {
            last_woken_offset: 0,
            last_woken_screen_digest: None,
            suppressed_ticks: 0,
            max_suppressed: cap,
        }
    }

    #[must_use]
    pub const fn last_woken_offset(&self) -> u64 {
        self.last_woken_offset
    }

    #[must_use]
    pub const fn suppressed_ticks(&self) -> u64 {
        self.suppressed_ticks
    }

    /// Evaluate an idle settle boundary at `(latest_offset, screen_digest)`.
    pub fn evaluate_quiesce(
        &mut self,
        latest_offset: u64,
        screen_digest: u64,
    ) -> QuiesceCoalesceVerdict {
        if !quiesce_has_unseen_output(self.last_woken_offset, latest_offset) {
            return QuiesceCoalesceVerdict::NothingNew;
        }
        if self.last_woken_screen_digest == Some(screen_digest)
            && self.suppressed_ticks < self.max_suppressed
        {
            let cand = self.suppressed_ticks.saturating_add(1);
            self.suppressed_ticks = quiesce_suppressed_clamp(cand, self.max_suppressed);
            return QuiesceCoalesceVerdict::SuppressedCosmetic {
                suppressed_ticks: self.suppressed_ticks,
            };
        }
        self.last_woken_offset = quiesce_woken_advance(self.last_woken_offset, latest_offset);
        self.last_woken_screen_digest = Some(screen_digest);
        self.suppressed_ticks = 0;
        QuiesceCoalesceVerdict::WakeAgent {
            wake_offset: self.last_woken_offset,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_unchanged_screen_redraws_up_to_cap_then_wakes() {
        let mut q = IdleQuiesceCoalescer::new(2);
        assert_eq!(
            q.evaluate_quiesce(0, 0xAA),
            QuiesceCoalesceVerdict::NothingNew
        );
        assert_eq!(
            q.evaluate_quiesce(10, 0xAA),
            QuiesceCoalesceVerdict::WakeAgent { wake_offset: 10 }
        );
        // Cosmetic cursor-blink redraws leaving screen digest 0xAA unchanged are suppressed twice:
        assert_eq!(
            q.evaluate_quiesce(11, 0xAA),
            QuiesceCoalesceVerdict::SuppressedCosmetic {
                suppressed_ticks: 1
            }
        );
        assert_eq!(
            q.evaluate_quiesce(12, 0xAA),
            QuiesceCoalesceVerdict::SuppressedCosmetic {
                suppressed_ticks: 2
            }
        );
        // Third tick flushes wake so liveness is preserved!
        assert_eq!(
            q.evaluate_quiesce(13, 0xAA),
            QuiesceCoalesceVerdict::WakeAgent { wake_offset: 13 }
        );
    }
}
