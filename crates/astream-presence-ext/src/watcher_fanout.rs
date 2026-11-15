// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded read-only terminal watcher registry and slow-watcher lag shedding
//! (`DESIGN-aterm-fabric.md` §4.2 line 4041, `Astream.Presence.TlaWatcherFanout`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "watcher_fanout_island.rs"]
mod watcher_fanout_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn watcher_count_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn watcher_cursor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use watcher_fanout_island::{watcher_count_clamp, watcher_cursor_advance};

/// Maximum concurrent read-only watchers attached to one terminal session.
pub const MAX_SESSION_WATCHERS: u64 = 64;

contract_fn! {
    /// Verified lag check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `watcher_within_lag_isl`.
    #[must_use]
    pub const fn watcher_within_lag(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Fast-forward gap notice emitted to a slow watcher instead of blocking the live PTY driver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WatcherLagGap {
    pub watcher_sid: String,
    pub skipped_from: u64,
    pub fast_forwarded_to: u64,
}

/// Non-blocking watcher cursor table.
#[derive(Debug, Clone)]
pub struct WatcherFanoutRegistry {
    max_watchers: u64,
    max_lag_records: u64,
    cursors: BTreeMap<String, u64>,
}

impl Default for WatcherFanoutRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl WatcherFanoutRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self::with_limits(MAX_SESSION_WATCHERS, 256)
    }

    #[must_use]
    pub fn with_limits(max_watchers: u64, max_lag_records: u64) -> Self {
        let cap = watcher_count_clamp(max_watchers, MAX_SESSION_WATCHERS);
        Self {
            max_watchers: if cap == 0 { 1 } else { cap },
            max_lag_records: if max_lag_records == 0 {
                1
            } else {
                max_lag_records
            },
            cursors: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.cursors.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cursors.is_empty()
    }

    pub fn attach_watcher(&mut self, sid: &str, start_offset: u64) -> bool {
        if sid.is_empty() {
            return false;
        }
        if !self.cursors.contains_key(sid) && (self.cursors.len() as u64) >= self.max_watchers {
            return false;
        }
        let mut owned = String::new();
        owned.push_str(sid);
        self.cursors.insert(owned, start_offset);
        true
    }

    pub fn ack_watcher(&mut self, sid: &str, new_cursor: u64) -> Option<u64> {
        let cur = self.cursors.get_mut(sid)?;
        *cur = watcher_cursor_advance(*cur, new_cursor);
        Some(*cur)
    }

    /// Fast-forwards any watcher lagging more than `max_lag_records` behind `session_head` to
    /// `keyframe_offset`, returning explicit `WatcherLagGap` notices.
    pub fn shed_lagging_watchers(
        &mut self,
        session_head: u64,
        keyframe_offset: u64,
    ) -> Vec<WatcherLagGap> {
        let eff_kf = if keyframe_offset > session_head {
            session_head
        } else {
            keyframe_offset
        };
        let mut gaps = Vec::new();
        for (sid, cur) in &mut self.cursors {
            let lag = session_head.saturating_sub(*cur);
            if !watcher_within_lag(self.max_lag_records, lag) && *cur < eff_kf {
                let old = *cur;
                *cur = watcher_cursor_advance(*cur, eff_kf);
                gaps.push(WatcherLagGap {
                    watcher_sid: sid.clone(),
                    skipped_from: old,
                    fast_forwarded_to: *cur,
                });
            }
        }
        gaps
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slow_watcher_is_fast_forwarded_to_keyframe_with_gap_while_caught_up_watcher_continues() {
        let mut reg = WatcherFanoutRegistry::with_limits(8, 50);
        assert!(reg.attach_watcher("@s-fast", 90));
        assert!(reg.attach_watcher("@s-slow", 10));

        let gaps = reg.shed_lagging_watchers(100, 80);
        assert_eq!(
            gaps,
            vec![WatcherLagGap {
                watcher_sid: "@s-slow".to_owned(),
                skipped_from: 10,
                fast_forwarded_to: 80,
            }]
        );
        assert_eq!(reg.ack_watcher("@s-fast", 95), Some(95));
    }
}
