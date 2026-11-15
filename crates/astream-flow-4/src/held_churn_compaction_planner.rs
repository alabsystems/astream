//! `<log>.held` churn-triggered compaction & `SLACK_DIV = 4` give-up planner.

#[cfg(clean_islands)]
#[path = "held_churn_compaction_planner_island.rs"]
mod held_churn_compaction_planner_island;
#[cfg(clean_islands)]
pub use held_churn_compaction_planner_island::{held_live_bytes_clamp, held_rewrite_epoch_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_live_bytes_clamp(live_bytes: u64) -> u64 {
    if live_bytes < 1_073_741_824 {
        live_bytes
    } else {
        1_073_741_824
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_rewrite_epoch_advance(prev_epoch: u64, next_epoch: u64) -> u64 {
    if prev_epoch < next_epoch {
        next_epoch
    } else {
        prev_epoch
    }
}

contract_fn! {
    #[must_use]
    pub const fn held_needs_rewrite(twice_live_bytes: u64, file_bytes: u64) -> bool
    clauses [ensures result == ((twice_live_bytes < file_bytes))]
    {
        twice_live_bytes < file_bytes
    }
}

pub const HELD_SLACK_DIV: u64 = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HeldChurnCompactionPlanner {
    live_bytes: u64,
    file_bytes: u64,
    rewrite_epoch: u64,
}

impl HeldChurnCompactionPlanner {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            live_bytes: 0,
            file_bytes: 0,
            rewrite_epoch: 0,
        }
    }

    #[must_use]
    pub const fn live_bytes(&self) -> u64 {
        self.live_bytes
    }

    #[must_use]
    pub const fn file_bytes(&self) -> u64 {
        self.file_bytes
    }

    #[must_use]
    pub const fn rewrite_epoch(&self) -> u64 {
        self.rewrite_epoch
    }

    /// Target retained ceiling after giving up at least `max_bytes / 4` (`SLACK_DIV = 4`)
    /// whenever `live_bytes > max_bytes`.
    #[must_use]
    pub const fn target_bytes_after_giveup(live_bytes: u64, max_bytes: u64) -> u64 {
        if live_bytes <= max_bytes {
            live_bytes
        } else {
            let slack = max_bytes / HELD_SLACK_DIV;
            max_bytes.saturating_sub(slack)
        }
    }

    pub fn observe_append(&mut self, live_bytes: u64, appended_bytes: u64) -> bool {
        self.live_bytes = held_live_bytes_clamp(live_bytes);
        self.file_bytes = self.file_bytes.saturating_add(appended_bytes);
        let twice_live = self.live_bytes.saturating_mul(2);
        held_needs_rewrite(twice_live, self.file_bytes)
    }

    pub fn complete_rewrite(&mut self) -> u64 {
        self.file_bytes = self.live_bytes;
        let next = self.rewrite_epoch.saturating_add(1);
        self.rewrite_epoch = held_rewrite_epoch_advance(self.rewrite_epoch, next);
        self.rewrite_epoch
    }
}

impl Default for HeldChurnCompactionPlanner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrites_only_past_twice_live_bytes_and_gives_up_quarter_slack() {
        assert_eq!(
            HeldChurnCompactionPlanner::target_bytes_after_giveup(900, 1000),
            900
        );
        assert_eq!(
            HeldChurnCompactionPlanner::target_bytes_after_giveup(1001, 1000),
            750
        );

        let mut p = HeldChurnCompactionPlanner::new();
        assert!(!p.observe_append(1000, 1000));
        assert!(!p.observe_append(1000, 1000));
        assert!(p.observe_append(1000, 1));
        assert_eq!(p.live_bytes(), 1000);
        assert_eq!(p.file_bytes(), 2001);
        assert_eq!(p.complete_rewrite(), 1);
        assert_eq!(p.rewrite_epoch(), 1);
    }
}
