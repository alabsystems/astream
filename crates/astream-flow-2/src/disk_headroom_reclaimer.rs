//! Shared-volume build headroom gate & bounded cache-eviction tracker (`disk_free_mb=`,
//! `await sys 'free>=room'`).

#[cfg(clean_islands)]
#[path = "disk_headroom_reclaimer_island.rs"]
mod disk_headroom_reclaimer_island;
#[cfg(clean_islands)]
pub use disk_headroom_reclaimer_island::{
    headroom_eviction_round_clamp, headroom_reclaimed_advance,
};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn headroom_reclaimed_advance(prev_reclaimed: u64, candidate_reclaimed: u64) -> u64 {
    if prev_reclaimed < candidate_reclaimed {
        candidate_reclaimed
    } else {
        prev_reclaimed
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn headroom_eviction_round_clamp(round: u64) -> u64 {
    if round < 16 {
        round
    } else {
        16
    }
}

contract_fn! {
    #[must_use]
    pub const fn headroom_has_room(free_mb: u64, room_floor_mb: u64) -> bool
    clauses [ensures result == (room_floor_mb <= free_mb)]
    {
        room_floor_mb <= free_mb
    }
}

pub const MAX_DISK_EVICTION_ROUNDS: u64 = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiskAdmission {
    AdmitBuild { free_mb: u64, headroom_mb: u64 },
    WaitReclaim { deficit_mb: u64, next_round: u64 },
    ExhaustedFailClosed { deficit_mb: u64, reclaimed_mb: u64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiskHeadroomReclaimer {
    room_floor_mb: u64,
    reclaimed_mb: u64,
    eviction_round: u64,
}

impl DiskHeadroomReclaimer {
    #[must_use]
    pub const fn new(room_floor_mb: u64) -> Self {
        Self {
            room_floor_mb,
            reclaimed_mb: 0,
            eviction_round: 0,
        }
    }

    #[must_use]
    pub const fn room_floor_mb(&self) -> u64 {
        self.room_floor_mb
    }

    #[must_use]
    pub const fn reclaimed_mb(&self) -> u64 {
        self.reclaimed_mb
    }

    #[must_use]
    pub const fn eviction_round(&self) -> u64 {
        self.eviction_round
    }

    pub fn record_reclaim(&mut self, newly_freed_mb: u64) {
        let total = self.reclaimed_mb.saturating_add(newly_freed_mb);
        self.reclaimed_mb = headroom_reclaimed_advance(self.reclaimed_mb, total);
        let next_round = self.eviction_round.saturating_add(1);
        self.eviction_round = headroom_eviction_round_clamp(next_round);
    }

    pub fn reset_rounds_on_room(&mut self, free_mb: u64) {
        if headroom_has_room(free_mb, self.room_floor_mb) {
            self.eviction_round = 0;
        }
    }

    #[must_use]
    pub const fn evaluate(&self, free_mb: u64) -> DiskAdmission {
        if headroom_has_room(free_mb, self.room_floor_mb) {
            DiskAdmission::AdmitBuild {
                free_mb,
                headroom_mb: free_mb.saturating_sub(self.room_floor_mb),
            }
        } else {
            let deficit_mb = self.room_floor_mb.saturating_sub(free_mb);
            if self.eviction_round < MAX_DISK_EVICTION_ROUNDS {
                DiskAdmission::WaitReclaim {
                    deficit_mb,
                    next_round: self.eviction_round.saturating_add(1),
                }
            } else {
                DiskAdmission::ExhaustedFailClosed {
                    deficit_mb,
                    reclaimed_mb: self.reclaimed_mb,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_when_free_meets_room_floor_and_fails_closed_after_max_rounds() {
        let mut r = DiskHeadroomReclaimer::new(8192);
        assert_eq!(
            r.evaluate(10240),
            DiskAdmission::AdmitBuild {
                free_mb: 10240,
                headroom_mb: 2048,
            }
        );
        assert_eq!(
            r.evaluate(6000),
            DiskAdmission::WaitReclaim {
                deficit_mb: 2192,
                next_round: 1,
            }
        );
        for _ in 0..MAX_DISK_EVICTION_ROUNDS {
            r.record_reclaim(100);
        }
        assert_eq!(r.eviction_round(), MAX_DISK_EVICTION_ROUNDS);
        assert_eq!(r.reclaimed_mb(), 1600);
        assert_eq!(
            r.evaluate(7600),
            DiskAdmission::ExhaustedFailClosed {
                deficit_mb: 592,
                reclaimed_mb: 1600,
            }
        );
        r.reset_rounds_on_room(9000);
        assert_eq!(r.eviction_round(), 0);
    }

    #[test]
    fn twin_grid_matches_clean_definitions() {
        let mut got_adv = String::new();
        let mut got_clamp = String::new();
        for a in [0u64, 1, 2] {
            for b in [0u64, 1, 2] {
                got_adv.push_str(&headroom_reclaimed_advance(a, b).to_string());
            }
        }
        assert_eq!(got_adv, "012112222");
        for r in [0u64, 0, 0, 0, 1, 1, 0, 1, 2] {
            got_clamp.push_str(&headroom_eviction_round_clamp(r).to_string());
        }
        assert_eq!(got_clamp, "000011012");
        assert_eq!(headroom_eviction_round_clamp(99), 16);
    }
}
