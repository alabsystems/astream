//! `Autopilot=Cruise` 6-phase work-rotation & anti-stall repetition stopper.

#[cfg(clean_islands)]
#[path = "autopilot_cruise_wheel_island.rs"]
mod autopilot_cruise_wheel_island;
#[cfg(clean_islands)]
pub use autopilot_cruise_wheel_island::{cruise_empty_streak_clamp, cruise_phase_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_phase_clamp(phase: u64) -> u64 {
    if phase < 5 {
        phase
    } else {
        5
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_empty_streak_clamp(streak: u64) -> u64 {
    if streak < 6 {
        streak
    } else {
        6
    }
}

contract_fn! {
    #[must_use]
    pub const fn cruise_reply_not_repeated(same_reply_count: u64) -> bool
    clauses [ensures result == (same_reply_count < 2)]
    {
        same_reply_count < 2
    }
}

#[inline]
#[must_use]
pub const fn cruise_should_continue(same_reply_count: u64, empty_streak: u64) -> bool {
    cruise_reply_not_repeated(same_reply_count) && empty_streak < 6
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruisePhase {
    WidestCheck,
    HostileReview,
    OutOfScopeItems,
    MeasureAgainstMain,
    NextOpenIssue,
    LandSessionWork,
}

impl CruisePhase {
    #[must_use]
    pub const fn from_index(idx: u64) -> Self {
        match cruise_phase_clamp(idx) {
            0 => Self::WidestCheck,
            1 => Self::HostileReview,
            2 => Self::OutOfScopeItems,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionWork,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseAction {
    PromptPhase(CruisePhase),
    ParkUntilWorkOrPerson,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AutopilotCruiseWheel {
    phase_idx: u64,
    empty_streak: u64,
    last_empty_digest: Option<u64>,
    same_reply_count: u64,
}

impl AutopilotCruiseWheel {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            phase_idx: 0,
            empty_streak: 0,
            last_empty_digest: None,
            same_reply_count: 0,
        }
    }

    #[must_use]
    pub const fn phase_idx(&self) -> u64 {
        self.phase_idx
    }

    #[must_use]
    pub const fn empty_streak(&self) -> u64 {
        self.empty_streak
    }

    #[must_use]
    pub const fn last_empty_digest(&self) -> Option<u64> {
        self.last_empty_digest
    }

    #[must_use]
    pub const fn same_reply_count(&self) -> u64 {
        self.same_reply_count
    }

    pub fn observe_turn(&mut self, did_work: bool, reply_digest: u64) -> CruiseAction {
        if did_work {
            self.empty_streak = 0;
            self.last_empty_digest = None;
            self.same_reply_count = 0;
        } else {
            self.empty_streak = cruise_empty_streak_clamp(self.empty_streak.saturating_add(1));
            if self.last_empty_digest == Some(reply_digest) {
                self.same_reply_count = self.same_reply_count.saturating_add(1);
            } else {
                self.last_empty_digest = Some(reply_digest);
                self.same_reply_count = 1;
            }
        }
        if !cruise_should_continue(self.same_reply_count, self.empty_streak) {
            return CruiseAction::ParkUntilWorkOrPerson;
        }
        let phase = CruisePhase::from_index(self.phase_idx);
        self.phase_idx = if self.phase_idx < 5 {
            cruise_phase_clamp(self.phase_idx + 1)
        } else {
            0
        };
        CruiseAction::PromptPhase(phase)
    }

    pub fn notify_person_turn(&mut self) {
        self.empty_streak = 0;
        self.last_empty_digest = None;
        self.same_reply_count = 0;
    }
}

impl Default for AutopilotCruiseWheel {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_all_six_phases_and_parks_on_duplicate_empty_or_six_empty_in_a_row() {
        let mut w = AutopilotCruiseWheel::new();
        assert_eq!(w.phase_idx(), 0);
        assert_eq!(
            w.observe_turn(true, 1),
            CruiseAction::PromptPhase(CruisePhase::WidestCheck)
        );
        assert_eq!(
            w.observe_turn(true, 1),
            CruiseAction::PromptPhase(CruisePhase::HostileReview)
        );
        assert_eq!(
            w.observe_turn(false, 99),
            CruiseAction::PromptPhase(CruisePhase::OutOfScopeItems)
        );
        assert_eq!(w.empty_streak(), 1);
        assert_eq!(w.last_empty_digest(), Some(99));
        assert_eq!(w.same_reply_count(), 1);
        assert_eq!(
            w.observe_turn(false, 99),
            CruiseAction::ParkUntilWorkOrPerson
        );

        w.notify_person_turn();
        for d in 10..15 {
            assert!(matches!(
                w.observe_turn(false, d),
                CruiseAction::PromptPhase(_)
            ));
        }
        assert_eq!(
            w.observe_turn(false, 15),
            CruiseAction::ParkUntilWorkOrPerson
        );
        assert_eq!(cruise_phase_clamp(99), 5);
        assert_eq!(cruise_empty_streak_clamp(99), 6);
    }
}
