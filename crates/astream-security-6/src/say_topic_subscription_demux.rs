// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Demand-driven `/f/<F>/pub/*/*/say/>` subscription & per-session `topic add <topic>` demux
//! (`docs/DESIGN-aterm-fabric.md` §5.1 lines 956–966, aterm `357107312` & `4454b5498`;
//! `Astream.Broker.TlaSayTopicSubscriptionDemux`).
//!
//! Enforces `aterm-link`'s `say` broadcast routing contract:
//! - Default topic set is empty (`0` deliveries when empty),
//! - The bridge holds the fleet-wide `/f/<F>/pub/*/*/say/>` subscription ONLY while `>= 1`
//!   hosted session has at least one active topic (`should_hold_fleet_say_sub() == true`),
//!   resuming from the lowest cursor owed across active bindings,
//! - A bare `say` lacking a session owner face (`has_session_owner == false`) is refused as unroutable.

#[cfg(clean_islands)]
#[path = "say_topic_subscription_demux_island.rs"]
mod say_topic_subscription_demux_island;
#[cfg(clean_islands)]
pub use say_topic_subscription_demux_island::{
    say_topic_cursor_advance_b132, say_topic_subs_clamp_b132,
};

/// Maximum concurrent `(session_tag, topic_hash)` bindings per bridge (`64` stack slots).
pub const MAX_SAY_TOPIC_BINDINGS: usize = 64;

#[cfg(not(clean_islands))]
/// Clamp active `(session, topic)` binding count to `max_subs`.
#[must_use]
pub const fn say_topic_subs_clamp_b132(cand_subs: u64, max_subs: u64) -> u64 {
    if cand_subs < max_subs {
        cand_subs
    } else {
        max_subs
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance highest `say` bus offset fanned in.
#[must_use]
pub const fn say_topic_cursor_advance_b132(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}

contract_fn! {
    /// True iff `active_topic_bindings > 0` (bridge must keep `/f/<F>/pub/*/*/say/>` open).
    #[must_use]
    pub const fn say_hold_fleet_sub_b132(active_topic_bindings: u64) -> bool
    clauses [ensures result == (active_topic_bindings > 0)]
    {
        active_topic_bindings > 0
    }
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
struct TopicBinding {
    sid_tag: u64,
    topic_hash: u64,
    owed_from_offset: u64,
}

/// Pure stack `say` topic router and fleet-subscription lifecycle controller.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy)]
pub struct SayTopicSubscriptionDemux {
    bindings: [Option<TopicBinding>; MAX_SAY_TOPIC_BINDINGS],
    active_count: u64,
    fanned_hwm: u64,
}

impl Default for SayTopicSubscriptionDemux {
    fn default() -> Self {
        Self::new()
    }
}

impl SayTopicSubscriptionDemux {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bindings: [None; MAX_SAY_TOPIC_BINDINGS],
            active_count: 0,
            fanned_hwm: 0,
        }
    }

    /// True iff at least one hosted session holds a topic (`aterm 4454b5498`).
    #[must_use]
    pub fn should_hold_fleet_say_sub(&self) -> bool {
        say_hold_fleet_sub_b132(self.active_count)
    }

    /// Lowest `owed_from_offset` across all active topic bindings, or `None` when idle.
    #[must_use]
    pub fn resume_from_lowest_cursor(&self) -> Option<u64> {
        let mut lowest: Option<u64> = None;
        let mut rest = self.bindings.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if let Some(b) = slot {
                lowest = Some(match lowest {
                    None => b.owed_from_offset,
                    Some(cur) => {
                        if b.owed_from_offset < cur {
                            b.owed_from_offset
                        } else {
                            cur
                        }
                    }
                });
            }
            rest = tail;
        }
        lowest
    }

    fn recount(&mut self) {
        let mut n = 0u64;
        let mut rest = self.bindings.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if slot.is_some() {
                n = n.saturating_add(1);
            }
            rest = tail;
        }
        self.active_count = say_topic_subs_clamp_b132(n, MAX_SAY_TOPIC_BINDINGS as u64);
    }

    /// Register `topic add <topic>` for `sid_tag` starting at `start_offset`.
    pub fn add_topic(&mut self, sid_tag: u64, topic_hash: u64, start_offset: u64) -> bool {
        // Idempotent if already present.
        let mut check = self.bindings.as_slice();
        while let &[slot, ref tail @ ..] = check {
            if let Some(b) = slot {
                if b.sid_tag == sid_tag && b.topic_hash == topic_hash {
                    return true;
                }
            }
            check = tail;
        }
        let mut idx = 0usize;
        while idx < MAX_SAY_TOPIC_BINDINGS {
            if let Some(slot) = self.bindings.get_mut(idx) {
                if slot.is_none() {
                    *slot = Some(TopicBinding {
                        sid_tag,
                        topic_hash,
                        owed_from_offset: start_offset,
                    });
                    self.recount();
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        false
    }

    /// Remove all topics for a closed session (or one topic if `Some(topic_hash)`).
    pub fn remove_topics(&mut self, sid_tag: u64, only_topic: Option<u64>) {
        let mut idx = 0usize;
        while idx < MAX_SAY_TOPIC_BINDINGS {
            if let Some(slot) = self.bindings.get_mut(idx) {
                if let Some(b) = *slot {
                    let hit = b.sid_tag == sid_tag
                        && match only_topic {
                            None => true,
                            Some(th) => b.topic_hash == th,
                        };
                    if hit {
                        *slot = None;
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        self.recount();
    }

    /// Fan in a `say` record at `offset` on `topic_hash` (`has_session_owner` must be `true`); returns count of sessions delivered.
    pub fn fan_in_say(
        &mut self,
        has_session_owner: bool,
        topic_hash: u64,
        offset: u64,
    ) -> Option<u64> {
        if !has_session_owner {
            return None; // Bare bridge-internal say has no session owner face and is unroutable!
        }
        let mut delivered = 0u64;
        let next_off = offset.saturating_add(1);
        let mut idx = 0usize;
        while idx < MAX_SAY_TOPIC_BINDINGS {
            if let Some(slot) = self.bindings.get_mut(idx) {
                if let Some(mut b) = *slot {
                    if b.topic_hash == topic_hash && offset >= b.owed_from_offset {
                        b.owed_from_offset = next_off;
                        *slot = Some(b);
                        delivered = delivered.saturating_add(1);
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        self.fanned_hwm = say_topic_cursor_advance_b132(self.fanned_hwm, next_off);
        Some(delivered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_fleet_sub_only_while_topics_exist_resumes_lowest_and_rejects_ownerless_say() {
        let mut d = SayTopicSubscriptionDemux::new();
        assert!(!d.should_hold_fleet_say_sub());
        assert_eq!(d.resume_from_lowest_cursor(), None);
        assert_eq!(d.fan_in_say(false, 0x11, 5), None);

        assert!(d.add_topic(1, 0xAA, 20));
        assert!(d.add_topic(2, 0xAA, 12));
        assert!(d.should_hold_fleet_say_sub());
        assert_eq!(d.resume_from_lowest_cursor(), Some(12));

        // Offset 15 delivers to session 2 (>= 12) but skips session 1 (< 20)!
        assert_eq!(d.fan_in_say(true, 0xAA, 15), Some(1));
        assert_eq!(d.resume_from_lowest_cursor(), Some(16));

        d.remove_topics(1, None);
        d.remove_topics(2, Some(0xAA));
        assert!(!d.should_hold_fleet_say_sub());
    }
}
