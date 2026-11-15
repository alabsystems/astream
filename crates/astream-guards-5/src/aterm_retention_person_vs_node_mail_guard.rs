// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` person-mail 7-day hold vs node-inbox group-commit release guard
//! (`evidence/manifest.toml` `broker.retention-rules` / `aterm_retention`;
//! `Astream.Broker.TlaAtermRetentionPersonVsNodeMailGuard`).
//!
//! Enforces the critical `aterm` inbox retention boundary (`tests/fixtures/aterm-broker.retain`):
//! - A node's inbox mail (`is_person_lane == false`) is released at the next retention cut once
//!   its matching node reader group commits past `mail_offset` (`node_group_commit > mail_offset`)
//!   OR its `max_age_ms` expires,
//! - A PERSON's unread mail (`is_person_lane == true`) MUST NEVER be released early by a node
//!   inbox group commit — only explicit person-lane commit (`person_group_commit > mail_offset`),
//!   7-day age expiry (`age_ms >= person_max_age_ms`), or class byte-cap slack eviction (`SLACK_DIV = 4`)
//!   releases it!

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "aterm_retention_person_vs_node_mail_guard_island.rs"]
mod aterm_retention_person_vs_node_mail_guard_island;
#[cfg(clean_islands)]
pub use aterm_retention_person_vs_node_mail_guard_island::{
    held_class_bytes_clamp_b154, held_class_floor_advance_b154,
};

/// 7-day person-mail retention horizon in milliseconds (`604_800_000 ms`).
pub const PERSON_MAIL_MAX_AGE_MS: u64 = 7 * 24 * 60 * 60 * 1_000;

#[cfg(not(clean_islands))]
/// Clamp held class byte usage to `class_max_bytes`.
#[must_use]
pub const fn held_class_bytes_clamp_b154(cand_bytes: u64, class_max_bytes: u64) -> u64 {
    if cand_bytes < class_max_bytes {
        cand_bytes
    } else {
        class_max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Advance hold class floor monotonically when byte/age bounds give up oldest records.
#[must_use]
pub const fn held_class_floor_advance_b154(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}

contract_fn! {
    /// True iff `mail_offset` is still unread under its OWN lane's group commit and within `max_age_ms`.
    #[must_use]
    pub const fn aterm_mail_must_hold_b154(
        is_person_lane: bool,
        mail_offset: u64,
        person_group_commit: u64,
        node_group_commit: u64,
        age_ms: u64,
        max_age_ms: u64,
    ) -> bool
    clauses [ensures result == (age_ms < max_age_ms && ((is_person_lane && person_group_commit <= mail_offset) || (!is_person_lane && node_group_commit <= mail_offset)))]
    {
        let unread_in_own_lane = if is_person_lane {
            person_group_commit <= mail_offset
        } else {
            node_group_commit <= mail_offset
        };
        age_ms < max_age_ms && unread_in_own_lane
    }
}

/// Retention planning verdict for an inbox record below the prefix cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtermMailRetentionDecision {
    CarryHeldUnread {
        mail_offset: u64,
        class_floor: u64,
    },
    ReleaseReadByOwnGroup {
        mail_offset: u64,
    },
    EvictOldestRaiseClassFloor {
        evicted_offset: u64,
        new_class_floor: u64,
        slack_target_bytes: u64,
    },
}

/// Evaluates `aterm` person-mail vs node-mail hold rules and `SLACK_DIV = 4` byte-cap eviction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtermMailHoldGuard {
    class_max_bytes: u64,
    class_floor: u64,
}

impl AtermMailHoldGuard {
    #[must_use]
    pub const fn new(class_max_bytes: u64) -> Self {
        Self {
            class_max_bytes,
            class_floor: 0,
        }
    }

    /// Evaluate whether `mail_offset` should be carried, released as read, or evicted for byte slack.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate_mail(
        &mut self,
        is_person_lane: bool,
        mail_offset: u64,
        person_group_commit: u64,
        node_group_commit: u64,
        age_ms: u64,
        max_age_ms: u64,
        projected_class_bytes: u64,
    ) -> AtermMailRetentionDecision {
        if !aterm_mail_must_hold_b154(
            is_person_lane,
            mail_offset,
            person_group_commit,
            node_group_commit,
            age_ms,
            max_age_ms,
        ) {
            if age_ms >= max_age_ms {
                let next_floor = mail_offset.saturating_add(1);
                self.class_floor = held_class_floor_advance_b154(self.class_floor, next_floor);
                return AtermMailRetentionDecision::EvictOldestRaiseClassFloor {
                    evicted_offset: mail_offset,
                    new_class_floor: self.class_floor,
                    slack_target_bytes: held_class_bytes_clamp_b154(
                        self.class_max_bytes
                            .saturating_sub(self.class_max_bytes / 4),
                        self.class_max_bytes,
                    ),
                };
            }
            return AtermMailRetentionDecision::ReleaseReadByOwnGroup { mail_offset };
        }
        if projected_class_bytes > self.class_max_bytes {
            let next_floor = mail_offset.saturating_add(1);
            self.class_floor = held_class_floor_advance_b154(self.class_floor, next_floor);
            let slack_target = self
                .class_max_bytes
                .saturating_sub(self.class_max_bytes / 4);
            return AtermMailRetentionDecision::EvictOldestRaiseClassFloor {
                evicted_offset: mail_offset,
                new_class_floor: self.class_floor,
                slack_target_bytes: held_class_bytes_clamp_b154(slack_target, self.class_max_bytes),
            };
        }
        AtermMailRetentionDecision::CarryHeldUnread {
            mail_offset,
            class_floor: self.class_floor,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_person_mail_despite_node_group_commits_until_day_7_or_person_read() {
        let mut g = AtermMailHoldGuard::new(4096);
        // Person mail at offset 10, node_group_commit = 500 (node read everything!), day 5 -> STILL HELD!
        assert_eq!(
            g.evaluate_mail(
                true,
                10,
                0,
                500,
                5 * 86_400_000,
                PERSON_MAIL_MAX_AGE_MS,
                512
            ),
            AtermMailRetentionDecision::CarryHeldUnread {
                mail_offset: 10,
                class_floor: 0,
            }
        );
        // Node mail at offset 12, node_group_commit = 500 -> released!
        assert_eq!(
            g.evaluate_mail(false, 12, 0, 500, 1_000, PERSON_MAIL_MAX_AGE_MS, 512),
            AtermMailRetentionDecision::ReleaseReadByOwnGroup { mail_offset: 12 }
        );
        // Byte overflow evicts oldest and targets 75% (`SLACK_DIV = 4`) = 3072 bytes:
        assert_eq!(
            g.evaluate_mail(true, 10, 0, 500, 1_000, PERSON_MAIL_MAX_AGE_MS, 5000),
            AtermMailRetentionDecision::EvictOldestRaiseClassFloor {
                evicted_offset: 10,
                new_class_floor: 11,
                slack_target_bytes: 3072,
            }
        );
    }
}
