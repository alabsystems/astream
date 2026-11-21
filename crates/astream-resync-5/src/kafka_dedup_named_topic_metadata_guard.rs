// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kafka Metadata/Fetch repeated-topic deduplication & named-topic non-widening guard
//! (`Astream.Kafka.TlaKafkaDedupNamedTopicMetadataGuard`).
//!
//! Enforces the two Kafka wire-protocol scoping invariants:
//! 1. **No named-topic widening**: ONLY an explicit `NULL` topics array (`topics_array_is_null`)
//!    enumerates all broker topics; an empty array `[]` returns `0` topics, and a named list
//!    `["orders"]` returns ONLY `"orders"` (or `UNKNOWN_TOPIC_OR_PARTITION`), never widening to
//!    unrelated topics!
//! 2. **No quadratic duplicate amplification**: repeated topic names in a single request are
//!    answered at most once (`emitted_unique_topics <= requested_topics`).

#[cfg(clean_islands)]
#[path = "kafka_dedup_named_topic_metadata_guard_island.rs"]
mod kafka_dedup_named_topic_metadata_guard_island;
#[cfg(clean_islands)]
pub use kafka_dedup_named_topic_metadata_guard_island::{
    metadata_response_gen_advance_b141, metadata_unique_topics_clamp_b141,
};

#[cfg(not(clean_islands))]
/// Clamp deduplicated topic answer count to `requested_count`.
#[must_use]
pub const fn metadata_unique_topics_clamp_b141(unique_count: u64, requested_count: u64) -> u64 {
    if unique_count < requested_count {
        unique_count
    } else {
        requested_count
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the metadata response generation counter.
#[must_use]
pub const fn metadata_response_gen_advance_b141(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// Enumeration of ALL broker topics is authorized ONLY when the wire `topics` nullable array
    /// is explicitly `NULL` (`topics_array_is_null && requested_count == 0`).
    #[must_use]
    pub const fn metadata_all_topics_authorized_b141(
        topics_array_is_null: bool,
        requested_count: u64,
    ) -> bool
    clauses [ensures result == (topics_array_is_null && requested_count == 0)]
    {
        topics_array_is_null && requested_count == 0
    }
}

/// Resolution plan for a Kafka `Metadata` request's `topics` field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetadataScopePlan {
    /// Wire `topics == null` (`-1` length): enumerate all broker topics.
    EnumerateAllBrokerTopics { response_gen: u64 },
    /// Wire `topics == []` (`0` length): return an empty topic metadata list!
    EmptyTopicList { response_gen: u64 },
    /// Wire `topics == [t1, ...]` (`requested_count >= 1`): answer ONLY the deduplicated named set!
    NamedUniqueTopicsOnly {
        emitted_unique_topics: u64,
        suppressed_duplicates: u64,
        response_gen: u64,
    },
}

/// Stateful planner guarding Kafka `Metadata` topic scoping and deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KafkaMetadataScopeGuard {
    response_gen: u64,
}

impl KafkaMetadataScopeGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { response_gen: 0 }
    }

    pub fn plan_request(
        &mut self,
        cand_gen: u64,
        topics_array_is_null: bool,
        requested_count: u64,
        raw_unique_count: u64,
    ) -> MetadataScopePlan {
        self.response_gen = metadata_response_gen_advance_b141(self.response_gen, cand_gen);
        if metadata_all_topics_authorized_b141(topics_array_is_null, requested_count) {
            return MetadataScopePlan::EnumerateAllBrokerTopics {
                response_gen: self.response_gen,
            };
        }
        if requested_count == 0 {
            return MetadataScopePlan::EmptyTopicList {
                response_gen: self.response_gen,
            };
        }
        let unique = metadata_unique_topics_clamp_b141(raw_unique_count, requested_count);
        MetadataScopePlan::NamedUniqueTopicsOnly {
            emitted_unique_topics: unique,
            suppressed_duplicates: requested_count.saturating_sub(unique),
            response_gen: self.response_gen,
        }
    }
}

impl Default for KafkaMetadataScopeGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_enumerates_all_empty_returns_zero_and_named_deduplicates_without_widening() {
        let mut g = KafkaMetadataScopeGuard::new();
        assert_eq!(
            g.plan_request(1, true, 0, 0),
            MetadataScopePlan::EnumerateAllBrokerTopics { response_gen: 1 }
        );
        // Empty `topics == []` (`is_null == false, requested == 0`) NEVER widens to all topics!
        assert_eq!(
            g.plan_request(2, false, 0, 0),
            MetadataScopePlan::EmptyTopicList { response_gen: 2 }
        );
        // `["events", "events", "events"]` answers `"events"` once, suppressing 2 duplicates!
        assert_eq!(
            g.plan_request(3, false, 3, 1),
            MetadataScopePlan::NamedUniqueTopicsOnly {
                emitted_unique_topics: 1,
                suppressed_duplicates: 2,
                response_gen: 3
            }
        );
    }
}
