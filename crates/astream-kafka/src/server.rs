// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::manual_map, clippy::manual_range_contains)]

//! Multi-partition Kafka `Produce` (v3), `Fetch` (v4), `ListOffsets` (v1),
//! consumer-group coordination (`FindCoordinator` v0, `JoinGroup` v0, `SyncGroup` v0,
//! `Heartbeat` v0, `LeaveGroup` v0, `OffsetCommit` v2, `OffsetFetch` v1), idempotent
//! [`KafkaStore`], [`KafkaEngine`], and live TCP [`KafkaServer`] / [`KafkaClient`].

use crate::record_batch::{
    decode_i64_be, decode_record_batch_v2, encode_i64_be, encode_record_batch_v2,
    kafka_batch_offset_advance, kafka_fetch_clamp_bytes, restamp_batch_base_offset,
    BatchDecodeError, RecordBatchV2,
};
use crate::{
    decode_i32_be, encode_i32_be, frame_response_for, is_flexible_request, is_flexible_response,
    metadata_response_multi_versioned, parse_header, put_compact_nullable_str, put_compact_str,
    put_empty_tags, put_i16, put_i32, put_str, put_uvarint, respond, skip_tag_buffer,
    take_compact_nullable_str, take_compact_str, take_i16, take_i32, take_kstring_len,
    take_uvarint, version_within_max, BrokerMeta, ClusterMeta, TopicMeta, API_VERSIONS, FETCH,
    FIND_COORDINATOR, HEARTBEAT, JOIN_GROUP, LEAVE_GROUP, LIST_OFFSETS, METADATA, NONE,
    OFFSET_COMMIT, OFFSET_FETCH, PRODUCE, SYNC_GROUP, UNKNOWN_TOPIC_OR_PARTITION,
};
use std::collections::{BTreeMap, HashMap};
use std::io::{self, Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Duration;

#[cfg(clean_islands)]
#[path = "group_island.rs"]
mod group_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{kafka_generation_advance, kafka_partition_clamp};
#[cfg(clean_islands)]
pub use group_island::{kafka_generation_advance, kafka_partition_clamp};

contract_fn! {
    /// Verified consumer-group coordinator generation match check linked via
    /// `clean-kernel-defeq` to `kafka_generation_matches_isl`.
    #[must_use]
    pub const fn kafka_generation_matches(req_gen: u64, cur_gen: u64) -> bool
    clauses [ensures result == (req_gen == cur_gen)]
    {
        req_gen == cur_gen
    }
}

/// Kafka error code 1: requested fetch offset is `< 0` or `> high_watermark`.
pub const OFFSET_OUT_OF_RANGE: i16 = 1;

/// Kafka error code 2: RecordBatch failed CRC-32C or v2 framing validation.
pub const CORRUPT_MESSAGE: i16 = 2;

/// Kafka error code 15: coordinator backing store is unavailable or failed I/O.
pub const COORDINATOR_NOT_AVAILABLE: i16 = 15;

/// Kafka error code 22: specified consumer-group generation id is stale or invalid.
pub const ILLEGAL_GENERATION: i16 = 22;

/// Kafka error code 23: member's `protocol_type` or supported protocols do not intersect the group.
pub const INCONSISTENT_GROUP_PROTOCOL: i16 = 23;

/// Kafka error code 24: empty or invalid consumer `group_id`.
pub const INVALID_GROUP_ID: i16 = 24;

/// Kafka error code 25: `member_id` is not an active member of the consumer group.
pub const UNKNOWN_MEMBER_ID: i16 = 25;

/// Kafka error code 27: group is rebalancing so clients must rejoin.
pub const REBALANCE_IN_PROGRESS: i16 = 27;

/// Kafka error code 42: unsupported compression codec or malformed request parameter.
pub const INVALID_REQUEST: i16 = 42;

/// Kafka error code 45: idempotent producer sequence gap or non-matching duplicate.
pub const OUT_OF_ORDER_SEQUENCE_NUMBER: i16 = 45;

/// Kafka error code 47: producer epoch `<` previously observed epoch for `producer_id`.
pub const INVALID_PRODUCER_EPOCH: i16 = 47;

/// Hard frame cap on the TCP accept path (16 MiB, matching `astream_wire::MAX_PAYLOAD_LEN`).
pub const MAX_KAFKA_FRAME_LEN: usize = 16 * 1024 * 1024;

/// Maximum partitions per topic enforced by [`kafka_partition_clamp`].
pub const MAX_TOPIC_PARTITIONS: i32 = 256;

/// Sentinel timestamp `-2` in `ListOffsets` v1: earliest retained offset (`0`).
pub const TIMESTAMP_EARLIEST: i64 = -2;

/// Sentinel timestamp `-1` in `ListOffsets` v1: log-end / high-watermark offset.
pub const TIMESTAMP_LATEST: i64 = -1;

/// Result of a `JoinGroup` v0 request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinGroupResult {
    pub error_code: i16,
    pub generation_id: i32,
    pub group_protocol: String,
    pub leader_id: String,
    pub member_id: String,
    pub members: Vec<(String, Vec<u8>)>,
}

/// Result of an `OffsetFetch` v1 partition lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedOffset {
    pub error_code: i16,
    pub offset: i64,
    pub metadata: Option<String>,
}

/// Concrete storage and consumer-group coordinator backend served by [`respond_with_engine`]
/// and [`KafkaServer::bind_engine`].
///
/// Uses concrete enum dispatch rather than generic trait monomorphization so every stateful
/// handler in `astream-kafka` discharges with zero `[instance-hypothesis:discharge]` obligations
/// under `targo trust check`.
pub enum KafkaEngine {
    /// In-memory multi-partition store and consumer-group coordinator.
    Memory(KafkaStore),
    /// Durable multi-partition store and coordinator backed by `astream_broker::ShardedBroker`.
    #[cfg(feature = "durable")]
    Durable(crate::durable::DurableKafkaStore),
}

enum StoreRef<'a> {
    Memory(&'a KafkaStore),
    #[cfg(feature = "durable")]
    Durable(&'a crate::durable::DurableKafkaStore),
}

impl StoreRef<'_> {
    fn topics_meta(&self) -> Vec<TopicMeta> {
        match self {
            Self::Memory(s) => s.topics_meta(),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.topics_meta(),
        }
    }

    fn fetch_batches(
        &self,
        topic: &str,
        partition_id: i32,
        fetch_offset: i64,
        max_bytes: i32,
    ) -> (i16, i64, Vec<u8>) {
        match self {
            Self::Memory(s) => s.fetch_batches(topic, partition_id, fetch_offset, max_bytes),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.fetch_batches(topic, partition_id, fetch_offset, max_bytes),
        }
    }

    fn list_offset(&self, topic: &str, partition_id: i32, target_ts: i64) -> (i16, i64, i64) {
        match self {
            Self::Memory(s) => s.list_offset(topic, partition_id, target_ts),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.list_offset(topic, partition_id, target_ts),
        }
    }

    fn fetch_offset(&self, group_id: &str, topic: &str, partition_id: i32) -> CommittedOffset {
        match self {
            Self::Memory(s) => s.fetch_offset(group_id, topic, partition_id),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.fetch_offset(group_id, topic, partition_id),
        }
    }
}

enum StoreMut<'a> {
    Memory(&'a mut KafkaStore),
    #[cfg(feature = "durable")]
    Durable(&'a mut crate::durable::DurableKafkaStore),
}

impl StoreMut<'_> {
    fn as_ref(&self) -> StoreRef<'_> {
        match self {
            Self::Memory(s) => StoreRef::Memory(s),
            #[cfg(feature = "durable")]
            Self::Durable(s) => StoreRef::Durable(s),
        }
    }

    fn append_batch(&mut self, topic: &str, partition_id: i32, raw_batch: &[u8]) -> (i16, i64) {
        match self {
            Self::Memory(s) => s.append_batch(topic, partition_id, raw_batch),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.append_batch(topic, partition_id, raw_batch),
        }
    }

    fn join_group(
        &mut self,
        group_id: &str,
        session_timeout_ms: i32,
        member_id: &str,
        protocol_type: &str,
        protocols: &[(String, Vec<u8>)],
    ) -> JoinGroupResult {
        match self {
            Self::Memory(s) => s.join_group(
                group_id,
                session_timeout_ms,
                member_id,
                protocol_type,
                protocols,
            ),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.join_group(
                group_id,
                session_timeout_ms,
                member_id,
                protocol_type,
                protocols,
            ),
        }
    }

    fn sync_group(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        assignments: &[(String, Vec<u8>)],
    ) -> (i16, Vec<u8>) {
        match self {
            Self::Memory(s) => s.sync_group(group_id, generation_id, member_id, assignments),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.sync_group(group_id, generation_id, member_id, assignments),
        }
    }

    fn heartbeat(&mut self, group_id: &str, generation_id: i32, member_id: &str) -> i16 {
        match self {
            Self::Memory(s) => s.heartbeat(group_id, generation_id, member_id),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.heartbeat(group_id, generation_id, member_id),
        }
    }

    fn leave_group(&mut self, group_id: &str, member_id: &str) -> i16 {
        match self {
            Self::Memory(s) => s.leave_group(group_id, member_id),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.leave_group(group_id, member_id),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn commit_offset(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        topic: &str,
        partition_id: i32,
        offset: i64,
        metadata: Option<&str>,
    ) -> i16 {
        match self {
            Self::Memory(s) => s.commit_offset(
                group_id,
                generation_id,
                member_id,
                topic,
                partition_id,
                offset,
                metadata,
            ),
            #[cfg(feature = "durable")]
            Self::Durable(s) => s.commit_offset(
                group_id,
                generation_id,
                member_id,
                topic,
                partition_id,
                offset,
                metadata,
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StoredBatch {
    pub(crate) base_offset: u64,
    pub(crate) next_offset: u64,
    pub(crate) first_timestamp_ms: i64,
    pub(crate) max_timestamp_ms: i64,
    pub(crate) bytes: Vec<u8>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ProducerWindow {
    pub(crate) epoch: i16,
    pub(crate) last_base_seq: i32,
    pub(crate) last_next_seq: i32,
    pub(crate) last_base_offset: i64,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct PartitionLog {
    pub(crate) high_watermark: u64,
    pub(crate) batches: Vec<StoredBatch>,
    pub(crate) producers: HashMap<i64, ProducerWindow>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GroupMember {
    pub(crate) member_id: String,
    pub(crate) session_timeout_ms: i32,
    pub(crate) protocols: Vec<(String, Vec<u8>)>,
    pub(crate) assignment: Vec<u8>,
}

impl GroupMember {
    fn supports_protocol(&self, name: &str) -> bool {
        for (p_name, _) in &self.protocols {
            if p_name == name {
                return true;
            }
        }
        false
    }

    fn metadata_for(&self, name: &str) -> Vec<u8> {
        for (p_name, meta) in &self.protocols {
            if p_name == name {
                return meta.clone();
            }
        }
        Vec::new()
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct GroupState {
    pub(crate) generation_id: i32,
    pub(crate) next_member_seq: u64,
    pub(crate) protocol_type: String,
    pub(crate) protocol_name: String,
    pub(crate) leader_id: String,
    pub(crate) members: Vec<GroupMember>,
}

impl GroupState {
    fn find_member_index(&self, member_id: &str) -> Option<usize> {
        let mut idx = 0usize;
        while idx < self.members.len() {
            if let Some(m) = self.members.get(idx) {
                if m.member_id == member_id {
                    return Some(idx);
                }
            }
            idx = idx.saturating_add(1);
        }
        None
    }
}

#[cfg(feature = "durable")]
pub(crate) enum AppendPlan {
    Duplicate {
        base_offset: i64,
    },
    Write {
        base_offset_i64: i64,
        batch: StoredBatch,
        producer_update: Option<(i64, ProducerWindow)>,
    },
}

fn select_common_protocol(members: &[GroupMember]) -> Option<String> {
    let first = members.first()?;
    for (cand, _) in &first.protocols {
        if cand.is_empty() {
            continue;
        }
        let mut all_support = true;
        for m in members {
            if !m.supports_protocol(cand) {
                all_support = false;
                break;
            }
        }
        if all_support {
            return Some(cand.clone());
        }
    }
    None
}

fn empty_join_error(error_code: i16, member_id: &str) -> JoinGroupResult {
    JoinGroupResult {
        error_code,
        generation_id: -1,
        group_protocol: String::new(),
        leader_id: String::new(),
        member_id: member_id.to_owned(),
        members: Vec::new(),
    }
}

/// Multi-partition in-memory Kafka RecordBatch v2 store with KIP-98 idempotent producer
/// deduplication/fencing and full consumer-group coordination (`TlaConsumerGroup`).
#[derive(Debug, Clone)]
pub struct KafkaStore {
    partitions: BTreeMap<String, Vec<PartitionLog>>,
    groups: BTreeMap<String, GroupState>,
    offsets: BTreeMap<(String, String, i32), (i64, Option<String>)>,
}

impl KafkaStore {
    /// Create a [`KafkaStore`] initialized with 1 partition (`0`) for each topic in `topics`.
    #[must_use]
    pub fn new(topics: &[String]) -> Self {
        let mut specs = Vec::new();
        for t in topics {
            specs.push((t.clone(), 1));
        }
        Self::with_partitions(&specs)
    }

    /// Create a [`KafkaStore`] with explicit per-topic partition counts (clamped into
    /// `1..=MAX_TOPIC_PARTITIONS` via Clean-origin [`kafka_partition_clamp`]).
    #[must_use]
    pub fn with_partitions(topics: &[(String, i32)]) -> Self {
        let mut partitions = BTreeMap::new();
        for (name, requested) in topics {
            let req_u64 = if *requested <= 1 {
                1u64
            } else {
                *requested as u64
            };
            let count = kafka_partition_clamp(req_u64, MAX_TOPIC_PARTITIONS as u64) as usize;
            let mut logs = Vec::new();
            let mut idx = 0usize;
            while idx < count {
                logs.push(PartitionLog::default());
                idx = idx.saturating_add(1);
            }
            partitions.insert(name.clone(), logs);
        }
        Self {
            partitions,
            groups: BTreeMap::new(),
            offsets: BTreeMap::new(),
        }
    }

    /// Return the partition count configured for `topic`, or `None` if unserved.
    #[must_use]
    pub fn partition_count(&self, topic: &str) -> Option<i32> {
        match self.partitions.get(topic) {
            Some(parts) => match i32::try_from(parts.len()) {
                Ok(n) => Some(n),
                Err(_) => Some(MAX_TOPIC_PARTITIONS),
            },
            None => None,
        }
    }

    /// Return the current high watermark (next offset) for `(topic, 0)`.
    #[must_use]
    pub fn high_watermark(&self, topic: &str) -> Option<u64> {
        self.high_watermark_partition(topic, 0)
    }

    /// Return the current high watermark (next offset) for `(topic, partition_id)`.
    #[must_use]
    pub fn high_watermark_partition(&self, topic: &str, partition_id: i32) -> Option<u64> {
        if partition_id < 0 {
            return None;
        }
        let parts = self.partitions.get(topic)?;
        let part = parts.get(partition_id as usize)?;
        Some(part.high_watermark)
    }

    fn part_ref(&self, topic: &str, partition_id: i32) -> Option<&PartitionLog> {
        if partition_id < 0 {
            return None;
        }
        let parts = self.partitions.get(topic)?;
        parts.get(partition_id as usize)
    }

    fn part_mut(&mut self, topic: &str, partition_id: i32) -> Option<&mut PartitionLog> {
        if partition_id < 0 {
            return None;
        }
        let parts = self.partitions.get_mut(topic)?;
        parts.get_mut(partition_id as usize)
    }

    fn build_append(
        part: &PartitionLog,
        raw_batch: &[u8],
    ) -> Result<(Option<i64>, Option<ProduceMutation>), (i16, i64)> {
        let (decoded, consumed) = match decode_record_batch_v2(raw_batch) {
            Ok(v) => v,
            Err(BatchDecodeError::CompressedUnsupported(_)) => return Err((INVALID_REQUEST, -1)),
            Err(_) => return Err((CORRUPT_MESSAGE, -1)),
        };
        if consumed != raw_batch.len() || decoded.records.is_empty() {
            return Err((CORRUPT_MESSAGE, -1));
        }
        let Ok(rec_count_i32) = i32::try_from(decoded.records.len()) else {
            return Err((CORRUPT_MESSAGE, -1));
        };

        if decoded.producer_id >= 0 {
            if decoded.base_sequence < 0 {
                return Err((OUT_OF_ORDER_SEQUENCE_NUMBER, -1));
            }
            let Some(cand_next_seq) = decoded.base_sequence.checked_add(rec_count_i32) else {
                return Err((OUT_OF_ORDER_SEQUENCE_NUMBER, -1));
            };
            if let Some(&win) = part.producers.get(&decoded.producer_id) {
                if decoded.producer_epoch < win.epoch {
                    return Err((INVALID_PRODUCER_EPOCH, -1));
                }
                if decoded.producer_epoch == win.epoch {
                    if decoded.base_sequence == win.last_base_seq
                        && cand_next_seq == win.last_next_seq
                    {
                        return Ok((Some(win.last_base_offset), None));
                    }
                    if decoded.base_sequence != win.last_next_seq {
                        return Err((OUT_OF_ORDER_SEQUENCE_NUMBER, -1));
                    }
                } else if decoded.base_sequence != 0 {
                    return Err((OUT_OF_ORDER_SEQUENCE_NUMBER, -1));
                }
            } else if decoded.base_sequence != 0 {
                return Err((OUT_OF_ORDER_SEQUENCE_NUMBER, -1));
            }
        }

        let base_off = part.high_watermark;
        let Ok(base_off_i64) = i64::try_from(base_off) else {
            return Err((INVALID_REQUEST, -1));
        };
        let mut stored_bytes = raw_batch.to_vec();
        if !restamp_batch_base_offset(&mut stored_bytes, base_off_i64) {
            return Err((CORRUPT_MESSAGE, -1));
        }
        let first_ts = match decoded.records.first() {
            Some(r) => r.timestamp_ms,
            None => 0,
        };
        let mut max_ts = first_ts;
        for r in &decoded.records {
            if r.timestamp_ms > max_ts {
                max_ts = r.timestamp_ms;
            }
        }
        let next_off = kafka_batch_offset_advance(
            base_off,
            base_off.saturating_add(decoded.records.len() as u64),
        );
        let stored = StoredBatch {
            base_offset: base_off,
            next_offset: next_off,
            first_timestamp_ms: first_ts,
            max_timestamp_ms: max_ts,
            bytes: stored_bytes,
        };
        let prod_upd = if decoded.producer_id >= 0 {
            let next_seq = decoded.base_sequence.saturating_add(rec_count_i32);
            Some((
                decoded.producer_id,
                ProducerWindow {
                    epoch: decoded.producer_epoch,
                    last_base_seq: decoded.base_sequence,
                    last_next_seq: next_seq,
                    last_base_offset: base_off_i64,
                },
            ))
        } else {
            None
        };
        Ok((None, Some((base_off_i64, stored, prod_upd))))
    }

    /// Append one encoded RecordBatch v2 payload to `(topic, partition_id)`, returning
    /// `(error_code, base_offset)`.
    pub fn append_batch(&mut self, topic: &str, partition_id: i32, raw_batch: &[u8]) -> (i16, i64) {
        let outcome = {
            let Some(part) = self.part_ref(topic, partition_id) else {
                return (UNKNOWN_TOPIC_OR_PARTITION, -1);
            };
            Self::build_append(part, raw_batch)
        };
        match outcome {
            Err(err) => err,
            Ok((Some(dup_off), _)) => (NONE, dup_off),
            Ok((None, Some((base_off_i64, stored, prod_upd)))) => {
                if let Some(part) = self.part_mut(topic, partition_id) {
                    part.high_watermark = stored.next_offset;
                    part.batches.push(stored);
                    if let Some((pid, win)) = prod_upd {
                        part.producers.insert(pid, win);
                    }
                }
                (NONE, base_off_i64)
            }
            Ok((None, None)) => (CORRUPT_MESSAGE, -1),
        }
    }

    #[cfg(feature = "durable")]
    pub(crate) fn plan_append_batch(
        &self,
        topic: &str,
        partition_id: i32,
        raw_batch: &[u8],
    ) -> Result<AppendPlan, (i16, i64)> {
        let Some(part) = self.part_ref(topic, partition_id) else {
            return Err((UNKNOWN_TOPIC_OR_PARTITION, -1));
        };
        match Self::build_append(part, raw_batch)? {
            (Some(dup_off), _) => Ok(AppendPlan::Duplicate {
                base_offset: dup_off,
            }),
            (None, Some((base_off_i64, stored, prod_upd))) => Ok(AppendPlan::Write {
                base_offset_i64: base_off_i64,
                batch: stored,
                producer_update: prod_upd,
            }),
            (None, None) => Err((CORRUPT_MESSAGE, -1)),
        }
    }

    #[cfg(feature = "durable")]
    pub(crate) fn commit_append_plan(&mut self, topic: &str, partition_id: i32, plan: AppendPlan) {
        if let AppendPlan::Write {
            batch,
            producer_update,
            ..
        } = plan
        {
            if let Some(part) = self.part_mut(topic, partition_id) {
                part.high_watermark = batch.next_offset;
                part.batches.push(batch);
                if let Some((pid, win)) = producer_update {
                    part.producers.insert(pid, win);
                }
            }
        }
    }

    #[cfg(feature = "durable")]
    pub(crate) fn replay_stored_batch(
        &mut self,
        topic: &str,
        partition_id: i32,
        stored_bytes: &[u8],
    ) -> bool {
        let Ok((decoded, consumed)) = decode_record_batch_v2(stored_bytes) else {
            return false;
        };
        if consumed != stored_bytes.len() || decoded.records.is_empty() || decoded.base_offset < 0 {
            return false;
        }
        let Ok(rec_count_i32) = i32::try_from(decoded.records.len()) else {
            return false;
        };
        let Some(part) = self.part_mut(topic, partition_id) else {
            return false;
        };
        let base_off = decoded.base_offset as u64;
        let first_ts = match decoded.records.first() {
            Some(r) => r.timestamp_ms,
            None => 0,
        };
        let mut max_ts = first_ts;
        for r in &decoded.records {
            if r.timestamp_ms > max_ts {
                max_ts = r.timestamp_ms;
            }
        }
        let next_off = kafka_batch_offset_advance(
            part.high_watermark,
            base_off.saturating_add(decoded.records.len() as u64),
        );
        part.batches.push(StoredBatch {
            base_offset: base_off,
            next_offset: next_off,
            first_timestamp_ms: first_ts,
            max_timestamp_ms: max_ts,
            bytes: stored_bytes.to_vec(),
        });
        part.high_watermark = next_off;
        if decoded.producer_id >= 0 && decoded.base_sequence >= 0 {
            let next_seq = decoded.base_sequence.saturating_add(rec_count_i32);
            part.producers.insert(
                decoded.producer_id,
                ProducerWindow {
                    epoch: decoded.producer_epoch,
                    last_base_seq: decoded.base_sequence,
                    last_next_seq: next_seq,
                    last_base_offset: decoded.base_offset,
                },
            );
        }
        true
    }

    /// Fetch RecordBatch v2 bytes starting from `fetch_offset` up to `max_bytes`
    /// (always returning at least the first matching batch even when larger than
    /// `max_bytes`, matching Kafka's KIP-74 progress rule so consumers never stall).
    #[must_use]
    pub fn fetch_batches(
        &self,
        topic: &str,
        partition_id: i32,
        fetch_offset: i64,
        max_bytes: i32,
    ) -> (i16, i64, Vec<u8>) {
        let Some(part) = self.part_ref(topic, partition_id) else {
            return (UNKNOWN_TOPIC_OR_PARTITION, -1, Vec::new());
        };
        let hw_i64 = i64::try_from(part.high_watermark).unwrap_or(i64::MAX);
        if fetch_offset < 0 || (fetch_offset as u64) > part.high_watermark {
            return (OFFSET_OUT_OF_RANGE, hw_i64, Vec::new());
        }
        let target = fetch_offset as u64;
        let budget = if max_bytes <= 0 {
            0u64
        } else {
            max_bytes as u64
        };
        let mut out = Vec::new();
        for b in &part.batches {
            if b.next_offset <= target {
                continue;
            }
            let cand_len = (out.len().saturating_add(b.bytes.len())) as u64;
            let clamped = kafka_fetch_clamp_bytes(cand_len, budget);
            if !out.is_empty() && clamped < cand_len {
                break;
            }
            out.extend_from_slice(&b.bytes);
            if budget == 0 {
                break;
            }
        }
        (NONE, hw_i64, out)
    }

    /// Resolve a `ListOffsets` v1 query (`-2` earliest, `-1` latest, `>= 0` first offset
    /// whose timestamp `>= target_ts`), returning `(error_code, timestamp, offset)`.
    #[must_use]
    pub fn list_offset(&self, topic: &str, partition_id: i32, target_ts: i64) -> (i16, i64, i64) {
        let Some(part) = self.part_ref(topic, partition_id) else {
            return (UNKNOWN_TOPIC_OR_PARTITION, -1, -1);
        };
        if target_ts == TIMESTAMP_EARLIEST {
            return (NONE, -1, 0);
        }
        if target_ts == TIMESTAMP_LATEST {
            let hw = i64::try_from(part.high_watermark).unwrap_or(i64::MAX);
            return (NONE, -1, hw);
        }
        if target_ts < 0 {
            return (INVALID_REQUEST, -1, -1);
        }
        for b in &part.batches {
            if b.max_timestamp_ms >= target_ts {
                if let Ok((decoded, _)) = decode_record_batch_v2(&b.bytes) {
                    for (idx, r) in decoded.records.iter().enumerate() {
                        if r.timestamp_ms >= target_ts {
                            let off = b.base_offset.saturating_add(idx as u64);
                            let off_i64 = i64::try_from(off).unwrap_or(i64::MAX);
                            return (NONE, r.timestamp_ms, off_i64);
                        }
                    }
                }
                let base_i64 = i64::try_from(b.base_offset).unwrap_or(i64::MAX);
                return (NONE, b.first_timestamp_ms, base_i64);
            }
        }
        (NONE, -1, -1)
    }

    pub(crate) fn compute_join_group(
        cur_group: Option<&GroupState>,
        group_id: &str,
        session_timeout_ms: i32,
        member_id: &str,
        protocol_type: &str,
        protocols: &[(String, Vec<u8>)],
    ) -> (JoinGroupResult, Option<GroupState>) {
        if group_id.is_empty() {
            return (empty_join_error(INVALID_GROUP_ID, member_id), None);
        }
        if session_timeout_ms <= 0 {
            return (empty_join_error(INVALID_REQUEST, member_id), None);
        }
        if protocol_type.is_empty() || protocols.is_empty() {
            return (
                empty_join_error(INCONSISTENT_GROUP_PROTOCOL, member_id),
                None,
            );
        }

        let mut g = match cur_group {
            Some(existing) => existing.clone(),
            None => GroupState::default(),
        };

        if !g.members.is_empty() && g.protocol_type != protocol_type {
            return (
                empty_join_error(INCONSISTENT_GROUP_PROTOCOL, member_id),
                None,
            );
        }

        let assigned_id = if member_id.is_empty() {
            g.next_member_seq = g.next_member_seq.saturating_add(1);
            format!("{group_id}-member-{}", g.next_member_seq)
        } else {
            if g.find_member_index(member_id).is_none() {
                return (empty_join_error(UNKNOWN_MEMBER_ID, member_id), None);
            }
            member_id.to_owned()
        };

        let candidate_member = GroupMember {
            member_id: assigned_id.clone(),
            session_timeout_ms,
            protocols: protocols.to_vec(),
            assignment: Vec::new(),
        };

        match g.find_member_index(&assigned_id) {
            Some(idx) => {
                if let Some(slot) = g.members.get_mut(idx) {
                    *slot = candidate_member;
                }
            }
            None => g.members.push(candidate_member),
        }

        let Some(chosen_proto) = select_common_protocol(&g.members) else {
            return (
                empty_join_error(INCONSISTENT_GROUP_PROTOCOL, &assigned_id),
                None,
            );
        };

        // Rebalance clears stale member assignments until the new leader issues SyncGroup.
        for m in &mut g.members {
            m.assignment.clear();
        }

        let cur_gen_u64 = if g.generation_id < 0 {
            0u64
        } else {
            g.generation_id as u64
        };
        let next_gen_u64 = kafka_generation_advance(cur_gen_u64, cur_gen_u64.saturating_add(1));
        g.generation_id = i32::try_from(next_gen_u64).unwrap_or(i32::MAX);
        g.protocol_type = protocol_type.to_owned();
        g.protocol_name = chosen_proto.clone();
        g.leader_id = match g.members.first() {
            Some(first) => first.member_id.clone(),
            None => String::new(),
        };

        let mut member_list = Vec::new();
        if assigned_id == g.leader_id {
            for m in &g.members {
                member_list.push((m.member_id.clone(), m.metadata_for(&chosen_proto)));
            }
        }

        let res = JoinGroupResult {
            error_code: NONE,
            generation_id: g.generation_id,
            group_protocol: chosen_proto,
            leader_id: g.leader_id.clone(),
            member_id: assigned_id,
            members: member_list,
        };
        (res, Some(g))
    }

    /// Coordinate a `JoinGroup` v0 transition, advancing `generation_id` monotonically via
    /// Clean-origin [`kafka_generation_advance`].
    pub fn join_group(
        &mut self,
        group_id: &str,
        session_timeout_ms: i32,
        member_id: &str,
        protocol_type: &str,
        protocols: &[(String, Vec<u8>)],
    ) -> JoinGroupResult {
        let (res, updated) = Self::compute_join_group(
            self.groups.get(group_id),
            group_id,
            session_timeout_ms,
            member_id,
            protocol_type,
            protocols,
        );
        if let Some(new_state) = updated {
            self.groups.insert(group_id.to_owned(), new_state);
        }
        res
    }

    pub(crate) fn compute_sync_group(
        cur_group: Option<&GroupState>,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        assignments: &[(String, Vec<u8>)],
    ) -> ((i16, Vec<u8>), Option<GroupState>) {
        if group_id.is_empty() {
            return ((INVALID_GROUP_ID, Vec::new()), None);
        }
        let Some(existing) = cur_group else {
            return ((UNKNOWN_MEMBER_ID, Vec::new()), None);
        };
        let Some(caller_idx) = existing.find_member_index(member_id) else {
            return ((UNKNOWN_MEMBER_ID, Vec::new()), None);
        };
        if generation_id < 0
            || existing.generation_id < 0
            || !kafka_generation_matches(generation_id as u64, existing.generation_id as u64)
        {
            return ((ILLEGAL_GENERATION, Vec::new()), None);
        }

        if member_id == existing.leader_id && !assignments.is_empty() {
            let mut updated = existing.clone();
            for m in &mut updated.members {
                m.assignment.clear();
                for (target_id, bytes) in assignments {
                    if m.member_id == *target_id {
                        m.assignment = bytes.clone();
                        break;
                    }
                }
            }
            let caller_bytes = match updated.members.get(caller_idx) {
                Some(m) => m.assignment.clone(),
                None => Vec::new(),
            };
            return ((NONE, caller_bytes), Some(updated));
        }

        let caller_bytes = match existing.members.get(caller_idx) {
            Some(m) => m.assignment.clone(),
            None => Vec::new(),
        };
        ((NONE, caller_bytes), None)
    }

    /// Coordinate a `SyncGroup` v0 request, checking `generation_id` via
    /// [`kafka_generation_matches`].
    pub fn sync_group(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        assignments: &[(String, Vec<u8>)],
    ) -> (i16, Vec<u8>) {
        let (reply, updated) = Self::compute_sync_group(
            self.groups.get(group_id),
            group_id,
            generation_id,
            member_id,
            assignments,
        );
        if let Some(new_state) = updated {
            self.groups.insert(group_id.to_owned(), new_state);
        }
        reply
    }

    /// Validate a `Heartbeat` v0 request against active membership and generation.
    #[must_use]
    pub fn heartbeat(&self, group_id: &str, generation_id: i32, member_id: &str) -> i16 {
        if group_id.is_empty() {
            return INVALID_GROUP_ID;
        }
        let Some(g) = self.groups.get(group_id) else {
            return UNKNOWN_MEMBER_ID;
        };
        if g.find_member_index(member_id).is_none() {
            return UNKNOWN_MEMBER_ID;
        }
        if generation_id < 0
            || g.generation_id < 0
            || !kafka_generation_matches(generation_id as u64, g.generation_id as u64)
        {
            return ILLEGAL_GENERATION;
        }
        NONE
    }

    pub(crate) fn compute_leave_group(
        cur_group: Option<&GroupState>,
        group_id: &str,
        member_id: &str,
    ) -> (i16, Option<GroupState>) {
        if group_id.is_empty() {
            return (INVALID_GROUP_ID, None);
        }
        let Some(existing) = cur_group else {
            return (UNKNOWN_MEMBER_ID, None);
        };
        if existing.find_member_index(member_id).is_none() {
            return (UNKNOWN_MEMBER_ID, None);
        }
        let mut updated = existing.clone();
        let cap = existing.members.len();
        let mut kept = if cap <= 65_536 {
            Vec::with_capacity(cap)
        } else {
            Vec::new()
        };
        for m in &existing.members {
            if m.member_id != member_id {
                kept.push(m.clone());
            }
        }
        updated.members = kept;
        let cur_gen_u64 = if updated.generation_id < 0 {
            0u64
        } else {
            updated.generation_id as u64
        };
        let next_gen_u64 = kafka_generation_advance(cur_gen_u64, cur_gen_u64.saturating_add(1));
        updated.generation_id = i32::try_from(next_gen_u64).unwrap_or(i32::MAX);
        updated.leader_id = match updated.members.first() {
            Some(first) => first.member_id.clone(),
            None => String::new(),
        };
        if updated.members.is_empty() {
            updated.protocol_name.clear();
        }
        (NONE, Some(updated))
    }

    /// Remove `member_id` from `group_id` (`LeaveGroup` v0), advancing `generation_id` so
    /// remaining members observe the rebalance.
    pub fn leave_group(&mut self, group_id: &str, member_id: &str) -> i16 {
        let (code, updated) =
            Self::compute_leave_group(self.groups.get(group_id), group_id, member_id);
        if let Some(new_state) = updated {
            self.groups.insert(group_id.to_owned(), new_state);
        }
        code
    }

    pub(crate) fn validate_commit_offset(
        &self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        topic: &str,
        partition_id: i32,
        offset: i64,
    ) -> i16 {
        if group_id.is_empty() {
            return INVALID_GROUP_ID;
        }
        if generation_id < 0 && member_id.is_empty() {
            if let Some(g) = self.groups.get(group_id) {
                if !g.members.is_empty() {
                    return ILLEGAL_GENERATION;
                }
            }
        } else {
            let Some(g) = self.groups.get(group_id) else {
                return UNKNOWN_MEMBER_ID;
            };
            if g.find_member_index(member_id).is_none() {
                return UNKNOWN_MEMBER_ID;
            }
            if generation_id < 0
                || g.generation_id < 0
                || !kafka_generation_matches(generation_id as u64, g.generation_id as u64)
            {
                return ILLEGAL_GENERATION;
            }
        }
        if self.part_ref(topic, partition_id).is_none() {
            return UNKNOWN_TOPIC_OR_PARTITION;
        }
        if offset < 0 {
            return INVALID_REQUEST;
        }
        NONE
    }

    pub(crate) fn install_committed_offset(
        &mut self,
        group_id: &str,
        topic: &str,
        partition_id: i32,
        offset: i64,
        metadata: Option<String>,
    ) {
        self.offsets.insert(
            (group_id.to_owned(), topic.to_owned(), partition_id),
            (offset, metadata),
        );
    }

    #[cfg(feature = "durable")]
    pub(crate) fn group_ref(&self, group_id: &str) -> Option<&GroupState> {
        self.groups.get(group_id)
    }

    #[cfg(feature = "durable")]
    pub(crate) fn install_group_state(&mut self, group_id: String, state: GroupState) {
        self.groups.insert(group_id, state);
    }

    /// Commit one `(group_id, topic, partition_id)` offset (`OffsetCommit` v2).
    #[allow(clippy::too_many_arguments)]
    pub fn commit_offset(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        topic: &str,
        partition_id: i32,
        offset: i64,
        metadata: Option<&str>,
    ) -> i16 {
        let code = self.validate_commit_offset(
            group_id,
            generation_id,
            member_id,
            topic,
            partition_id,
            offset,
        );
        if code != NONE {
            return code;
        }
        let meta_owned = opt_str_owned(metadata);
        self.install_committed_offset(group_id, topic, partition_id, offset, meta_owned);
        NONE
    }

    /// Fetch one `(group_id, topic, partition_id)` committed offset (`OffsetFetch` v1).
    #[must_use]
    pub fn fetch_offset(&self, group_id: &str, topic: &str, partition_id: i32) -> CommittedOffset {
        if group_id.is_empty() {
            return CommittedOffset {
                error_code: INVALID_GROUP_ID,
                offset: -1,
                metadata: None,
            };
        }
        if self.part_ref(topic, partition_id).is_none() {
            return CommittedOffset {
                error_code: UNKNOWN_TOPIC_OR_PARTITION,
                offset: -1,
                metadata: None,
            };
        }
        match self
            .offsets
            .get(&(group_id.to_owned(), topic.to_owned(), partition_id))
        {
            Some((off, meta)) => CommittedOffset {
                error_code: NONE,
                offset: *off,
                metadata: meta.clone(),
            },
            None => CommittedOffset {
                error_code: NONE,
                offset: -1,
                metadata: None,
            },
        }
    }
    /// Return advertised topics and their partition counts in deterministic order.
    #[must_use]
    pub fn topics_meta(&self) -> Vec<TopicMeta> {
        let mut out = Vec::new();
        for (name, parts) in &self.partitions {
            let count = match i32::try_from(parts.len()) {
                Ok(n) if n >= 1 => n,
                _ => 1,
            };
            out.push(TopicMeta {
                name: name.clone(),
                partitions: count,
            });
        }
        out
    }
}

const fn take_i8(b: &[u8]) -> Option<(i8, &[u8])> {
    let &[b0, ref rest @ ..] = b else {
        return None;
    };
    Some((b0 as i8, rest))
}

pub(crate) const fn take_i64(b: &[u8]) -> Option<(i64, &[u8])> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = b else {
        return None;
    };
    Some((decode_i64_be(&[b0, b1, b2, b3, b4, b5, b6, b7]), rest))
}

type ProduceMutation = (i64, StoredBatch, Option<(i64, ProducerWindow)>);

#[allow(clippy::manual_map)]
pub(crate) fn opt_str_owned(s: Option<&str>) -> Option<String> {
    match s {
        Some(v) => Some(v.to_owned()),
        None => None,
    }
}
type ProducePartReply = (i32, i16, i64);
type FetchPartReply = (i32, i16, i64, Vec<u8>);
type ListOffsetsPartReply = (i32, i16, i64, i64);
type OffsetCommitPartReply = (i32, i16);
type OffsetFetchPartReply = (i32, CommittedOffset);

/// Supported `(api_key, min_version, max_version)` tuple returned by [`KafkaClient::api_versions`].
pub type ApiVersionEntry = (i16, i16, i16);

pub(crate) fn take_kstr(b: &[u8]) -> Option<(Option<&str>, &[u8])> {
    let (len_opt, rest) = take_kstring_len(b)?;
    let Some(len) = len_opt else {
        return Some((None, rest));
    };
    let slice = rest.get(..len)?;
    let Ok(s) = core::str::from_utf8(slice) else {
        return None;
    };
    Some((Some(s), rest.get(len..)?))
}

pub(crate) fn take_nonnull_kstr(b: &[u8]) -> Option<(&str, &[u8])> {
    let (Some(s), rest) = take_kstr(b)? else {
        return None;
    };
    Some((s, rest))
}

pub(crate) fn take_nullable_bytes(b: &[u8]) -> Option<(Option<&[u8]>, &[u8])> {
    let (n, rest) = take_i32(b)?;
    if n < 0 {
        return Some((None, rest));
    }
    let len = n as usize;
    Some((Some(rest.get(..len)?), rest.get(len..)?))
}

pub(crate) fn take_bytes(b: &[u8]) -> Option<(&[u8], &[u8])> {
    let (Some(bytes), rest) = take_nullable_bytes(b)? else {
        return None;
    };
    Some((bytes, rest))
}

pub(crate) fn put_nullable_str(o: &mut Vec<u8>, s: Option<&str>) {
    match s {
        Some(v) => put_str(o, v),
        None => put_i16(o, -1),
    }
}

pub(crate) fn put_bytes(o: &mut Vec<u8>, b: &[u8]) {
    let len = i32::try_from(b.len()).unwrap_or(i32::MAX);
    put_i32(o, len);
    if let Some(slice) = b.get(..(len as usize)) {
        o.extend_from_slice(slice);
    }
}

fn merged_topics_meta(cluster: &ClusterMeta, backend: StoreRef<'_>) -> Vec<TopicMeta> {
    let mut topics = backend.topics_meta();
    for t in &cluster.topics {
        let mut present = false;
        for tm in &topics {
            if tm.name == *t {
                present = true;
                break;
            }
        }
        if !present {
            topics.push(TopicMeta {
                name: t.clone(),
                partitions: 1,
            });
        }
    }
    topics
}

fn respond_with_store_mut(
    req: &[u8],
    cluster: &ClusterMeta,
    backend: &mut StoreMut<'_>,
) -> Option<Vec<u8>> {
    let (h, body_at) = parse_header(req)?;
    if h.api_key == API_VERSIONS {
        return respond(req, cluster);
    }
    let body = req.get(body_at..)?;
    let payload = match h.api_key {
        METADATA if h.api_version >= 0 && version_within_max(h.api_version as u64, 9) => {
            let topics = merged_topics_meta(cluster, backend.as_ref());
            metadata_response_multi_versioned(h.api_version, body, &cluster.broker, &topics)?
        }
        PRODUCE if h.api_version == 3 && version_within_max(h.api_version as u64, 3) => {
            produce_v3_response(body, backend)?
        }
        FETCH if h.api_version == 4 && version_within_max(h.api_version as u64, 4) => {
            fetch_v4_response(body, backend.as_ref())?
        }
        LIST_OFFSETS if h.api_version == 1 && version_within_max(h.api_version as u64, 1) => {
            list_offsets_v1_response(body, backend.as_ref())?
        }
        OFFSET_COMMIT if h.api_version == 2 && version_within_max(h.api_version as u64, 2) => {
            offset_commit_v2_response(body, backend)?
        }
        OFFSET_FETCH if h.api_version == 1 && version_within_max(h.api_version as u64, 1) => {
            offset_fetch_v1_response(body, backend.as_ref())?
        }
        FIND_COORDINATOR if h.api_version >= 0 && version_within_max(h.api_version as u64, 3) => {
            find_coordinator_response(h.api_version, body, &cluster.broker)?
        }
        JOIN_GROUP if h.api_version == 0 && version_within_max(h.api_version as u64, 0) => {
            join_group_v0_response(body, backend)?
        }
        HEARTBEAT if h.api_version == 0 && version_within_max(h.api_version as u64, 0) => {
            heartbeat_v0_response(body, backend)?
        }
        LEAVE_GROUP if h.api_version == 0 && version_within_max(h.api_version as u64, 0) => {
            leave_group_v0_response(body, backend)?
        }
        SYNC_GROUP if h.api_version == 0 && version_within_max(h.api_version as u64, 0) => {
            sync_group_v0_response(body, backend)?
        }
        _ => Vec::new(),
    };
    frame_response_for(h.api_key, h.api_version, h.correlation_id, &payload)
}

/// Stateful dispatcher over [`KafkaEngine`] (`KafkaStore` or `DurableKafkaStore`),
/// answering all 12 supported Kafka APIs (`ApiVersions` v0 + downgrade, `Metadata` v0,
/// `Produce` v3, `Fetch` v4, `ListOffsets` v1, `OffsetCommit` v2, `OffsetFetch` v1,
/// `FindCoordinator` v0, `JoinGroup` v0, `Heartbeat` v0, `LeaveGroup` v0, `SyncGroup` v0).
#[must_use]
pub fn respond_with_engine(
    req: &[u8],
    cluster: &ClusterMeta,
    engine: &mut KafkaEngine,
) -> Option<Vec<u8>> {
    match engine {
        KafkaEngine::Memory(store) => {
            let mut m = StoreMut::Memory(store);
            respond_with_store_mut(req, cluster, &mut m)
        }
        #[cfg(feature = "durable")]
        KafkaEngine::Durable(store) => {
            let mut m = StoreMut::Durable(store);
            respond_with_store_mut(req, cluster, &mut m)
        }
    }
}

/// Stateful dispatcher specialized to in-memory [`KafkaStore`].
#[must_use]
pub fn respond_with_store(
    req: &[u8],
    cluster: &ClusterMeta,
    store: &mut KafkaStore,
) -> Option<Vec<u8>> {
    let mut m = StoreMut::Memory(store);
    respond_with_store_mut(req, cluster, &mut m)
}

/// Stateful dispatcher specialized to `ShardedBroker`-backed [`crate::durable::DurableKafkaStore`].
#[cfg(feature = "durable")]
#[must_use]
pub fn respond_with_durable(
    req: &[u8],
    cluster: &ClusterMeta,
    store: &mut crate::durable::DurableKafkaStore,
) -> Option<Vec<u8>> {
    let mut m = StoreMut::Durable(store);
    respond_with_store_mut(req, cluster, &mut m)
}

fn produce_v3_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (_txn_id, cur) = take_kstr(body)?;
    let (_acks, cur) = take_i16(cur)?;
    let (_timeout_ms, mut cur) = take_i32(cur)?;
    let (topic_count, after_tc) = take_i32(cur)?;
    cur = after_tc;
    if topic_count < 0 {
        return None;
    }

    let mut topic_replies: Vec<(String, Vec<ProducePartReply>)> = Vec::new();
    let mut t_idx = 0i32;
    while t_idx < topic_count {
        let (topic, after_name) = take_nonnull_kstr(cur)?;
        let (part_count, mut p_cur) = take_i32(after_name)?;
        if part_count < 0 {
            return None;
        }
        let mut part_replies = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < part_count {
            let (part_id, after_pid) = take_i32(p_cur)?;
            let (records_opt, next_p) = take_nullable_bytes(after_pid)?;
            let (err, base_off) = match records_opt {
                Some(raw) => backend.append_batch(topic, part_id, raw),
                None => (CORRUPT_MESSAGE, -1),
            };
            part_replies.push((part_id, err, base_off));
            p_cur = next_p;
            p_idx = p_idx.saturating_add(1);
        }
        topic_replies.push((topic.to_owned(), part_replies));
        cur = p_cur;
        t_idx = t_idx.saturating_add(1);
    }

    let mut out = Vec::new();
    put_i32(&mut out, topic_replies.len() as i32);
    for (topic, parts) in &topic_replies {
        put_str(&mut out, topic);
        put_i32(&mut out, parts.len() as i32);
        for &(pid, err, base_off) in parts {
            put_i32(&mut out, pid);
            put_i16(&mut out, err);
            out.extend_from_slice(&encode_i64_be(base_off));
            out.extend_from_slice(&encode_i64_be(-1));
        }
    }
    put_i32(&mut out, 0);
    Some(out)
}

fn fetch_v4_response(body: &[u8], backend: StoreRef<'_>) -> Option<Vec<u8>> {
    let (_replica_id, cur) = take_i32(body)?;
    let (_max_wait_ms, cur) = take_i32(cur)?;
    let (_min_bytes, cur) = take_i32(cur)?;
    let (req_max_bytes, cur) = take_i32(cur)?;
    let (_isolation, cur) = take_i8(cur)?;
    let (topic_count, mut cur) = take_i32(cur)?;
    if topic_count < 0 {
        return None;
    }

    let mut remaining_req_budget = if req_max_bytes <= 0 { 0 } else { req_max_bytes };
    let mut topic_replies: Vec<(String, Vec<FetchPartReply>)> = Vec::new();
    let mut t_idx = 0i32;
    while t_idx < topic_count {
        let (topic, after_name) = take_nonnull_kstr(cur)?;
        let (part_count, mut p_cur) = take_i32(after_name)?;
        if part_count < 0 {
            return None;
        }
        let mut part_replies = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < part_count {
            let (part_id, after_pid) = take_i32(p_cur)?;
            let (fetch_off, after_off) = take_i64(after_pid)?;
            let (part_max_bytes, next_p) = take_i32(after_off)?;
            let effective_max = if part_max_bytes < remaining_req_budget {
                part_max_bytes
            } else {
                remaining_req_budget
            };
            let (err, hw, bytes) = backend.fetch_batches(topic, part_id, fetch_off, effective_max);
            let spent = i32::try_from(bytes.len()).unwrap_or(i32::MAX);
            remaining_req_budget = remaining_req_budget.saturating_sub(spent);
            part_replies.push((part_id, err, hw, bytes));
            p_cur = next_p;
            p_idx = p_idx.saturating_add(1);
        }
        topic_replies.push((topic.to_owned(), part_replies));
        cur = p_cur;
        t_idx = t_idx.saturating_add(1);
    }

    let mut out = Vec::new();
    put_i32(&mut out, 0);
    put_i32(&mut out, topic_replies.len() as i32);
    for (topic, parts) in &topic_replies {
        put_str(&mut out, topic);
        put_i32(&mut out, parts.len() as i32);
        for (pid, err, hw, bytes) in parts {
            put_i32(&mut out, *pid);
            put_i16(&mut out, *err);
            out.extend_from_slice(&encode_i64_be(*hw));
            out.extend_from_slice(&encode_i64_be(*hw));
            put_i32(&mut out, 0);
            put_bytes(&mut out, bytes);
        }
    }
    Some(out)
}

fn list_offsets_v1_response(body: &[u8], backend: StoreRef<'_>) -> Option<Vec<u8>> {
    let (_replica_id, cur) = take_i32(body)?;
    let (topic_count, mut cur) = take_i32(cur)?;
    if topic_count < 0 {
        return None;
    }

    let mut topic_replies: Vec<(String, Vec<ListOffsetsPartReply>)> = Vec::new();
    let mut t_idx = 0i32;
    while t_idx < topic_count {
        let (topic, after_name) = take_nonnull_kstr(cur)?;
        let (part_count, mut p_cur) = take_i32(after_name)?;
        if part_count < 0 {
            return None;
        }
        let mut part_replies = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < part_count {
            let (part_id, after_pid) = take_i32(p_cur)?;
            let (target_ts, next_p) = take_i64(after_pid)?;
            let (err, ts, off) = backend.list_offset(topic, part_id, target_ts);
            part_replies.push((part_id, err, ts, off));
            p_cur = next_p;
            p_idx = p_idx.saturating_add(1);
        }
        topic_replies.push((topic.to_owned(), part_replies));
        cur = p_cur;
        t_idx = t_idx.saturating_add(1);
    }

    let mut out = Vec::new();
    put_i32(&mut out, topic_replies.len() as i32);
    for (topic, parts) in &topic_replies {
        put_str(&mut out, topic);
        put_i32(&mut out, parts.len() as i32);
        for &(pid, err, ts, off) in parts {
            put_i32(&mut out, pid);
            put_i16(&mut out, err);
            out.extend_from_slice(&encode_i64_be(ts));
            out.extend_from_slice(&encode_i64_be(off));
        }
    }
    Some(out)
}

fn find_coordinator_response(
    api_version: i16,
    body: &[u8],
    broker: &BrokerMeta,
) -> Option<Vec<u8>> {
    let (key, key_type) = if api_version >= 3 {
        let (k, r1) = take_compact_str(body)?;
        let (kt, r2) = take_i8(r1)?;
        let _ = skip_tag_buffer(r2)?;
        (k, kt)
    } else if api_version >= 1 {
        let (k, r1) = take_nonnull_kstr(body)?;
        let (kt, _r2) = take_i8(r1)?;
        (k, kt)
    } else {
        let (k, _r1) = take_nonnull_kstr(body)?;
        (k, 0i8)
    };

    let (err, node_id, host, port) = if key_type != 0 {
        (COORDINATOR_NOT_AVAILABLE, -1, "", -1)
    } else if key.is_empty() {
        (INVALID_GROUP_ID, -1, "", -1)
    } else {
        (NONE, broker.node_id, broker.host.as_str(), broker.port)
    };

    let mut out = Vec::new();
    if api_version == 0 {
        put_i16(&mut out, err);
        put_i32(&mut out, node_id);
        put_str(&mut out, host);
        put_i32(&mut out, port);
        return Some(out);
    }
    if api_version <= 2 {
        put_i32(&mut out, 0); // throttle_time_ms
        put_i16(&mut out, err);
        put_nullable_str(&mut out, None); // error_message
        put_i32(&mut out, node_id);
        put_str(&mut out, host);
        put_i32(&mut out, port);
        return Some(out);
    }
    // KIP-482 flexible v3 body
    put_i32(&mut out, 0); // throttle_time_ms
    put_i16(&mut out, err);
    put_compact_nullable_str(&mut out, None); // error_message
    put_i32(&mut out, node_id);
    put_compact_str(&mut out, host);
    put_i32(&mut out, port);
    put_empty_tags(&mut out);
    Some(out)
}

fn join_group_v0_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (session_timeout_ms, cur) = take_i32(cur)?;
    let (member_id, cur) = take_nonnull_kstr(cur)?;
    let (protocol_type, cur) = take_nonnull_kstr(cur)?;
    let (proto_count, mut cur) = take_i32(cur)?;
    if proto_count < 0 {
        return None;
    }

    let mut protocols = Vec::new();
    let mut idx = 0i32;
    while idx < proto_count {
        let (p_name, after_name) = take_nonnull_kstr(cur)?;
        let (p_meta, next_cur) = take_bytes(after_name)?;
        protocols.push((p_name.to_owned(), p_meta.to_vec()));
        cur = next_cur;
        idx = idx.saturating_add(1);
    }

    let res = backend.join_group(
        group_id,
        session_timeout_ms,
        member_id,
        protocol_type,
        &protocols,
    );

    let mut out = Vec::new();
    put_i16(&mut out, res.error_code);
    put_i32(&mut out, res.generation_id);
    put_str(&mut out, &res.group_protocol);
    put_str(&mut out, &res.leader_id);
    put_str(&mut out, &res.member_id);
    put_i32(&mut out, res.members.len() as i32);
    for (m_id, m_meta) in &res.members {
        put_str(&mut out, m_id);
        put_bytes(&mut out, m_meta);
    }
    Some(out)
}

fn sync_group_v0_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (generation_id, cur) = take_i32(cur)?;
    let (member_id, cur) = take_nonnull_kstr(cur)?;
    let (assign_count, mut cur) = take_i32(cur)?;
    if assign_count < 0 {
        return None;
    }

    let mut assignments = Vec::new();
    let mut idx = 0i32;
    while idx < assign_count {
        let (m_id, after_id) = take_nonnull_kstr(cur)?;
        let (m_bytes, next_cur) = take_bytes(after_id)?;
        assignments.push((m_id.to_owned(), m_bytes.to_vec()));
        cur = next_cur;
        idx = idx.saturating_add(1);
    }

    let (err, assignment) = backend.sync_group(group_id, generation_id, member_id, &assignments);
    let mut out = Vec::new();
    put_i16(&mut out, err);
    put_bytes(&mut out, &assignment);
    Some(out)
}

fn heartbeat_v0_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (generation_id, cur) = take_i32(cur)?;
    let (member_id, _rest) = take_nonnull_kstr(cur)?;
    let err = backend.heartbeat(group_id, generation_id, member_id);
    let mut out = Vec::new();
    put_i16(&mut out, err);
    Some(out)
}

fn leave_group_v0_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (member_id, _rest) = take_nonnull_kstr(cur)?;
    let err = backend.leave_group(group_id, member_id);
    let mut out = Vec::new();
    put_i16(&mut out, err);
    Some(out)
}

fn offset_commit_v2_response(body: &[u8], backend: &mut StoreMut<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (generation_id, cur) = take_i32(cur)?;
    let (member_id, cur) = take_nonnull_kstr(cur)?;
    let (_retention_time_ms, cur) = take_i64(cur)?;
    let (topic_count, mut cur) = take_i32(cur)?;
    if topic_count < 0 {
        return None;
    }

    let mut topic_replies: Vec<(String, Vec<OffsetCommitPartReply>)> = Vec::new();
    let mut t_idx = 0i32;
    while t_idx < topic_count {
        let (topic, after_name) = take_nonnull_kstr(cur)?;
        let (part_count, mut p_cur) = take_i32(after_name)?;
        if part_count < 0 {
            return None;
        }
        let mut part_replies = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < part_count {
            let (part_id, after_pid) = take_i32(p_cur)?;
            let (offset, after_off) = take_i64(after_pid)?;
            let (metadata, next_p) = take_kstr(after_off)?;
            let err = backend.commit_offset(
                group_id,
                generation_id,
                member_id,
                topic,
                part_id,
                offset,
                metadata,
            );
            part_replies.push((part_id, err));
            p_cur = next_p;
            p_idx = p_idx.saturating_add(1);
        }
        topic_replies.push((topic.to_owned(), part_replies));
        cur = p_cur;
        t_idx = t_idx.saturating_add(1);
    }

    let mut out = Vec::new();
    put_i32(&mut out, topic_replies.len() as i32);
    for (topic, parts) in &topic_replies {
        put_str(&mut out, topic);
        put_i32(&mut out, parts.len() as i32);
        for &(pid, err) in parts {
            put_i32(&mut out, pid);
            put_i16(&mut out, err);
        }
    }
    Some(out)
}

fn offset_fetch_v1_response(body: &[u8], backend: StoreRef<'_>) -> Option<Vec<u8>> {
    let (group_id, cur) = take_nonnull_kstr(body)?;
    let (topic_count, mut cur) = take_i32(cur)?;
    if topic_count < 0 {
        return None;
    }

    let mut topic_replies: Vec<(String, Vec<OffsetFetchPartReply>)> = Vec::new();
    let mut t_idx = 0i32;
    while t_idx < topic_count {
        let (topic, after_name) = take_nonnull_kstr(cur)?;
        let (part_count, mut p_cur) = take_i32(after_name)?;
        if part_count < 0 {
            return None;
        }
        let mut part_replies = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < part_count {
            let (part_id, next_p) = take_i32(p_cur)?;
            let committed = backend.fetch_offset(group_id, topic, part_id);
            part_replies.push((part_id, committed));
            p_cur = next_p;
            p_idx = p_idx.saturating_add(1);
        }
        topic_replies.push((topic.to_owned(), part_replies));
        cur = p_cur;
        t_idx = t_idx.saturating_add(1);
    }

    let mut out = Vec::new();
    put_i32(&mut out, topic_replies.len() as i32);
    for (topic, parts) in &topic_replies {
        put_str(&mut out, topic);
        put_i32(&mut out, parts.len() as i32);
        for (pid, committed) in parts {
            put_i32(&mut out, *pid);
            out.extend_from_slice(&encode_i64_be(committed.offset));
            put_nullable_str(&mut out, committed.metadata.as_deref());
            put_i16(&mut out, committed.error_code);
        }
    }
    Some(out)
}

enum KafkaWireStream {
    Plain(TcpStream),
    #[cfg(feature = "aead")]
    Sealed(astream_aead::SealedStream<TcpStream>),
    #[cfg(feature = "handshake")]
    Roam(astream_aead::RoamStream),
}

impl KafkaWireStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Plain(s) => s.read(buf),
            #[cfg(feature = "aead")]
            Self::Sealed(s) => s.read(buf),
            #[cfg(feature = "handshake")]
            Self::Roam(s) => s.read(buf),
        }
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        match self {
            Self::Plain(s) => s.write_all(buf),
            #[cfg(feature = "aead")]
            Self::Sealed(s) => s.write_all(buf),
            #[cfg(feature = "handshake")]
            Self::Roam(s) => s.write_all(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Plain(s) => s.flush(),
            #[cfg(feature = "aead")]
            Self::Sealed(s) => s.flush(),
            #[cfg(feature = "handshake")]
            Self::Roam(s) => s.flush(),
        }
    }
}

/// Encrypted and mutually-authenticated listener credentials for [`KafkaServer::bind_encrypted`],
/// [`KafkaServer::bind_encrypted_sasl`], `KafkaServer::bind_durable_encrypted`, and
/// `KafkaServer::bind_durable_encrypted_sasl`.
#[cfg(feature = "aead")]
#[derive(Clone)]
pub enum KafkaEncryptedListener {
    /// Pre-shared-key XChaCha20-Poly1305 ordered-record stream (`LEVEL_SEALED_PSK`).
    Sealed {
        /// 32-byte XChaCha20-Poly1305 pre-shared key.
        key: [u8; 32],
    },
    /// Forward-secret ephemeral X25519 + PSK handshake (`LEVEL_HANDSHAKE_FS`).
    #[cfg(feature = "handshake")]
    Handshake {
        /// 32-byte pre-shared authentication key mixed via HKDF-SHA256.
        psk: [u8; 32],
    },
    /// Mutual Ed25519 signed-DH (`LEVEL_MUTUAL_IDENTITY`) verifying clients against
    /// `authorized_clients` with zero shared secrets.
    #[cfg(feature = "identity")]
    Identity {
        /// Server host Ed25519 identity keypair.
        host: Arc<astream_aead::IdentityKeypair>,
        /// Allow-listed client Ed25519 32-byte public keys.
        authorized_clients: Vec<[u8; 32]>,
    },
    /// Mutual CA-certified SIGMA (`LEVEL_CERTIFIED_CA`) with overlapping host-key/CA
    /// rotation and out-of-process `SSH_AUTH_SOCK` signing support.
    #[cfg(feature = "identity")]
    Certified {
        /// Live-rotatable host certificate + signer (`IdentityKeypair` or `SshAgentSigner`).
        host_rotator: astream_aead::HostCertRotator,
        /// Shared CA trust store verifying client `ACRT` certificates.
        client_trust: astream_aead::SharedCertTrust,
    },
}

#[cfg(feature = "aead")]
impl std::fmt::Debug for KafkaEncryptedListener {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sealed { .. } => f.write_str("KafkaEncryptedListener::Sealed(<redacted>)"),
            #[cfg(feature = "handshake")]
            Self::Handshake { .. } => f.write_str("KafkaEncryptedListener::Handshake(<redacted>)"),
            #[cfg(feature = "identity")]
            Self::Identity {
                authorized_clients, ..
            } => write!(
                f,
                "KafkaEncryptedListener::Identity(authorized={})",
                authorized_clients.len()
            ),
            #[cfg(feature = "identity")]
            Self::Certified { .. } => f.write_str("KafkaEncryptedListener::Certified(<ca-trust>)"),
        }
    }
}

#[cfg(feature = "aead")]
impl KafkaEncryptedListener {
    fn upgrade_accepted(
        &self,
        sock: TcpStream,
    ) -> io::Result<(KafkaWireStream, crate::kafka_tls::KafkaSessionSecurity)> {
        let mut sess = crate::kafka_tls::KafkaSessionSecurity::new();
        match self {
            Self::Sealed { key } => {
                let sealed = astream_aead::SealedStream::handshake_server(sock, *key)?;
                sess.upgrade_transport(crate::kafka_tls::LEVEL_SEALED_PSK, None);
                Ok((KafkaWireStream::Sealed(sealed), sess))
            }
            #[cfg(feature = "handshake")]
            Self::Handshake { psk } => {
                let sealed = astream_aead::server_handshake(sock, psk)?;
                sess.upgrade_transport(crate::kafka_tls::LEVEL_HANDSHAKE_FS, None);
                Ok((KafkaWireStream::Sealed(sealed), sess))
            }
            #[cfg(feature = "identity")]
            Self::Identity {
                host,
                authorized_clients,
            } => {
                let (sealed, client_pub) =
                    astream_aead::server_identity_handshake(sock, host, authorized_clients)?;
                sess.upgrade_transport(crate::kafka_tls::LEVEL_MUTUAL_IDENTITY, Some(client_pub));
                Ok((KafkaWireStream::Sealed(sealed), sess))
            }
            #[cfg(feature = "identity")]
            Self::Certified {
                host_rotator,
                client_trust,
            } => {
                let now_ms =
                    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
                        Ok(d) => u64::try_from(d.as_millis()).unwrap_or(u64::MAX),
                        Err(_) => 0,
                    };
                let trust_snap = client_trust.snapshot();
                let (sealed, verified) =
                    astream_aead::server_cert_handshake(sock, host_rotator, &trust_snap, now_ms)?;
                sess.upgrade_transport(
                    crate::kafka_tls::LEVEL_CERTIFIED_CA,
                    Some(verified.subject_pub),
                );
                Ok((KafkaWireStream::Sealed(sealed), sess))
            }
        }
    }
}

#[derive(Clone)]
enum ListenerWireMode {
    Plain,
    #[cfg(feature = "aead")]
    Encrypted(Arc<KafkaEncryptedListener>),
}

impl ListenerWireMode {
    const fn requires_encryption(&self) -> bool {
        match self {
            Self::Plain => false,
            #[cfg(feature = "aead")]
            Self::Encrypted(_) => true,
        }
    }

    fn upgrade_accepted(
        &self,
        sock: TcpStream,
    ) -> io::Result<(KafkaWireStream, crate::kafka_tls::KafkaSessionSecurity)> {
        match self {
            Self::Plain => Ok((
                KafkaWireStream::Plain(sock),
                crate::kafka_tls::KafkaSessionSecurity::new(),
            )),
            #[cfg(feature = "aead")]
            Self::Encrypted(tls) => tls.upgrade_accepted(sock),
        }
    }
}

fn read_kafka_frame(stream: &mut KafkaWireStream) -> io::Result<Option<Vec<u8>>> {
    let mut len_buf = [0u8; 4];
    match stream.read(&mut len_buf) {
        Ok(0) => return Ok(None),
        Ok(mut got) => {
            while got < 4 {
                let Some(rem) = len_buf.get_mut(got..) else {
                    break;
                };
                let n = stream.read(rem)?;
                if n == 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "truncated Kafka frame size prefix",
                    ));
                }
                got = got.saturating_add(n);
            }
        }
        Err(e) => return Err(e),
    }
    let size = decode_i32_be(&len_buf);
    if size <= 0 || (size as usize) > MAX_KAFKA_FRAME_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Kafka frame size outside 1..=MAX_KAFKA_FRAME_LEN",
        ));
    }
    let ulen = size as usize;
    let mut payload = Vec::new();
    let mut chunk = [0u8; 4096];
    while payload.len() < ulen {
        let want = ulen.saturating_sub(payload.len()).min(chunk.len());
        let Some(dst) = chunk.get_mut(..want) else {
            break;
        };
        let n = stream.read(dst)?;
        if n == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated Kafka frame body",
            ));
        }
        if let Some(read_bytes) = dst.get(..n) {
            payload.extend_from_slice(read_bytes);
        }
    }
    Ok(Some(payload))
}

fn serve_kafka_conn(
    sock: TcpStream,
    running: Arc<AtomicBool>,
    backend: Arc<Mutex<KafkaEngine>>,
    cluster: Arc<ClusterMeta>,
    sasl: Option<Arc<crate::sasl::SaslConfig>>,
    wire_mode: ListenerWireMode,
) {
    let policy = crate::kafka_tls::ListenerSecurityPolicy {
        require_encrypted: wire_mode.requires_encryption(),
        require_sasl: sasl.is_some(),
    };
    let (stream, sec_session) = match wire_mode.upgrade_accepted(sock) {
        Ok(pair) => pair,
        Err(_) => return,
    };
    serve_kafka_stream(stream, sec_session, policy, running, backend, cluster, sasl);
}

fn serve_kafka_stream(
    mut stream: KafkaWireStream,
    mut sec_session: crate::kafka_tls::KafkaSessionSecurity,
    policy: crate::kafka_tls::ListenerSecurityPolicy,
    running: Arc<AtomicBool>,
    backend: Arc<Mutex<KafkaEngine>>,
    cluster: Arc<ClusterMeta>,
    sasl: Option<Arc<crate::sasl::SaslConfig>>,
) {
    let mut sasl_session = crate::sasl::SaslSession::new();
    while running.load(Ordering::SeqCst) {
        let req = match read_kafka_frame(&mut stream) {
            Ok(Some(r)) => r,
            Ok(None) | Err(_) => break,
        };
        let resp = if let Some(ref cfg) = sasl {
            let Some((hdr, body_at)) = parse_header(&req) else {
                break;
            };
            if !sasl_session.allows_api(hdr.api_key) {
                break;
            }
            let Some(body) = req.get(body_at..) else {
                break;
            };
            if hdr.api_key == crate::sasl::SASL_HANDSHAKE {
                crate::sasl::respond_sasl_handshake(&hdr, body, cfg, &mut sasl_session)
            } else if hdr.api_key == crate::sasl::SASL_AUTHENTICATE {
                let out =
                    crate::sasl::respond_sasl_authenticate(&hdr, body, cfg, &mut sasl_session);
                if sasl_session.is_authenticated() {
                    sec_session.mark_sasl_authenticated();
                }
                out
            } else if hdr.api_key == API_VERSIONS {
                let Ok(mut guard) = backend.lock() else {
                    break;
                };
                respond_with_engine(&req, &cluster, &mut guard)
            } else {
                if !sec_session.admits_data_plane(&policy) {
                    break;
                }
                let Ok(mut guard) = backend.lock() else {
                    break;
                };
                respond_with_engine(&req, &cluster, &mut guard)
            }
        } else {
            if !sec_session.admits_data_plane(&policy) {
                break;
            }
            let Ok(mut guard) = backend.lock() else {
                break;
            };
            respond_with_engine(&req, &cluster, &mut guard)
        };
        let Some(frame) = resp else {
            break;
        };
        if stream.write_all(&frame).is_err() || stream.flush().is_err() {
            break;
        }
        if sasl.is_some() && sasl_session.is_failed() {
            break;
        }
    }
}

fn accept_kafka_loop(
    listener: TcpListener,
    running: Arc<AtomicBool>,
    conns: Arc<Mutex<Vec<TcpStream>>>,
    backend: Arc<Mutex<KafkaEngine>>,
    cluster: Arc<ClusterMeta>,
    sasl: Option<Arc<crate::sasl::SaslConfig>>,
    wire_mode: ListenerWireMode,
) {
    let mut workers: Vec<JoinHandle<()>> = Vec::new();
    while running.load(Ordering::SeqCst) {
        let Ok((sock, _peer)) = listener.accept() else {
            if !running.load(Ordering::SeqCst) {
                break;
            }
            thread::sleep(Duration::from_millis(10));
            continue;
        };
        if !running.load(Ordering::SeqCst) {
            break;
        }
        let _ = sock.set_nodelay(true);
        let _ = sock.set_read_timeout(Some(Duration::from_secs(5)));
        let _ = sock.set_write_timeout(Some(Duration::from_secs(5)));
        if let Ok(cloned) = sock.try_clone() {
            if let Ok(mut list) = conns.lock() {
                list.push(cloned);
            }
        }
        let st = Arc::clone(&backend);
        let cl = Arc::clone(&cluster);
        let rf = Arc::clone(&running);
        let sc = match &sasl {
            Some(arc) => Some(Arc::clone(arc)),
            None => None,
        };
        let wm = wire_mode.clone();
        if let Ok(jh) =
            thread::Builder::new().spawn(move || serve_kafka_conn(sock, rf, st, cl, sc, wm))
        {
            workers.push(jh);
        }
    }
    if let Ok(mut list) = conns.lock() {
        for s in std::mem::take(&mut *list) {
            let _ = s.shutdown(Shutdown::Both);
        }
    }
    for jh in workers {
        let _ = jh.join();
    }
}

#[cfg(feature = "handshake")]
fn accept_kafka_roam_loop(
    mut listener: astream_aead::RoamListener,
    running: Arc<AtomicBool>,
    roam_conns: Arc<Mutex<Vec<astream_aead::RoamCloser>>>,
    backend: Arc<Mutex<KafkaEngine>>,
    cluster: Arc<ClusterMeta>,
    sasl: Option<Arc<crate::sasl::SaslConfig>>,
) {
    let mut workers: Vec<JoinHandle<()>> = Vec::new();
    while running.load(Ordering::SeqCst) {
        match listener.accept_timeout(Duration::from_millis(20)) {
            Ok(Some(roam_stream)) => {
                if !running.load(Ordering::SeqCst) {
                    break;
                }
                let _ = roam_stream.set_read_timeout(Some(Duration::from_secs(5)));
                let _ = roam_stream.set_write_timeout(Some(Duration::from_secs(5)));
                if let Ok(mut list) = roam_conns.lock() {
                    list.push(roam_stream.closer());
                }
                let st = Arc::clone(&backend);
                let cl = Arc::clone(&cluster);
                let rf = Arc::clone(&running);
                let sc = match &sasl {
                    Some(arc) => Some(Arc::clone(arc)),
                    None => None,
                };
                let policy = crate::kafka_tls::ListenerSecurityPolicy {
                    require_encrypted: true,
                    require_sasl: sc.is_some(),
                };
                let mut sec = crate::kafka_tls::KafkaSessionSecurity::new();
                sec.upgrade_transport(crate::kafka_tls::LEVEL_HANDSHAKE_FS, None);
                if let Ok(jh) = thread::Builder::new().spawn(move || {
                    serve_kafka_stream(
                        KafkaWireStream::Roam(roam_stream),
                        sec,
                        policy,
                        rf,
                        st,
                        cl,
                        sc,
                    )
                }) {
                    workers.push(jh);
                }
            }
            Ok(None) => {}
            Err(_) => break,
        }
    }
    if let Ok(mut list) = roam_conns.lock() {
        for c in std::mem::take(&mut *list) {
            c.shutdown_both();
        }
    }
    listener.shutdown();
    for jh in workers {
        let _ = jh.join();
    }
}

/// Handle to a running live TCP or UDP-roaming [`KafkaServer`]. Stops the accept loop,
/// joins active connection threads, and drops the backend synchronously on `shutdown()` or drop.
pub struct KafkaServerHandle {
    addr: SocketAddr,
    is_udp: bool,
    running: Arc<AtomicBool>,
    conns: Arc<Mutex<Vec<TcpStream>>>,
    #[cfg(feature = "handshake")]
    roam_conns: Arc<Mutex<Vec<astream_aead::RoamCloser>>>,
    acceptor: Option<JoinHandle<()>>,
}

impl KafkaServerHandle {
    /// Bound socket address (useful when started on port `0`).
    #[must_use]
    pub const fn local_addr(&self) -> SocketAddr {
        self.addr
    }

    /// Gracefully stop the listener, close active client connections, and join all
    /// connection threads so any durable backend releases its file locks before return.
    pub fn shutdown(&mut self) {
        if self.running.swap(false, Ordering::SeqCst) {
            if !self.is_udp {
                let _ = TcpStream::connect_timeout(&self.addr, Duration::from_millis(100));
            }
            if let Ok(mut list) = self.conns.lock() {
                for s in std::mem::take(&mut *list) {
                    let _ = s.shutdown(Shutdown::Both);
                }
            }
            #[cfg(feature = "handshake")]
            if let Ok(mut list) = self.roam_conns.lock() {
                for c in std::mem::take(&mut *list) {
                    c.shutdown_both();
                }
            }
        }
        if let Some(h) = self.acceptor.take() {
            let _ = h.join();
        }
    }
}

impl Drop for KafkaServerHandle {
    fn drop(&mut self) {
        self.shutdown();
    }
}

/// Live TCP server speaking 4-byte size-prefixed Kafka frames over [`KafkaEngine`]
/// (`KafkaStore` or `DurableKafkaStore`), optionally encrypted via `KafkaEncryptedListener`
/// (`Sealed`, `Handshake`, or mutual Ed25519 `Identity`) and gated by [`crate::sasl::SaslConfig`].
pub struct KafkaServer;

impl KafkaServer {
    /// Bind `addr` and serve `cluster` + in-memory [`KafkaStore`] on background connection threads.
    pub fn bind(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            None,
            ListenerWireMode::Plain,
        )
    }

    /// Bind `addr` with mandatory SASL authentication (`PLAIN` / `SCRAM-SHA-256`) over in-memory [`KafkaStore`].
    pub fn bind_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            Some(sasl),
            ListenerWireMode::Plain,
        )
    }

    /// Bind `addr` over an encrypted / mutually-authenticated [`KafkaEncryptedListener`] backed by [`KafkaStore`].
    #[cfg(feature = "aead")]
    pub fn bind_encrypted(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
        tls: KafkaEncryptedListener,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            None,
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    /// Bind `addr` over an encrypted / mutually-authenticated [`KafkaEncryptedListener`] AND mandatory SASL authentication.
    #[cfg(feature = "aead")]
    pub fn bind_encrypted_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
        tls: KafkaEncryptedListener,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            Some(sasl),
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    /// Bind `addr` and serve `cluster` + `ShardedBroker`-backed [`crate::durable::DurableKafkaStore`].
    #[cfg(feature = "durable")]
    pub fn bind_durable(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            None,
            ListenerWireMode::Plain,
        )
    }

    /// Bind `addr` with mandatory SASL authentication over `ShardedBroker`-backed [`crate::durable::DurableKafkaStore`].
    #[cfg(feature = "durable")]
    pub fn bind_durable_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            Some(sasl),
            ListenerWireMode::Plain,
        )
    }

    /// Bind `addr` over an encrypted [`KafkaEncryptedListener`] backed by [`crate::durable::DurableKafkaStore`].
    #[cfg(all(feature = "durable", feature = "aead"))]
    pub fn bind_durable_encrypted(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
        tls: KafkaEncryptedListener,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            None,
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    /// Bind `addr` over an encrypted [`KafkaEncryptedListener`] AND mandatory SASL authentication backed by [`crate::durable::DurableKafkaStore`].
    #[cfg(all(feature = "durable", feature = "aead"))]
    pub fn bind_durable_encrypted_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
        tls: KafkaEncryptedListener,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            Some(sasl),
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    /// Bind `addr` and serve `cluster` + [`KafkaEngine`] on background connection threads.
    pub fn bind_engine(
        addr: &str,
        cluster: ClusterMeta,
        engine: KafkaEngine,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(addr, cluster, engine, None, ListenerWireMode::Plain)
    }

    /// Bind `addr` with mandatory SASL authentication over [`KafkaEngine`].
    pub fn bind_engine_sasl(
        addr: &str,
        cluster: ClusterMeta,
        engine: KafkaEngine,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(addr, cluster, engine, Some(sasl), ListenerWireMode::Plain)
    }

    /// Bind `addr` over an encrypted [`KafkaEncryptedListener`] serving [`KafkaEngine`].
    #[cfg(feature = "aead")]
    pub fn bind_engine_encrypted(
        addr: &str,
        cluster: ClusterMeta,
        engine: KafkaEngine,
        tls: KafkaEncryptedListener,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            engine,
            None,
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    /// Bind `addr` over an encrypted [`KafkaEncryptedListener`] AND mandatory SASL authentication serving [`KafkaEngine`].
    #[cfg(feature = "aead")]
    pub fn bind_engine_encrypted_sasl(
        addr: &str,
        cluster: ClusterMeta,
        engine: KafkaEngine,
        tls: KafkaEncryptedListener,
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_with_security(
            addr,
            cluster,
            engine,
            Some(sasl),
            ListenerWireMode::Encrypted(Arc::new(tls)),
        )
    }

    fn bind_engine_with_security(
        addr: &str,
        mut cluster: ClusterMeta,
        engine: KafkaEngine,
        sasl: Option<crate::sasl::SaslConfig>,
        wire_mode: ListenerWireMode,
    ) -> io::Result<KafkaServerHandle> {
        let listener = TcpListener::bind(addr)?;
        let bound = listener.local_addr()?;
        if cluster.broker.port == 0 {
            cluster.broker.port = i32::from(bound.port());
        }
        let running = Arc::new(AtomicBool::new(true));
        let conns: Arc<Mutex<Vec<TcpStream>>> = Arc::new(Mutex::new(Vec::new()));
        let shared_backend = Arc::new(Mutex::new(engine));
        let shared_cluster = Arc::new(cluster);
        let shared_sasl = match sasl {
            Some(cfg) => Some(Arc::new(cfg)),
            None => None,
        };

        let r_flag = Arc::clone(&running);
        let c_list = Arc::clone(&conns);
        let acceptor = thread::Builder::new().spawn(move || {
            accept_kafka_loop(
                listener,
                r_flag,
                c_list,
                shared_backend,
                shared_cluster,
                shared_sasl,
                wire_mode,
            )
        })?;

        Ok(KafkaServerHandle {
            addr: bound,
            is_udp: false,
            running,
            conns,
            #[cfg(feature = "handshake")]
            roam_conns: Arc::new(Mutex::new(Vec::new())),
            acceptor: Some(acceptor),
        })
    }

    /// Bind UDP `addr` over zero-gap AEAD-over-UDP connection migration (`AROM` v1) backed by [`KafkaStore`].
    #[cfg(feature = "handshake")]
    pub fn bind_roaming(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
        psk: [u8; 32],
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_roaming_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            psk,
            None,
        )
    }

    /// Bind UDP `addr` over zero-gap AEAD-over-UDP connection migration AND mandatory SASL authentication backed by [`KafkaStore`].
    #[cfg(feature = "handshake")]
    pub fn bind_roaming_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: KafkaStore,
        psk: [u8; 32],
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_roaming_with_security(
            addr,
            cluster,
            KafkaEngine::Memory(store),
            psk,
            Some(sasl),
        )
    }

    /// Bind UDP `addr` over zero-gap AEAD-over-UDP connection migration backed by [`crate::durable::DurableKafkaStore`].
    #[cfg(all(feature = "durable", feature = "handshake"))]
    pub fn bind_durable_roaming(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
        psk: [u8; 32],
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_roaming_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            psk,
            None,
        )
    }

    /// Bind UDP `addr` over zero-gap AEAD-over-UDP connection migration AND mandatory SASL authentication backed by [`crate::durable::DurableKafkaStore`].
    #[cfg(all(feature = "durable", feature = "handshake"))]
    pub fn bind_durable_roaming_sasl(
        addr: &str,
        cluster: ClusterMeta,
        store: crate::durable::DurableKafkaStore,
        psk: [u8; 32],
        sasl: crate::sasl::SaslConfig,
    ) -> io::Result<KafkaServerHandle> {
        Self::bind_engine_roaming_with_security(
            addr,
            cluster,
            KafkaEngine::Durable(store),
            psk,
            Some(sasl),
        )
    }

    #[cfg(feature = "handshake")]
    fn bind_engine_roaming_with_security(
        addr: &str,
        mut cluster: ClusterMeta,
        engine: KafkaEngine,
        psk: [u8; 32],
        sasl: Option<crate::sasl::SaslConfig>,
    ) -> io::Result<KafkaServerHandle> {
        let listener = astream_aead::RoamListener::bind(addr, psk)?;
        let bound = listener.local_addr();
        if cluster.broker.port == 0 {
            cluster.broker.port = i32::from(bound.port());
        }
        let running = Arc::new(AtomicBool::new(true));
        let conns: Arc<Mutex<Vec<TcpStream>>> = Arc::new(Mutex::new(Vec::new()));
        let roam_conns: Arc<Mutex<Vec<astream_aead::RoamCloser>>> =
            Arc::new(Mutex::new(Vec::new()));
        let shared_backend = Arc::new(Mutex::new(engine));
        let shared_cluster = Arc::new(cluster);
        let shared_sasl = match sasl {
            Some(cfg) => Some(Arc::new(cfg)),
            None => None,
        };

        let r_flag = Arc::clone(&running);
        let rc_list = Arc::clone(&roam_conns);
        let acceptor = thread::Builder::new().spawn(move || {
            accept_kafka_roam_loop(
                listener,
                r_flag,
                rc_list,
                shared_backend,
                shared_cluster,
                shared_sasl,
            )
        })?;

        Ok(KafkaServerHandle {
            addr: bound,
            is_udp: true,
            running,
            conns,
            roam_conns,
            acceptor: Some(acceptor),
        })
    }
}

/// Synchronous TCP client for driving [`KafkaServer`] over real 4-byte BE size-prefixed
/// Kafka wire frames across all 12 supported APIs (plaintext or `SealedStream`-encrypted).
pub struct KafkaClient {
    stream: KafkaWireStream,
    next_corr: i32,
    client_id: String,
}

impl KafkaClient {
    fn open_configured_socket(addr: SocketAddr) -> io::Result<TcpStream> {
        let sock = TcpStream::connect(addr)?;
        sock.set_nodelay(true)?;
        sock.set_read_timeout(Some(Duration::from_secs(5)))?;
        sock.set_write_timeout(Some(Duration::from_secs(5)))?;
        Ok(sock)
    }

    /// Connect to a plaintext Kafka TCP endpoint at `addr`.
    pub fn connect(addr: SocketAddr, client_id: &str) -> io::Result<Self> {
        let sock = Self::open_configured_socket(addr)?;
        Ok(Self {
            stream: KafkaWireStream::Plain(sock),
            next_corr: 1,
            client_id: client_id.to_owned(),
        })
    }

    /// Connect to a pre-shared-key `Sealed` (`XChaCha20-Poly1305`) Kafka endpoint at `addr`.
    #[cfg(feature = "aead")]
    pub fn connect_sealed(addr: SocketAddr, client_id: &str, key: [u8; 32]) -> io::Result<Self> {
        let sock = Self::open_configured_socket(addr)?;
        let sealed = astream_aead::SealedStream::handshake_client(sock, key)?;
        Ok(Self {
            stream: KafkaWireStream::Sealed(sealed),
            next_corr: 1,
            client_id: client_id.to_owned(),
        })
    }

    /// Connect to a forward-secret X25519 + PSK `Handshake` Kafka endpoint at `addr`.
    #[cfg(feature = "handshake")]
    pub fn connect_handshake(addr: SocketAddr, client_id: &str, psk: [u8; 32]) -> io::Result<Self> {
        let sock = Self::open_configured_socket(addr)?;
        let sealed = astream_aead::client_handshake(sock, &psk)?;
        Ok(Self {
            stream: KafkaWireStream::Sealed(sealed),
            next_corr: 1,
            client_id: client_id.to_owned(),
        })
    }

    /// Connect to a mutual Ed25519 `Identity` signed-DH Kafka endpoint at `addr`, pinning
    /// `expected_server` and proving `client_identity`.
    #[cfg(feature = "identity")]
    pub fn connect_identity(
        addr: SocketAddr,
        client_id: &str,
        client_identity: &astream_aead::IdentityKeypair,
        expected_server: &[u8; 32],
    ) -> io::Result<Self> {
        let sock = Self::open_configured_socket(addr)?;
        let sealed =
            astream_aead::client_identity_handshake(sock, client_identity, expected_server)?;
        Ok(Self {
            stream: KafkaWireStream::Sealed(sealed),
            next_corr: 1,
            client_id: client_id.to_owned(),
        })
    }

    /// Connect to a mutual CA-certified SIGMA (`KafkaEncryptedListener::Certified`) Kafka
    /// endpoint at `addr` using an [`astream_aead::IdentitySigner`] (`IdentityKeypair` or
    /// `SshAgentSigner`) and `client_cert`, verifying the broker's host certificate against
    /// `server_trust` and `expected_host_principal`.
    #[cfg(feature = "identity")]
    pub fn connect_certified(
        addr: SocketAddr,
        client_id: &str,
        client_signer: &astream_aead::IdentitySigner,
        client_cert: &astream_aead::IdentityCertificate,
        server_trust: &astream_aead::CertTrustStore,
        expected_host_principal: Option<&str>,
    ) -> io::Result<Self> {
        let (cli, _) = Self::connect_certified_verified(
            addr,
            client_id,
            client_signer,
            client_cert,
            server_trust,
            expected_host_principal,
        )?;
        Ok(cli)
    }

    /// Like [`Self::connect_certified`], returning both the connected [`KafkaClient`] and the
    /// verified broker host certificate metadata ([`astream_aead::VerifiedPeerCert`]).
    #[cfg(feature = "identity")]
    pub fn connect_certified_verified(
        addr: SocketAddr,
        client_id: &str,
        client_signer: &astream_aead::IdentitySigner,
        client_cert: &astream_aead::IdentityCertificate,
        server_trust: &astream_aead::CertTrustStore,
        expected_host_principal: Option<&str>,
    ) -> io::Result<(Self, astream_aead::VerifiedPeerCert)> {
        let now_ms = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => u64::try_from(d.as_millis()).unwrap_or(u64::MAX),
            Err(_) => 0,
        };
        let sock = Self::open_configured_socket(addr)?;
        let (sealed, verified_host) = astream_aead::client_cert_handshake(
            sock,
            client_signer,
            client_cert,
            server_trust,
            expected_host_principal,
            now_ms,
        )?;
        Ok((
            Self {
                stream: KafkaWireStream::Sealed(sealed),
                next_corr: 1,
                client_id: client_id.to_owned(),
            },
            verified_host,
        ))
    }

    /// Connect to a zero-gap AEAD-over-UDP roaming Kafka endpoint (`KafkaServer::bind_roaming*`)
    /// at `addr`, returning both the connected [`KafkaClient`] and its [`astream_aead::RoamHandle`]
    /// path-migration controller.
    #[cfg(feature = "handshake")]
    pub fn connect_roaming(
        addr: SocketAddr,
        client_id: &str,
        psk: [u8; 32],
    ) -> io::Result<(Self, astream_aead::RoamHandle)> {
        let (roam_stream, roam_handle) = astream_aead::client_roam_connect(addr, &psk)?;
        roam_stream.set_read_timeout(Some(Duration::from_secs(5)))?;
        roam_stream.set_write_timeout(Some(Duration::from_secs(5)))?;
        Ok((
            Self {
                stream: KafkaWireStream::Roam(roam_stream),
                next_corr: 1,
                client_id: client_id.to_owned(),
            },
            roam_handle,
        ))
    }

    fn send_raw(&mut self, api_key: i16, api_version: i16, body: &[u8]) -> io::Result<Vec<u8>> {
        let corr = self.next_corr;
        self.next_corr = self.next_corr.wrapping_add(1);

        let mut req = Vec::new();
        put_i16(&mut req, api_key);
        put_i16(&mut req, api_version);
        put_i32(&mut req, corr);
        put_str(&mut req, &self.client_id);
        if is_flexible_request(api_key, api_version) {
            put_empty_tags(&mut req);
        }
        req.extend_from_slice(body);

        let Ok(req_len) = i32::try_from(req.len()) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Kafka request exceeds i32::MAX",
            ));
        };
        let mut framed = Vec::new();
        framed.extend_from_slice(&encode_i32_be(req_len));
        framed.extend_from_slice(&req);
        self.stream.write_all(&framed)?;
        self.stream.flush()?;

        let Some(resp) = read_kafka_frame(&mut self.stream)? else {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "server closed connection",
            ));
        };
        let &[c0, c1, c2, c3, ref resp_body @ ..] = resp.as_slice() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Kafka response header",
            ));
        };
        let got_corr = decode_i32_be(&[c0, c1, c2, c3]);
        if got_corr != corr {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Kafka correlation_id mismatch",
            ));
        }
        if !resp_body.is_empty() && is_flexible_response(api_key, api_version) {
            let Some(after_hdr_tags) = skip_tag_buffer(resp_body) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed KIP-482 ResponseHeader v1 TAG_BUFFER",
                ));
            };
            return Ok(after_hdr_tags.to_vec());
        }
        Ok(resp_body.to_vec())
    }

    /// Issue an `ApiVersions` request at `version` (`v0..=3` native, `v4+` KIP-511 downgrade),
    /// returning `(error_code, Vec<(key, min, max)>)`.
    pub fn api_versions(&mut self, version: i16) -> io::Result<(i16, Vec<ApiVersionEntry>)> {
        let mut req_body = Vec::new();
        if version >= 3 {
            put_compact_str(&mut req_body, "astream-kafka");
            put_compact_str(&mut req_body, "0.2.0");
            put_empty_tags(&mut req_body);
        }
        let body = self.send_raw(API_VERSIONS, version, &req_body)?;
        let Some((err, cur)) = take_i16(&body) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ApiVersions",
            ));
        };
        if err == NONE && version >= 3 {
            let Some((raw_count, mut cur)) = take_uvarint(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short ApiVersions v3 compact count",
                ));
            };
            let count = raw_count.saturating_sub(1);
            let mut entries = Vec::new();
            let mut idx = 0u32;
            while idx < count {
                let Some((k, c1)) = take_i16(cur) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short ApiVersions v3 entry",
                    ));
                };
                let Some((min_v, c2)) = take_i16(c1) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short ApiVersions v3 min",
                    ));
                };
                let Some((max_v, c3)) = take_i16(c2) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short ApiVersions v3 max",
                    ));
                };
                let Some(c4) = skip_tag_buffer(c3) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "malformed ApiVersions v3 entry tags",
                    ));
                };
                entries.push((k, min_v, max_v));
                cur = c4;
                idx = idx.saturating_add(1);
            }
            let Some((_throttle_ms, after_thr)) = take_i32(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short ApiVersions v3 throttle",
                ));
            };
            let Some(_after_tags) = skip_tag_buffer(after_thr) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed ApiVersions v3 body tags",
                ));
            };
            return Ok((err, entries));
        }

        let Some((count, mut cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ApiVersions count",
            ));
        };
        let mut entries = Vec::new();
        let mut idx = 0i32;
        while idx < count && cur.len() >= 6 {
            let (k, c1) = match take_i16(cur) {
                Some(v) => v,
                None => break,
            };
            let (min_v, c2) = match take_i16(c1) {
                Some(v) => v,
                None => break,
            };
            let (max_v, c3) = match take_i16(c2) {
                Some(v) => v,
                None => break,
            };
            entries.push((k, min_v, max_v));
            cur = c3;
            idx = idx.saturating_add(1);
        }
        Ok((err, entries))
    }

    /// Issue a `Metadata` v0 request (`topics.is_empty()` queries all topics), returning
    /// `(broker_meta, Vec<(topic_error_code, topic_name, partition_ids)>)`.
    #[allow(clippy::type_complexity)]
    pub fn metadata(
        &mut self,
        topics: &[&str],
    ) -> io::Result<(BrokerMeta, Vec<(i16, String, Vec<i32>)>)> {
        let mut req_body = Vec::new();
        put_i32(&mut req_body, topics.len() as i32);
        for t in topics {
            put_str(&mut req_body, t);
        }
        let resp = self.send_raw(METADATA, 0, &req_body)?;
        let Some((b_count, mut cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata brokers",
            ));
        };
        if b_count <= 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Metadata missing broker entry",
            ));
        }
        let mut first_broker: Option<BrokerMeta> = None;
        let mut b_idx = 0i32;
        while b_idx < b_count {
            let Some((node_id, c1)) = take_i32(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata node_id",
                ));
            };
            let Some((host, c2)) = take_nonnull_kstr(c1) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata host",
                ));
            };
            let Some((port, c3)) = take_i32(c2) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata port",
                ));
            };
            if first_broker.is_none() {
                first_broker = Some(BrokerMeta {
                    node_id,
                    host: host.to_owned(),
                    port,
                });
            }
            cur = c3;
            b_idx = b_idx.saturating_add(1);
        }
        let Some(broker) = first_broker else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "missing Metadata broker",
            ));
        };
        let Some((t_count, mut t_cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata topics",
            ));
        };
        let mut out_topics = Vec::new();
        let mut t_idx = 0i32;
        while t_idx < t_count {
            let Some((t_err, c1)) = take_i16(t_cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata topic err",
                ));
            };
            let Some((t_name, c2)) = take_nonnull_kstr(c1) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata topic name",
                ));
            };
            let Some((p_count, mut p_cur)) = take_i32(c2) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata part count",
                ));
            };
            let mut part_ids = Vec::new();
            let mut p_idx = 0i32;
            while p_idx < p_count {
                let Some((_p_err, pc1)) = take_i16(p_cur) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata part err",
                    ));
                };
                let Some((pid, pc2)) = take_i32(pc1) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata part id",
                    ));
                };
                let Some((_leader, pc3)) = take_i32(pc2) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata leader",
                    ));
                };
                let Some((rep_len, mut pc4)) = take_i32(pc3) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata replicas",
                    ));
                };
                let mut r_idx = 0i32;
                while r_idx < rep_len {
                    let Some((_r, next_r)) = take_i32(pc4) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "short Metadata replica",
                        ));
                    };
                    pc4 = next_r;
                    r_idx = r_idx.saturating_add(1);
                }
                let Some((isr_len, mut pc5)) = take_i32(pc4) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata isr",
                    ));
                };
                let mut i_idx = 0i32;
                while i_idx < isr_len {
                    let Some((_i, next_i)) = take_i32(pc5) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "short Metadata isr node",
                        ));
                    };
                    pc5 = next_i;
                    i_idx = i_idx.saturating_add(1);
                }
                part_ids.push(pid);
                p_cur = pc5;
                p_idx = p_idx.saturating_add(1);
            }
            out_topics.push((t_err, t_name.to_owned(), part_ids));
            t_cur = p_cur;
            t_idx = t_idx.saturating_add(1);
        }
        Ok((broker, out_topics))
    }

    /// Produce one [`RecordBatchV2`] to `(topic, partition)`, returning `(error_code, base_offset)`.
    pub fn produce(
        &mut self,
        topic: &str,
        partition: i32,
        batch: &RecordBatchV2,
    ) -> io::Result<(i16, i64)> {
        let Some(raw_batch) = encode_record_batch_v2(batch) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid RecordBatchV2",
            ));
        };
        self.produce_raw(topic, partition, &raw_batch)
    }

    /// Produce pre-encoded (or intentionally corrupted) RecordBatch bytes to `(topic, partition)`.
    pub fn produce_raw(
        &mut self,
        topic: &str,
        partition: i32,
        raw_batch: &[u8],
    ) -> io::Result<(i16, i64)> {
        let mut body = Vec::new();
        put_i16(&mut body, -1);
        put_i16(&mut body, -1);
        put_i32(&mut body, 5_000);
        put_i32(&mut body, 1);
        put_str(&mut body, topic);
        put_i32(&mut body, 1);
        put_i32(&mut body, partition);
        put_bytes(&mut body, raw_batch);

        let resp = self.send_raw(PRODUCE, 3, &body)?;
        let Some((_t_count, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce reply",
            ));
        };
        let Some((_t_name, cur)) = take_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce topic",
            ));
        };
        let Some((_p_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce parts",
            ));
        };
        let Some((_pid, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce pid",
            ));
        };
        let Some((err, cur)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce err",
            ));
        };
        let Some((base_off, _cur)) = take_i64(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Produce offset",
            ));
        };
        Ok((err, base_off))
    }

    /// Fetch decoded [`RecordBatchV2`] batches from `(topic, partition)` starting at
    /// `fetch_offset`, returning `(error_code, high_watermark, batches)`.
    pub fn fetch(
        &mut self,
        topic: &str,
        partition: i32,
        fetch_offset: i64,
        max_bytes: i32,
    ) -> io::Result<(i16, i64, Vec<RecordBatchV2>)> {
        let mut body = Vec::new();
        put_i32(&mut body, -1);
        put_i32(&mut body, 100);
        put_i32(&mut body, 1);
        put_i32(&mut body, max_bytes);
        body.push(0u8);
        put_i32(&mut body, 1);
        put_str(&mut body, topic);
        put_i32(&mut body, 1);
        put_i32(&mut body, partition);
        body.extend_from_slice(&encode_i64_be(fetch_offset));
        put_i32(&mut body, max_bytes);

        let resp = self.send_raw(FETCH, 4, &body)?;
        let Some((_throttle, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch reply",
            ));
        };
        let Some((_t_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch topics",
            ));
        };
        let Some((_t_name, cur)) = take_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch topic",
            ));
        };
        let Some((_p_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch parts",
            ));
        };
        let Some((_pid, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch pid",
            ));
        };
        let Some((err, cur)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch err",
            ));
        };
        let Some((hw, cur)) = take_i64(cur) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short Fetch hw"));
        };
        let Some((_lso, cur)) = take_i64(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch lso",
            ));
        };
        let Some((_aborted, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch aborted",
            ));
        };
        let Some((raw_opt, _rest)) = take_nullable_bytes(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Fetch records",
            ));
        };

        let mut batches = Vec::new();
        if let Some(mut slice) = raw_opt {
            while !slice.is_empty() {
                let Ok((b, used)) = decode_record_batch_v2(slice) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "invalid RecordBatch v2 in Fetch response",
                    ));
                };
                batches.push(b);
                slice = match slice.get(used..) {
                    Some(rem) => rem,
                    None => &[],
                };
            }
        }
        Ok((err, hw, batches))
    }

    /// Issue a `ListOffsets` v1 request (`-2` earliest, `-1` latest, `>= 0` timestamp),
    /// returning `(error_code, timestamp, offset)`.
    pub fn list_offsets(
        &mut self,
        topic: &str,
        partition: i32,
        timestamp: i64,
    ) -> io::Result<(i16, i64, i64)> {
        let mut body = Vec::new();
        put_i32(&mut body, -1);
        put_i32(&mut body, 1);
        put_str(&mut body, topic);
        put_i32(&mut body, 1);
        put_i32(&mut body, partition);
        body.extend_from_slice(&encode_i64_be(timestamp));

        let resp = self.send_raw(LIST_OFFSETS, 1, &body)?;
        let Some((_t_count, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets",
            ));
        };
        let Some((_t_name, cur)) = take_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets topic",
            ));
        };
        let Some((_p_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets parts",
            ));
        };
        let Some((_pid, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets pid",
            ));
        };
        let Some((err, cur)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets err",
            ));
        };
        let Some((ts, cur)) = take_i64(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets ts",
            ));
        };
        let Some((off, _cur)) = take_i64(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short ListOffsets off",
            ));
        };
        Ok((err, ts, off))
    }

    /// Issue a KIP-482 flexible `Metadata` v9 request (`topics = None` queries all topics),
    /// returning `(broker_meta, cluster_id, Vec<(topic_error_code, topic_name, partition_ids)>)`.
    #[allow(clippy::type_complexity)]
    pub fn metadata_v9(
        &mut self,
        topics: Option<&[&str]>,
    ) -> io::Result<(BrokerMeta, Option<String>, Vec<(i16, String, Vec<i32>)>)> {
        let mut req_body = Vec::new();
        match topics {
            None => put_uvarint(&mut req_body, 0),
            Some(list) => {
                put_uvarint(&mut req_body, (list.len() as u32).saturating_add(1));
                for &t in list {
                    put_compact_str(&mut req_body, t);
                    put_empty_tags(&mut req_body);
                }
            }
        }
        req_body.push(0); // allow_auto_topic_creation
        req_body.push(0); // include_cluster_authorized_operations
        req_body.push(0); // include_topic_authorized_operations
        put_empty_tags(&mut req_body);

        let resp = self.send_raw(METADATA, 9, &req_body)?;
        let Some((_throttle_ms, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 throttle",
            ));
        };
        let Some((raw_b_count, mut cur)) = take_uvarint(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 brokers",
            ));
        };
        let b_count = raw_b_count.saturating_sub(1);
        if b_count == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Metadata v9 missing broker entry",
            ));
        }
        let mut first_broker: Option<BrokerMeta> = None;
        let mut b_idx = 0u32;
        while b_idx < b_count {
            let Some((node_id, c1)) = take_i32(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 node_id",
                ));
            };
            let Some((host, c2)) = take_compact_str(c1) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 host",
                ));
            };
            let Some((port, c3)) = take_i32(c2) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 port",
                ));
            };
            let Some((_rack, c4)) = take_compact_nullable_str(c3) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 rack",
                ));
            };
            let Some(c5) = skip_tag_buffer(c4) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed Metadata v9 broker tags",
                ));
            };
            if first_broker.is_none() {
                first_broker = Some(BrokerMeta {
                    node_id,
                    host: host.to_owned(),
                    port,
                });
            }
            cur = c5;
            b_idx = b_idx.saturating_add(1);
        }
        let Some(broker) = first_broker else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "missing Metadata v9 broker",
            ));
        };
        let Some((cluster_id_opt, c_after_cid)) = take_compact_nullable_str(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 cluster_id",
            ));
        };
        let cluster_id = opt_str_owned(cluster_id_opt);
        let Some((_controller_id, c_after_ctrl)) = take_i32(c_after_cid) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 controller_id",
            ));
        };
        let Some((raw_t_count, mut t_cur)) = take_uvarint(c_after_ctrl) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 topics",
            ));
        };
        let t_count = raw_t_count.saturating_sub(1);
        let mut out_topics = Vec::new();
        let mut t_idx = 0u32;
        while t_idx < t_count {
            let Some((t_err, tc1)) = take_i16(t_cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 topic err",
                ));
            };
            let Some((t_name, tc2)) = take_compact_str(tc1) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 topic name",
                ));
            };
            let Some((_is_internal, tc3)) = take_i8(tc2) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 is_internal",
                ));
            };
            let Some((raw_p_count, mut p_cur)) = take_uvarint(tc3) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 part count",
                ));
            };
            let p_count = raw_p_count.saturating_sub(1);
            let mut part_ids = Vec::new();
            let mut p_idx = 0u32;
            while p_idx < p_count {
                let Some((_p_err, pc1)) = take_i16(p_cur) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 part err",
                    ));
                };
                let Some((pid, pc2)) = take_i32(pc1) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 pid",
                    ));
                };
                let Some((_leader, pc3)) = take_i32(pc2) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 leader",
                    ));
                };
                let Some((_leader_ep, pc4)) = take_i32(pc3) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 leader_epoch",
                    ));
                };
                let Some((raw_rep, mut pc5)) = take_uvarint(pc4) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 replicas",
                    ));
                };
                let mut r_idx = 0u32;
                while r_idx < raw_rep.saturating_sub(1) {
                    let Some((_r, next_r)) = take_i32(pc5) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "short Metadata v9 replica",
                        ));
                    };
                    pc5 = next_r;
                    r_idx = r_idx.saturating_add(1);
                }
                let Some((raw_isr, mut pc6)) = take_uvarint(pc5) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 isr",
                    ));
                };
                let mut i_idx = 0u32;
                while i_idx < raw_isr.saturating_sub(1) {
                    let Some((_i, next_i)) = take_i32(pc6) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "short Metadata v9 isr node",
                        ));
                    };
                    pc6 = next_i;
                    i_idx = i_idx.saturating_add(1);
                }
                let Some((raw_off, mut pc7)) = take_uvarint(pc6) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short Metadata v9 offline_replicas",
                    ));
                };
                let mut o_idx = 0u32;
                while o_idx < raw_off.saturating_sub(1) {
                    let Some((_o, next_o)) = take_i32(pc7) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "short Metadata v9 offline node",
                        ));
                    };
                    pc7 = next_o;
                    o_idx = o_idx.saturating_add(1);
                }
                let Some(pc8) = skip_tag_buffer(pc7) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "malformed Metadata v9 partition tags",
                    ));
                };
                part_ids.push(pid);
                p_cur = pc8;
                p_idx = p_idx.saturating_add(1);
            }
            let Some((_auth_ops, after_ops)) = take_i32(p_cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short Metadata v9 topic_authorized_operations",
                ));
            };
            let Some(after_t_tags) = skip_tag_buffer(after_ops) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed Metadata v9 topic tags",
                ));
            };
            out_topics.push((t_err, t_name.to_owned(), part_ids));
            t_cur = after_t_tags;
            t_idx = t_idx.saturating_add(1);
        }
        let Some((_cluster_ops, after_cops)) = take_i32(t_cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Metadata v9 cluster_authorized_operations",
            ));
        };
        let Some(_rem) = skip_tag_buffer(after_cops) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "malformed Metadata v9 body tags",
            ));
        };
        Ok((broker, cluster_id, out_topics))
    }

    /// Issue a `FindCoordinator` v0 request for `group_id`.
    pub fn find_coordinator(&mut self, group_id: &str) -> io::Result<(i16, BrokerMeta)> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        let resp = self.send_raw(FIND_COORDINATOR, 0, &body)?;
        let Some((err, cur)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator",
            ));
        };
        let Some((node_id, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator node_id",
            ));
        };
        let Some((host, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator host",
            ));
        };
        let Some((port, _rest)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator port",
            ));
        };
        Ok((
            err,
            BrokerMeta {
                node_id,
                host: host.to_owned(),
                port,
            },
        ))
    }

    /// Issue a KIP-482 flexible `FindCoordinator` v3 request for `group_id` (`key_type = 0`).
    pub fn find_coordinator_v3(&mut self, group_id: &str) -> io::Result<(i16, BrokerMeta)> {
        let mut body = Vec::new();
        put_compact_str(&mut body, group_id);
        body.push(0); // key_type = GROUP (0)
        put_empty_tags(&mut body);
        let resp = self.send_raw(FIND_COORDINATOR, 3, &body)?;
        let Some((_throttle_ms, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 throttle",
            ));
        };
        let Some((err, cur)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 err",
            ));
        };
        let Some((_err_msg, cur)) = take_compact_nullable_str(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 error_message",
            ));
        };
        let Some((node_id, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 node_id",
            ));
        };
        let Some((host, cur)) = take_compact_str(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 host",
            ));
        };
        let Some((port, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short FindCoordinator v3 port",
            ));
        };
        let Some(_rem) = skip_tag_buffer(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "malformed FindCoordinator v3 body tags",
            ));
        };
        Ok((
            err,
            BrokerMeta {
                node_id,
                host: host.to_owned(),
                port,
            },
        ))
    }

    /// Issue a `JoinGroup` v0 request.
    pub fn join_group(
        &mut self,
        group_id: &str,
        session_timeout_ms: i32,
        member_id: &str,
        protocol_type: &str,
        protocols: &[(&str, &[u8])],
    ) -> io::Result<JoinGroupResult> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_i32(&mut body, session_timeout_ms);
        put_str(&mut body, member_id);
        put_str(&mut body, protocol_type);
        put_i32(&mut body, protocols.len() as i32);
        for &(p_name, p_meta) in protocols {
            put_str(&mut body, p_name);
            put_bytes(&mut body, p_meta);
        }

        let resp = self.send_raw(JOIN_GROUP, 0, &body)?;
        let Some((error_code, cur)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup err",
            ));
        };
        let Some((generation_id, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup generation",
            ));
        };
        let Some((group_protocol, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup protocol",
            ));
        };
        let Some((leader_id, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup leader",
            ));
        };
        let Some((assigned_member, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup member_id",
            ));
        };
        let Some((m_count, mut m_cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short JoinGroup members",
            ));
        };
        let mut members = Vec::new();
        let mut idx = 0i32;
        while idx < m_count {
            let Some((m_id, mc1)) = take_nonnull_kstr(m_cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short JoinGroup member entry",
                ));
            };
            let Some((m_meta, mc2)) = take_bytes(mc1) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short JoinGroup member meta",
                ));
            };
            members.push((m_id.to_owned(), m_meta.to_vec()));
            m_cur = mc2;
            idx = idx.saturating_add(1);
        }
        Ok(JoinGroupResult {
            error_code,
            generation_id,
            group_protocol: group_protocol.to_owned(),
            leader_id: leader_id.to_owned(),
            member_id: assigned_member.to_owned(),
            members,
        })
    }

    /// Issue a `SyncGroup` v0 request, returning `(error_code, member_assignment)`.
    pub fn sync_group(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        assignments: &[(&str, &[u8])],
    ) -> io::Result<(i16, Vec<u8>)> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_i32(&mut body, generation_id);
        put_str(&mut body, member_id);
        put_i32(&mut body, assignments.len() as i32);
        for &(m_id, m_bytes) in assignments {
            put_str(&mut body, m_id);
            put_bytes(&mut body, m_bytes);
        }
        let resp = self.send_raw(SYNC_GROUP, 0, &body)?;
        let Some((err, cur)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short SyncGroup err",
            ));
        };
        let Some((assign, _rest)) = take_bytes(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short SyncGroup assignment",
            ));
        };
        Ok((err, assign.to_vec()))
    }

    /// Issue a `Heartbeat` v0 request.
    pub fn heartbeat(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
    ) -> io::Result<i16> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_i32(&mut body, generation_id);
        put_str(&mut body, member_id);
        let resp = self.send_raw(HEARTBEAT, 0, &body)?;
        let Some((err, _rest)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short Heartbeat",
            ));
        };
        Ok(err)
    }

    /// Issue a `LeaveGroup` v0 request.
    pub fn leave_group(&mut self, group_id: &str, member_id: &str) -> io::Result<i16> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_str(&mut body, member_id);
        let resp = self.send_raw(LEAVE_GROUP, 0, &body)?;
        let Some((err, _rest)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short LeaveGroup",
            ));
        };
        Ok(err)
    }

    /// Issue an `OffsetCommit` v2 request for one `(topic, partition)`.
    #[allow(clippy::too_many_arguments)]
    pub fn offset_commit(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        topic: &str,
        partition: i32,
        offset: i64,
        metadata: Option<&str>,
    ) -> io::Result<i16> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_i32(&mut body, generation_id);
        put_str(&mut body, member_id);
        body.extend_from_slice(&encode_i64_be(-1));
        put_i32(&mut body, 1);
        put_str(&mut body, topic);
        put_i32(&mut body, 1);
        put_i32(&mut body, partition);
        body.extend_from_slice(&encode_i64_be(offset));
        put_nullable_str(&mut body, metadata);

        let resp = self.send_raw(OFFSET_COMMIT, 2, &body)?;
        let Some((_t_count, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetCommit",
            ));
        };
        let Some((_t_name, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetCommit topic",
            ));
        };
        let Some((_p_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetCommit parts",
            ));
        };
        let Some((_pid, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetCommit pid",
            ));
        };
        let Some((err, _rest)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetCommit err",
            ));
        };
        Ok(err)
    }

    /// Issue an `OffsetFetch` v1 request for one `(topic, partition)`.
    pub fn offset_fetch(
        &mut self,
        group_id: &str,
        topic: &str,
        partition: i32,
    ) -> io::Result<CommittedOffset> {
        let mut body = Vec::new();
        put_str(&mut body, group_id);
        put_i32(&mut body, 1);
        put_str(&mut body, topic);
        put_i32(&mut body, 1);
        put_i32(&mut body, partition);

        let resp = self.send_raw(OFFSET_FETCH, 1, &body)?;
        let Some((_t_count, cur)) = take_i32(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch",
            ));
        };
        let Some((_t_name, cur)) = take_nonnull_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch topic",
            ));
        };
        let Some((_p_count, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch parts",
            ));
        };
        let Some((_pid, cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch pid",
            ));
        };
        let Some((offset, cur)) = take_i64(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch offset",
            ));
        };
        let Some((meta_opt, cur)) = take_kstr(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch metadata",
            ));
        };
        let Some((error_code, _rest)) = take_i16(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short OffsetFetch err",
            ));
        };
        Ok(CommittedOffset {
            error_code,
            offset,
            metadata: opt_str_owned(meta_opt),
        })
    }

    /// Issue a `SaslHandshake` (`v0..=1`) request and return `(error_code, enabled_mechanisms)`.
    pub fn sasl_handshake(
        &mut self,
        version: i16,
        mechanism: &str,
    ) -> io::Result<(i16, Vec<String>)> {
        let mut body = Vec::new();
        put_str(&mut body, mechanism);
        let resp = self.send_raw(crate::sasl::SASL_HANDSHAKE, version, &body)?;
        let Some((err, cur)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short SaslHandshake error_code",
            ));
        };
        let Some((count_i32, mut cur)) = take_i32(cur) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short SaslHandshake mechanisms count",
            ));
        };
        if count_i32 < 0 || count_i32 > 64 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid SaslHandshake mechanisms count",
            ));
        }
        let count = count_i32 as usize;
        let mut mechs = Vec::with_capacity(count);
        let mut i = 0usize;
        while i < count {
            let Some((Some(m), rest)) = take_kstr(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed SaslHandshake mechanism string",
                ));
            };
            mechs.push(m.to_owned());
            cur = rest;
            i += 1;
        }
        Ok((err, mechs))
    }

    /// Issue one `SaslAuthenticate` (`v0..=2`, including KIP-482 flexible `v2`) request step.
    pub fn sasl_authenticate_raw(
        &mut self,
        version: i16,
        auth_bytes: &[u8],
    ) -> io::Result<crate::sasl::SaslAuthOutcome> {
        let mut body = Vec::new();
        if version >= 2 {
            put_uvarint(&mut body, (auth_bytes.len() as u32).saturating_add(1));
            body.extend_from_slice(auth_bytes);
            put_empty_tags(&mut body);
        } else {
            put_i32(&mut body, auth_bytes.len() as i32);
            body.extend_from_slice(auth_bytes);
        }
        let resp = self.send_raw(crate::sasl::SASL_AUTHENTICATE, version, &body)?;
        let Some((error_code, cur)) = take_i16(&resp) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short SaslAuthenticate error_code",
            ));
        };
        if version >= 2 {
            let Some((err_msg, cur)) = take_compact_nullable_str(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short SaslAuthenticate v2 error_message",
                ));
            };
            let Some((raw_len, cur)) = take_uvarint(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short SaslAuthenticate v2 auth_bytes len",
                ));
            };
            if raw_len == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "null SaslAuthenticate v2 auth_bytes",
                ));
            }
            let blen = (raw_len - 1) as usize;
            let Some(out_bytes) = cur.get(..blen) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "truncated SaslAuthenticate v2 auth_bytes",
                ));
            };
            let Some(after_bytes) = cur.get(blen..) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "truncated SaslAuthenticate v2 tail",
                ));
            };
            let Some((lifetime_ms, after_life)) = take_i64(after_bytes) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short SaslAuthenticate v2 session_lifetime_ms",
                ));
            };
            if skip_tag_buffer(after_life).is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed SaslAuthenticate v2 TAG_BUFFER",
                ));
            }
            Ok(crate::sasl::SaslAuthOutcome {
                error_code,
                error_message: opt_str_owned(err_msg),
                auth_bytes: out_bytes.to_vec(),
                session_lifetime_ms: lifetime_ms,
            })
        } else {
            let Some((err_msg, cur)) = take_kstr(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short SaslAuthenticate error_message",
                ));
            };
            let Some((blen_i32, cur)) = take_i32(cur) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "short SaslAuthenticate auth_bytes len",
                ));
            };
            if blen_i32 < 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "negative SaslAuthenticate auth_bytes len",
                ));
            }
            let blen = blen_i32 as usize;
            let Some(out_bytes) = cur.get(..blen) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "truncated SaslAuthenticate auth_bytes",
                ));
            };
            let Some(after_bytes) = cur.get(blen..) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "truncated SaslAuthenticate tail",
                ));
            };
            let lifetime_ms = if version >= 1 {
                let Some((ms, _)) = take_i64(after_bytes) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "short SaslAuthenticate v1 session_lifetime_ms",
                    ));
                };
                ms
            } else {
                0
            };
            Ok(crate::sasl::SaslAuthOutcome {
                error_code,
                error_message: opt_str_owned(err_msg),
                auth_bytes: out_bytes.to_vec(),
                session_lifetime_ms: lifetime_ms,
            })
        }
    }

    /// Perform full SASL `PLAIN` handshake + authentication (`SaslHandshake` v1 + `SaslAuthenticate` `version`).
    pub fn sasl_authenticate_plain(
        &mut self,
        version: i16,
        username: &str,
        password: &[u8],
    ) -> io::Result<crate::sasl::SaslAuthOutcome> {
        let (hs_err, _) = self.sasl_handshake(1, "PLAIN")?;
        if hs_err != NONE {
            return Ok(crate::sasl::SaslAuthOutcome {
                error_code: hs_err,
                error_message: Some("SaslHandshake failed".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            });
        }
        let token = crate::sasl::build_plain_token("", username, password);
        self.sasl_authenticate_raw(version, &token)
    }

    /// Perform full mutual RFC 5802 / RFC 7677 `SCRAM-SHA-256` authentication over TCP,
    /// including constant-time verification of the broker's `ServerSignature`.
    pub fn sasl_authenticate_scram_sha256(
        &mut self,
        version: i16,
        username: &str,
        password: &[u8],
        client_nonce: &str,
    ) -> io::Result<()> {
        let (hs_err, _) = self.sasl_handshake(1, "SCRAM-SHA-256")?;
        if hs_err != NONE {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "SaslHandshake SCRAM-SHA-256 rejected",
            ));
        }
        let (mut scram, client_first) =
            crate::sasl::ScramSha256Client::start(username, client_nonce);
        let step1 = self.sasl_authenticate_raw(version, &client_first)?;
        if step1.error_code != NONE {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "SCRAM-SHA-256 server-first rejected",
            ));
        }
        let Some(client_final) = scram.step_server_first(password, &step1.auth_bytes) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid SCRAM-SHA-256 server-first challenge",
            ));
        };
        let step2 = self.sasl_authenticate_raw(version, &client_final)?;
        if step2.error_code != NONE {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "SCRAM-SHA-256 client proof rejected",
            ));
        }
        if !scram.verify_server_final(&step2.auth_bytes) {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "SCRAM-SHA-256 server signature mismatch",
            ));
        }
        Ok(())
    }
}
