// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Durable multi-partition Kafka backend over [`astream_broker::ShardedBroker`].
//!
//! Maps Kafka topic partitions 1-to-1 onto `ShardedBroker` shards (`shard = partition_id % shards`)
//! under `/kafka/data/t_<topic_hex>/<partition_id>`, consumer-group coordinator snapshots onto
//! `/kafka/group/g_<group_hex>`, and committed offsets onto
//! `/kafka/offset/g_<group_hex>/t_<topic_hex>/<partition_id>` (auto-compacted via `BrokerLog`'s
//! last-value index on reopen).

use crate::record_batch::{decode_i64_be, encode_i64_be};
use crate::server::{
    put_bytes, put_nullable_str, take_bytes, take_i64, take_kstr, take_nonnull_kstr, AppendPlan,
    CommittedOffset, GroupMember, GroupState, JoinGroupResult, KafkaStore,
    COORDINATOR_NOT_AVAILABLE, INVALID_GROUP_ID, INVALID_REQUEST,
};
use crate::{put_i32, put_str, take_i32, TopicMeta, NONE};
use astream_broker::{Client, Durability, OpenOptions, ShardedBroker, ShardedHandle};
use astream_wire::{assign_partition, PartitionKey};
use std::io;
use std::net::TcpStream;
use std::path::Path;

const DURABLE_PRODUCER_ID: u64 = 0x4b41_464b_415f_4455;
const MAX_IDENT_BYTES: usize = 46;
const GROUP_SNAP_V1: u8 = 0x01;
const OFFSET_SNAP_V1: u8 = 0x01;
const FETCH_PAGE_RECORDS: u32 = 512;

const fn nibble_hex(n: u8) -> u8 {
    let low = n & 0x0f;
    if low < 10 {
        b'0' + low
    } else {
        b'a' + (low - 10)
    }
}

const fn from_hex_digit(b: u8) -> Option<u8> {
    if b >= b'0' && b <= b'9' {
        Some(b - b'0')
    } else if b >= b'a' && b <= b'f' {
        Some(10 + (b - b'a'))
    } else if b >= b'A' && b <= b'F' {
        Some(10 + (b - b'A'))
    } else {
        None
    }
}

fn hex_encode_prefixed(prefix: &str, raw: &str) -> Option<String> {
    if raw.is_empty() || raw.len() > MAX_IDENT_BYTES || prefix.len() > MAX_IDENT_BYTES {
        return None;
    }
    let mut out = String::new();
    out.push_str(prefix);
    for &b in raw.as_bytes() {
        out.push(nibble_hex(b >> 4) as char);
        out.push(nibble_hex(b & 0x0f) as char);
    }
    Some(out)
}

fn hex_decode_prefixed(prefix: &str, encoded: &str) -> Option<String> {
    let hex = encoded.strip_prefix(prefix)?;
    if hex.is_empty() || hex.len() % 2 != 0 || hex.len() > MAX_IDENT_BYTES * 2 {
        return None;
    }
    let bytes = hex.as_bytes();
    let mut decoded = Vec::new();
    let mut idx = 0usize;
    while idx < bytes.len() {
        let hi = from_hex_digit(*bytes.get(idx)?)?;
        let lo = from_hex_digit(*bytes.get(idx.saturating_add(1))?)?;
        decoded.push((hi << 4) | lo);
        idx = idx.saturating_add(2);
    }
    String::from_utf8(decoded).ok()
}

fn data_subject(topic: &str, partition_id: i32) -> Option<String> {
    if partition_id < 0 {
        return None;
    }
    let t_seg = hex_encode_prefixed("t_", topic)?;
    Some(format!("/kafka/data/{t_seg}/{partition_id}"))
}

fn group_subject(group_id: &str) -> Option<String> {
    let g_seg = hex_encode_prefixed("g_", group_id)?;
    Some(format!("/kafka/group/{g_seg}"))
}

fn offset_subject(group_id: &str, topic: &str, partition_id: i32) -> Option<String> {
    if partition_id < 0 {
        return None;
    }
    let g_seg = hex_encode_prefixed("g_", group_id)?;
    let t_seg = hex_encode_prefixed("t_", topic)?;
    Some(format!("/kafka/offset/{g_seg}/{t_seg}/{partition_id}"))
}

fn parse_group_subject(subj: &str) -> Option<String> {
    let g_seg = subj.strip_prefix("/kafka/group/")?;
    if g_seg.contains('/') {
        return None;
    }
    hex_decode_prefixed("g_", g_seg)
}

fn parse_offset_subject(subj: &str) -> Option<(String, String, i32)> {
    let rest = subj.strip_prefix("/kafka/offset/")?;
    let (g_seg, rest2) = rest.split_once('/')?;
    let (t_seg, p_seg) = rest2.split_once('/')?;
    if p_seg.contains('/') {
        return None;
    }
    let group_id = hex_decode_prefixed("g_", g_seg)?;
    let topic = hex_decode_prefixed("t_", t_seg)?;
    let Ok(pid) = p_seg.parse::<i32>() else {
        return None;
    };
    if pid < 0 {
        return None;
    }
    Some((group_id, topic, pid))
}

fn encode_group_snapshot(g: &GroupState) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(GROUP_SNAP_V1);
    put_i32(&mut out, g.generation_id);
    out.extend_from_slice(&encode_i64_be(g.next_member_seq as i64));
    put_str(&mut out, &g.protocol_type);
    put_str(&mut out, &g.protocol_name);
    put_str(&mut out, &g.leader_id);
    put_i32(&mut out, g.members.len() as i32);
    for m in &g.members {
        put_str(&mut out, &m.member_id);
        put_i32(&mut out, m.session_timeout_ms);
        put_i32(&mut out, m.protocols.len() as i32);
        for (p_name, p_meta) in &m.protocols {
            put_str(&mut out, p_name);
            put_bytes(&mut out, p_meta);
        }
        put_bytes(&mut out, &m.assignment);
    }
    out
}

fn decode_group_snapshot(raw: &[u8]) -> Option<GroupState> {
    let &[ver, ref cur @ ..] = raw else {
        return None;
    };
    if ver != GROUP_SNAP_V1 {
        return None;
    }
    let (generation_id, cur) = take_i32(cur)?;
    let (next_seq_i64, cur) = take_i64(cur)?;
    let (protocol_type, cur) = take_nonnull_kstr(cur)?;
    let (protocol_name, cur) = take_nonnull_kstr(cur)?;
    let (leader_id, cur) = take_nonnull_kstr(cur)?;
    let (m_count, mut cur) = take_i32(cur)?;
    if m_count < 0 {
        return None;
    }
    let mut members = Vec::new();
    let mut m_idx = 0i32;
    while m_idx < m_count {
        let (m_id, mc1) = take_nonnull_kstr(cur)?;
        let (timeout_ms, mc2) = take_i32(mc1)?;
        let (p_count, mut p_cur) = take_i32(mc2)?;
        if p_count < 0 {
            return None;
        }
        let mut protocols = Vec::new();
        let mut p_idx = 0i32;
        while p_idx < p_count {
            let (p_name, pc1) = take_nonnull_kstr(p_cur)?;
            let (p_meta, pc2) = take_bytes(pc1)?;
            protocols.push((p_name.to_owned(), p_meta.to_vec()));
            p_cur = pc2;
            p_idx = p_idx.saturating_add(1);
        }
        let (assign, next_m) = take_bytes(p_cur)?;
        members.push(GroupMember {
            member_id: m_id.to_owned(),
            session_timeout_ms: timeout_ms,
            protocols,
            assignment: assign.to_vec(),
        });
        cur = next_m;
        m_idx = m_idx.saturating_add(1);
    }
    Some(GroupState {
        generation_id,
        next_member_seq: next_seq_i64 as u64,
        protocol_type: protocol_type.to_owned(),
        protocol_name: protocol_name.to_owned(),
        leader_id: leader_id.to_owned(),
        members,
    })
}

fn encode_offset_snapshot(offset: i64, metadata: Option<&str>) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(OFFSET_SNAP_V1);
    out.extend_from_slice(&encode_i64_be(offset));
    put_nullable_str(&mut out, metadata);
    out
}

fn decode_offset_snapshot(raw: &[u8]) -> Option<(i64, Option<String>)> {
    let &[ver, ref cur @ ..] = raw else {
        return None;
    };
    if ver != OFFSET_SNAP_V1 {
        return None;
    }
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref after_off @ ..] = cur else {
        return None;
    };
    let offset = decode_i64_be(&[b0, b1, b2, b3, b4, b5, b6, b7]);
    let (meta_opt, _rest) = take_kstr(after_off)?;
    let owned_meta = crate::server::opt_str_owned(meta_opt);
    Some((offset, owned_meta))
}

/// Durable multi-partition Kafka store and coordinator backed by
/// [`astream_broker::ShardedBroker`].
pub struct DurableKafkaStore {
    mem: KafkaStore,
    conns: Vec<Client<TcpStream>>,
    next_seqs: Vec<u64>,
    shards: u32,
    handle: Option<ShardedHandle>,
    _broker: ShardedBroker,
}

impl DurableKafkaStore {
    /// Open (or recover) a Strict-durability [`DurableKafkaStore`] over `shards` independent
    /// broker logs under `dir`.
    pub fn open(dir: impl AsRef<Path>, shards: u32, topics: &[(String, i32)]) -> io::Result<Self> {
        Self::open_with(dir, shards, Durability::Strict, topics)
    }

    /// Open (or recover) a [`DurableKafkaStore`] at the chosen [`Durability`] tier.
    pub fn open_with(
        dir: impl AsRef<Path>,
        shards: u32,
        durability: Durability,
        topics: &[(String, i32)],
    ) -> io::Result<Self> {
        let shards = shards.max(1);
        for (name, _) in topics {
            if hex_encode_prefixed("t_", name).is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("topic name {name:?} must be 1..={MAX_IDENT_BYTES} bytes"),
                ));
            }
        }
        let sharded = ShardedBroker::open_opts(
            dir,
            shards,
            OpenOptions::new(durability).with_resident_budget(0),
        )?;
        let mut handle = sharded.serve_tcp_loopback()?;
        let mut conns = Vec::new();
        let mut next_seqs = Vec::new();
        let mut idx = 0usize;
        while idx < (shards as usize) {
            let Some(addr) = handle.tcp_addr(idx) else {
                handle.shutdown();
                return Err(io::Error::other("missing loopback TCP address on shard"));
            };
            let mut cli = match Client::connect_tcp(addr) {
                Ok(c) => c,
                Err(e) => {
                    conns.clear();
                    handle.shutdown();
                    return Err(e);
                }
            };
            let head = match cli.fetch(0, "/kafka/>", 0) {
                Ok((_empty, (_next, h))) => h,
                Err(e) => {
                    conns.clear();
                    handle.shutdown();
                    return Err(e);
                }
            };
            next_seqs.push(head.saturating_add(1));
            conns.push(cli);
            idx = idx.saturating_add(1);
        }

        let mut store = Self {
            mem: KafkaStore::with_partitions(topics),
            conns,
            next_seqs,
            shards,
            handle: Some(handle),
            _broker: sharded,
        };
        store.recover_from_shards()?;
        Ok(store)
    }

    /// Return the current high watermark for `(topic, partition_id)`.
    #[must_use]
    pub fn high_watermark_partition(&self, topic: &str, partition_id: i32) -> Option<u64> {
        self.mem.high_watermark_partition(topic, partition_id)
    }

    /// Number of underlying `ShardedBroker` shards.
    #[must_use]
    pub const fn shards(&self) -> u32 {
        self.shards
    }

    /// Aggregate `(resident_records, resident_bytes, retained_records)` across the
    /// underlying [`ShardedBroker`] shards.
    #[must_use]
    pub fn broker_residency(&self) -> (usize, usize, usize) {
        self._broker.residency()
    }

    /// Shut down per-shard TCP listeners, join shard writer threads, and release log locks.
    pub fn shutdown(&mut self) {
        self.conns.clear();
        if let Some(mut h) = self.handle.take() {
            h.shutdown();
        }
    }

    const fn partition_shard(&self, partition_id: i32) -> usize {
        let n = if self.shards == 0 { 1 } else { self.shards };
        ((partition_id as u32) % n) as usize
    }

    const fn group_shard(&self, group_id: &str) -> usize {
        assign_partition(PartitionKey::Keyed(group_id.as_bytes()), self.shards) as usize
    }

    fn publish_to_shard(&mut self, shard: usize, subject: &str, body: &[u8]) -> io::Result<u64> {
        let Some(&seq) = self.next_seqs.get(shard) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "shard index out of bounds",
            ));
        };
        let Some(conn) = self.conns.get_mut(shard) else {
            return Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "shard connection closed",
            ));
        };
        let (off, deduped) = conn.publish(DURABLE_PRODUCER_ID, seq, subject, body)?;
        let next = off.saturating_add(2).max(seq.saturating_add(1));
        if let Some(slot) = self.next_seqs.get_mut(shard) {
            *slot = next;
        }
        if deduped {
            return Err(io::Error::other(
                "unexpected dedup hit on fresh DurableKafkaStore sequence",
            ));
        }
        Ok(off)
    }

    fn recover_from_shards(&mut self) -> io::Result<()> {
        let topics = self.mem.topics_meta();
        for tm in &topics {
            let mut pid = 0i32;
            while pid < tm.partitions {
                let Some(subj) = data_subject(&tm.name, pid) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "unencodable topic subject during recovery",
                    ));
                };
                let shard = self.partition_shard(pid);
                let mut cursor = 0u64;
                loop {
                    let Some(conn) = self.conns.get_mut(shard) else {
                        return Err(io::Error::other("missing shard connection during recovery"));
                    };
                    let (rows, (next, head)) = conn.fetch(cursor, &subj, FETCH_PAGE_RECORDS)?;
                    for (_off, _s, body) in rows {
                        if !self.mem.replay_stored_batch(&tm.name, pid, &body) {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "corrupt Kafka RecordBatch v2 on durable shard",
                            ));
                        }
                    }
                    if next >= head || next <= cursor {
                        break;
                    }
                    cursor = next;
                }
                pid = pid.saturating_add(1);
            }
        }

        let mut shard = 0usize;
        while shard < self.conns.len() {
            let group_rows = {
                let Some(conn) = self.conns.get_mut(shard) else {
                    break;
                };
                let (rows, _mark) = conn.last_all("/kafka/group/*")?;
                rows
            };
            for (_off, subj, body) in group_rows {
                let Some(group_id) = parse_group_subject(&subj) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "malformed /kafka/group subject on durable shard",
                    ));
                };
                let Some(state) = decode_group_snapshot(&body) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "corrupt /kafka/group snapshot on durable shard",
                    ));
                };
                self.mem.install_group_state(group_id, state);
            }

            let offset_rows = {
                let Some(conn) = self.conns.get_mut(shard) else {
                    break;
                };
                let (rows, _mark) = conn.last_all("/kafka/offset/*/*/*")?;
                rows
            };
            for (_off, subj, body) in offset_rows {
                let Some((group_id, topic, pid)) = parse_offset_subject(&subj) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "malformed /kafka/offset subject on durable shard",
                    ));
                };
                let Some((committed_off, meta)) = decode_offset_snapshot(&body) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "corrupt /kafka/offset snapshot on durable shard",
                    ));
                };
                self.mem
                    .install_committed_offset(&group_id, &topic, pid, committed_off, meta);
            }
            shard = shard.saturating_add(1);
        }
        Ok(())
    }
}

impl Drop for DurableKafkaStore {
    fn drop(&mut self) {
        self.shutdown();
    }
}

impl DurableKafkaStore {
    /// Return advertised topics and their partition counts.
    #[must_use]
    pub fn topics_meta(&self) -> Vec<TopicMeta> {
        self.mem.topics_meta()
    }

    /// Append one encoded RecordBatch v2 payload to `(topic, partition_id)`, persisting to the
    /// mapped `ShardedBroker` shard before updating in-memory state.
    pub fn append_batch(&mut self, topic: &str, partition_id: i32, raw_batch: &[u8]) -> (i16, i64) {
        let plan = match self.mem.plan_append_batch(topic, partition_id, raw_batch) {
            Ok(p) => p,
            Err(err) => return err,
        };
        match plan {
            AppendPlan::Duplicate { base_offset } => (NONE, base_offset),
            AppendPlan::Write {
                base_offset_i64,
                ref batch,
                ..
            } => {
                let Some(subj) = data_subject(topic, partition_id) else {
                    return (INVALID_REQUEST, -1);
                };
                let shard = self.partition_shard(partition_id);
                if self.publish_to_shard(shard, &subj, &batch.bytes).is_err() {
                    return (COORDINATOR_NOT_AVAILABLE, -1);
                }
                self.mem.commit_append_plan(topic, partition_id, plan);
                (NONE, base_offset_i64)
            }
        }
    }

    /// Fetch RecordBatch v2 bytes starting at `fetch_offset` up to `max_bytes`.
    #[must_use]
    pub fn fetch_batches(
        &self,
        topic: &str,
        partition_id: i32,
        fetch_offset: i64,
        max_bytes: i32,
    ) -> (i16, i64, Vec<u8>) {
        self.mem
            .fetch_batches(topic, partition_id, fetch_offset, max_bytes)
    }

    /// Resolve a `ListOffsets` v1 timestamp query on `(topic, partition_id)`.
    #[must_use]
    pub fn list_offset(&self, topic: &str, partition_id: i32, target_ts: i64) -> (i16, i64, i64) {
        self.mem.list_offset(topic, partition_id, target_ts)
    }

    /// Coordinate a `JoinGroup` v0 request and persist the updated group snapshot to its shard.
    pub fn join_group(
        &mut self,
        group_id: &str,
        session_timeout_ms: i32,
        member_id: &str,
        protocol_type: &str,
        protocols: &[(String, Vec<u8>)],
    ) -> JoinGroupResult {
        let Some(subj) = group_subject(group_id) else {
            return JoinGroupResult {
                error_code: INVALID_GROUP_ID,
                generation_id: -1,
                group_protocol: String::new(),
                leader_id: String::new(),
                member_id: member_id.to_owned(),
                members: Vec::new(),
            };
        };
        let (res, updated) = KafkaStore::compute_join_group(
            self.mem.group_ref(group_id),
            group_id,
            session_timeout_ms,
            member_id,
            protocol_type,
            protocols,
        );
        if let Some(new_state) = updated {
            let snap = encode_group_snapshot(&new_state);
            let shard = self.group_shard(group_id);
            if self.publish_to_shard(shard, &subj, &snap).is_err() {
                return JoinGroupResult {
                    error_code: COORDINATOR_NOT_AVAILABLE,
                    generation_id: -1,
                    group_protocol: String::new(),
                    leader_id: String::new(),
                    member_id: member_id.to_owned(),
                    members: Vec::new(),
                };
            }
            self.mem.install_group_state(group_id.to_owned(), new_state);
        }
        res
    }

    /// Coordinate a `SyncGroup` v0 request and persist any leader assignment snapshot.
    pub fn sync_group(
        &mut self,
        group_id: &str,
        generation_id: i32,
        member_id: &str,
        assignments: &[(String, Vec<u8>)],
    ) -> (i16, Vec<u8>) {
        let (reply, updated) = KafkaStore::compute_sync_group(
            self.mem.group_ref(group_id),
            group_id,
            generation_id,
            member_id,
            assignments,
        );
        if let Some(new_state) = updated {
            let Some(subj) = group_subject(group_id) else {
                return (INVALID_GROUP_ID, Vec::new());
            };
            let snap = encode_group_snapshot(&new_state);
            let shard = self.group_shard(group_id);
            if self.publish_to_shard(shard, &subj, &snap).is_err() {
                return (COORDINATOR_NOT_AVAILABLE, Vec::new());
            }
            self.mem.install_group_state(group_id.to_owned(), new_state);
        }
        reply
    }

    /// Validate a `Heartbeat` v0 request against active membership and generation.
    #[must_use]
    pub fn heartbeat(&self, group_id: &str, generation_id: i32, member_id: &str) -> i16 {
        self.mem.heartbeat(group_id, generation_id, member_id)
    }

    /// Remove `member_id` from `group_id` (`LeaveGroup` v0) and persist the rebalanced group snapshot.
    pub fn leave_group(&mut self, group_id: &str, member_id: &str) -> i16 {
        let (code, updated) =
            KafkaStore::compute_leave_group(self.mem.group_ref(group_id), group_id, member_id);
        if let Some(new_state) = updated {
            let Some(subj) = group_subject(group_id) else {
                return INVALID_GROUP_ID;
            };
            let snap = encode_group_snapshot(&new_state);
            let shard = self.group_shard(group_id);
            if self.publish_to_shard(shard, &subj, &snap).is_err() {
                return COORDINATOR_NOT_AVAILABLE;
            }
            self.mem.install_group_state(group_id.to_owned(), new_state);
        }
        code
    }

    /// Commit one `(group_id, topic, partition_id)` offset (`OffsetCommit` v2) and persist to shard.
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
        let code = self.mem.validate_commit_offset(
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
        let Some(subj) = offset_subject(group_id, topic, partition_id) else {
            return INVALID_REQUEST;
        };
        let snap = encode_offset_snapshot(offset, metadata);
        let shard = self.group_shard(group_id);
        if self.publish_to_shard(shard, &subj, &snap).is_err() {
            return COORDINATOR_NOT_AVAILABLE;
        }
        let owned_meta = crate::server::opt_str_owned(metadata);
        self.mem
            .install_committed_offset(group_id, topic, partition_id, offset, owned_meta);
        NONE
    }

    /// Fetch one `(group_id, topic, partition_id)` committed offset (`OffsetFetch` v1).
    #[must_use]
    pub fn fetch_offset(&self, group_id: &str, topic: &str, partition_id: i32) -> CommittedOffset {
        self.mem.fetch_offset(group_id, topic, partition_id)
    }
}
