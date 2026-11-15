// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public-log regressions for short producer histories, promotion through a gap,
//! replicated key replacements, and reconstruction from retained log bytes.

use astream_broker::{BrokerLog, BrokerRecord, Durability};
use astream_wire::Offset;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
const SUBJECT: &str = "/dedup/short";
type Keys = BTreeMap<(u64, u64), Offset>;

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("astream-short-dedup-{}-{n}", std::process::id()));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch directory");
    }

    fn log(&self) -> PathBuf {
        self.0.join("bus.log")
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn append(log: &mut BrokerLog, keys: &mut Keys, pid: u64, seq: u64) {
    let head = log.head();
    assert_eq!(
        log.publish(pid, seq, SUBJECT.into(), vec![pid as u8, seq as u8])
            .unwrap(),
        (head, false)
    );
    assert!(keys.insert((pid, seq), head).is_none());
}

fn retries_append_nothing(log: &mut BrokerLog, keys: &Keys) {
    let head = log.head();
    // Payload changes cannot change the offset named by a retained ingest key.
    for (&(pid, seq), &offset) in keys.iter().rev() {
        assert_eq!(
            log.publish(
                pid,
                seq,
                SUBJECT.into(),
                b"retry with different bytes".to_vec()
            )
            .unwrap(),
            (offset, true),
            "retry ({pid}, {seq})"
        );
    }
    assert_eq!(log.head(), head);
    assert_eq!(log.dedup_len(), keys.len());
}

fn short_histories_then_bridged_growth(log: &mut BrokerLog) -> Keys {
    let mut keys = Keys::new();
    for pid in 0..64 {
        for seq in [4, 1, 3, 2] {
            append(log, &mut keys, pid, seq);
        }
    }
    // Grow one producer through two disjoint runs. Filling the gap must retain
    // every key on both sides when the representation changes to packed chunks.
    for seq in (6..=9).chain([5]).chain(10..=40) {
        append(log, &mut keys, 0, seq);
    }
    keys
}

#[test]
fn short_producer_retries_survive_bridge_growth_and_reopen() {
    let scratch = Scratch::new();
    let mut log = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    let keys = short_histories_then_bridged_growth(&mut log);
    retries_append_nothing(&mut log, &keys);
    log.close_clean().unwrap();
    drop(log);

    let mut reopened = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    retries_append_nothing(&mut reopened, &keys);
    for record in reopened.read_range(Offset::ZERO, keys.len()) {
        assert_eq!(keys[&(record.producer_id, record.producer_seq)], record.seq);
        assert_eq!(
            record.body,
            vec![record.producer_id as u8, record.producer_seq as u8]
        );
    }
}

#[cfg(feature = "retention")]
#[test]
fn retention_prunes_short_and_packed_keys_before_rebuilding_on_reopen() {
    let scratch = Scratch::new();
    let mut log = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    let mut keys = short_histories_then_bridged_growth(&mut log);
    // Cuts through a short producer and drops the beginning of the long producer.
    let floor = Offset(130);
    assert_eq!(log.retain_before(floor).unwrap(), floor.0);
    keys.retain(|_, off| *off >= floor);
    retries_append_nothing(&mut log, &keys);
    // Pruned keys may be produced again; their newer records must survive rebuild.
    append(&mut log, &mut keys, 32, 1);
    append(&mut log, &mut keys, 0, 1);
    log.close_clean().unwrap();
    drop(log);

    let mut reopened = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    assert_eq!(reopened.stats().base, floor);
    retries_append_nothing(&mut reopened, &keys);
    assert_eq!(reopened.read_range(floor, keys.len()).len(), keys.len());
}

#[test]
fn replica_replacements_for_short_and_growing_producers_survive_reopen() {
    let scratch = Scratch::new();
    let mut log = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    let mut keys = Keys::new();
    let records = [(7, 1), (7, 2), (7, 1)]
        .into_iter()
        .chain((1..=40).map(|seq| (8, seq)))
        .chain([(8, 1), (7, 2)]);
    for (pid, seq) in records {
        let head = log.head();
        let record = BrokerRecord {
            seq: head,
            producer_id: pid,
            producer_seq: seq,
            subject: SUBJECT.into(),
            body: head.0.to_le_bytes().to_vec(),
            commit: None,
        };
        assert_eq!(
            log.replicate_fenced(1, head.0, record.clone()).unwrap(),
            (head, false)
        );
        assert_eq!(
            log.replicate_fenced(1, head.0, record).unwrap(),
            (head, true),
            "re-shipping a frame is also idempotent"
        );
        keys.insert((pid, seq), head);
    }
    assert_eq!(keys[&(7, 1)], Offset(2));
    assert_eq!(keys[&(8, 1)], Offset(43));
    assert_eq!(keys[&(7, 2)], Offset(44));
    retries_append_nothing(&mut log, &keys);
    #[cfg(feature = "retention")]
    {
        assert_eq!(log.retain_before(Offset(3)).unwrap(), 3);
        keys.retain(|_, off| off.0 >= 3);
        retries_append_nothing(&mut log, &keys);
    }
    log.close_clean().unwrap();
    drop(log);

    let mut reopened = BrokerLog::open_with(scratch.log(), Durability::Relaxed).unwrap();
    retries_append_nothing(&mut reopened, &keys);
}
