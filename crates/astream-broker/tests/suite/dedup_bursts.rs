// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public log coverage for unequal-rate ordinary/ACK chunks and reconstruction.

use astream_broker::{BrokerLog, Durability, ACK_SEQ_BASE};
use astream_wire::Offset;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("astream-burst-dedup-{}-{n}", std::process::id()));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch directory");
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn check_keys(log: &mut BrokerLog, keys: &BTreeMap<u64, Offset>) {
    let head = log.head();
    for (&seq, &original) in keys.iter().rev() {
        let subject = if seq >= ACK_SEQ_BASE {
            "/burst/ack"
        } else {
            "/burst/ordinary"
        };
        assert_eq!(
            log.publish(7, seq, subject.into(), b"retry".to_vec())
                .unwrap(),
            (original, true),
            "retained producer seq {seq}"
        );
    }
    assert_eq!(log.head(), head);
    assert_eq!(log.dedup_len(), keys.len());
}

#[test]
fn unequal_publish_ack_runs_keep_original_offsets_across_reopen_and_retention() {
    let scratch = Scratch::new();
    let path = scratch.0.join("bus.log");
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    let mut keys = BTreeMap::new();
    for batch in 0..256 {
        let mut input = Offset::ZERO;
        for within in 0..32 {
            let seq = batch * 32 + within + 1;
            input = log.head();
            assert_eq!(
                log.publish(7, seq, "/burst/ordinary".into(), b"ordinary".to_vec())
                    .unwrap(),
                (input, false)
            );
            keys.insert(seq, input);
        }
        let ack_seq = ACK_SEQ_BASE | input.0;
        let ack = log.head();
        assert_eq!(
            log.process_and_produce(
                7,
                ack_seq,
                "/burst/ack".into(),
                b"ack".to_vec(),
                "burst32".into(),
                input.0 + 1,
            )
            .unwrap(),
            (ack, false)
        );
        keys.insert(ack_seq, ack);
    }
    assert_eq!(log.head(), Offset(256 * 33));
    check_keys(&mut log, &keys);
    log.close_clean().unwrap();
    drop(log);
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    check_keys(&mut log, &keys);
    #[cfg(feature = "retention")]
    {
        let floor = Offset(4097);
        assert_eq!(log.retain_before(floor).unwrap(), floor.0);
        keys.retain(|_, original| *original >= floor);
        check_keys(&mut log, &keys);
        let replacement = log.head();
        assert_eq!(
            log.publish(7, 1, "/burst/ordinary".into(), b"new".to_vec())
                .unwrap(),
            (replacement, false)
        );
        keys.insert(1, replacement);
        log.close_clean().unwrap();
        drop(log);
        let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
        assert_eq!(log.base(), floor);
        check_keys(&mut log, &keys);
    }
}
