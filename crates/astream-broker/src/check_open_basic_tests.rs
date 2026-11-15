// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Public open-check behavior in every feature configuration, including no retention.

use super::{BrokerLog, OpenCheck};
use crate::test_scratch::Scratch;
use astream_wire::Offset;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

fn seed() -> (Scratch, PathBuf) {
    let scratch = Scratch::new("check-open-basic");
    let path = scratch.path().join("bus.log");
    let mut log = BrokerLog::open(&path).unwrap();
    log.publish(7, 1, "/f/F/pub/n1/s1/ev".into(), b"kept".to_vec())
        .unwrap();
    drop(log);
    (scratch, path)
}

fn snapshot(root: &Path) -> BTreeMap<OsString, Vec<u8>> {
    std::fs::read_dir(root)
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            (entry.file_name(), std::fs::read(entry.path()).unwrap())
        })
        .collect()
}

#[test]
fn a_plain_log_check_preserves_files_and_releases_its_lock_in_every_feature_configuration() {
    let (scratch, path) = seed();
    let before = snapshot(scratch.path());
    assert!(before.contains_key(&OsString::from("bus.log.id")));
    assert_eq!(
        BrokerLog::check_open(&path, None).unwrap(),
        OpenCheck::Opens {
            base: Offset::ZERO,
            head: Offset(1),
            torn: 0,
        }
    );
    assert_eq!(snapshot(scratch.path()), before);

    // An ordinary open still succeeds after the check has released its lock.
    let log = BrokerLog::open(&path).unwrap();
    let held = snapshot(scratch.path());
    assert_eq!(
        BrokerLog::check_open(&path, None).unwrap_err().kind(),
        std::io::ErrorKind::AlreadyExists
    );
    assert_eq!(snapshot(scratch.path()), held);
    drop(log);
}

#[cfg(not(feature = "at-rest"))]
#[test]
fn a_key_without_at_rest_is_refused_without_writes_or_a_leaked_lock() {
    let (scratch, path) = seed();
    let before = snapshot(scratch.path());
    assert_eq!(
        BrokerLog::check_open(&path, Some([0x5a; 32]))
            .unwrap_err()
            .kind(),
        std::io::ErrorKind::Unsupported
    );
    assert_eq!(snapshot(scratch.path()), before);
    assert_eq!(
        BrokerLog::check_open(&path, None).unwrap(),
        OpenCheck::Opens {
            base: Offset::ZERO,
            head: Offset(1),
            torn: 0,
        }
    );
    assert_eq!(snapshot(scratch.path()), before);
    drop(BrokerLog::open(&path).unwrap());
}
