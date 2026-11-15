// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Prepared opens hold the actual log file through sidecar preparation and
//! recovery. These controls use owned files only, without a listener or child.

use astream_broker::{Broker, BrokerLog, Durability};
use std::cell::Cell;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// Exclusive creation, never removal of a preexisting path. Bind before every
/// log owner so its files are removed only after their handles have dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("asprep-{}-{n}", std::process::id()));
        let mut builder = std::fs::DirBuilder::new();
        builder.recursive(false);
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            builder.mode(0o700);
        }
        builder.create(&path).expect("exclusive scratch directory");
        Self(path)
    }

    fn log(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn sidecar(path: &Path) -> PathBuf {
    astream_broker::identity_path(path)
}

#[test]
fn preparation_owns_the_log_before_identity_and_until_broker_drop() {
    let scratch = Scratch::new();
    let path = scratch.log("bus.log");
    let calls = Cell::new(0);
    let broker = Broker::open_with_prepare(&path, Durability::Relaxed, || {
        calls.set(calls.get() + 1);
        assert!(!sidecar(&path).exists(), "identity must be settled later");
        let err = BrokerLog::open(&path)
            .err()
            .expect("the actual log is locked");
        assert_eq!(err.kind(), io::ErrorKind::AlreadyExists);
        Ok(())
    })
    .unwrap();
    assert_eq!(calls.get(), 1);
    assert!(sidecar(&path).is_file());
    let owned_sidecar = std::fs::read(sidecar(&path)).unwrap();
    let contender_called = Cell::new(false);
    let err = Broker::open_with_prepare(&path, Durability::Strict, || {
        contender_called.set(true);
        Ok(())
    })
    .err()
    .expect("a contender cannot prepare a live broker's sidecars");
    assert_eq!(err.kind(), io::ErrorKind::AlreadyExists);
    assert!(!contender_called.get());
    assert_eq!(std::fs::read(sidecar(&path)).unwrap(), owned_sidecar);
    drop(broker);
    let reopened = Broker::open_with_prepare(&path, Durability::Strict, || {
        calls.set(calls.get() + 1);
        Ok(())
    })
    .unwrap();
    assert_eq!(calls.get(), 2);
    drop(reopened);
}

#[derive(Debug)]
struct PreparationRefused;

impl std::fmt::Display for PreparationRefused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("fixture preparation refused")
    }
}

impl std::error::Error for PreparationRefused {}

#[test]
fn a_preparation_error_precedes_recovery_and_releases_the_file() {
    let scratch = Scratch::new();
    let path = scratch.log("bus.log");
    {
        let mut seed = BrokerLog::open(&path).unwrap();
        seed.publish(7, 1, "/fixture/record".to_string(), b"retained".to_vec())
            .unwrap();
    }
    let intact_len = std::fs::metadata(&path).unwrap().len();
    // A one-byte torn frame will be removed by a successful recovery, so it
    // witnesses whether recovery ran before the preparation refusal.
    std::fs::OpenOptions::new()
        .append(true)
        .open(&path)
        .unwrap()
        .write_all(&[0xA5])
        .unwrap();
    let bytes = std::fs::read(&path).unwrap();
    let identity = std::fs::read(sidecar(&path)).unwrap();
    let err = Broker::open_with_prepare(&path, Durability::Relaxed, || {
        let held = BrokerLog::open(&path)
            .err()
            .expect("preparation owns the log");
        assert_eq!(held.kind(), io::ErrorKind::AlreadyExists);
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            PreparationRefused,
        ))
    })
    .err()
    .expect("the preparation refusal is propagated");
    assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    assert!(err
        .get_ref()
        .and_then(|e| e.downcast_ref::<PreparationRefused>())
        .is_some());
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
    assert_eq!(std::fs::read(sidecar(&path)).unwrap(), identity);
    let recovered = BrokerLog::open(&path).unwrap();
    assert_eq!(recovered.head().0, 1);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), intact_len);
}

#[test]
fn a_preparation_unwind_releases_the_file() {
    let scratch = Scratch::new();
    let path = scratch.log("bus.log");
    let outcome = std::panic::catch_unwind(|| {
        Broker::open_with_prepare(&path, Durability::Relaxed, || {
            panic!("fixture preparation unwind");
        })
    });
    assert!(outcome.is_err());
    let reopened = BrokerLog::open(&path).unwrap();
    assert_eq!(reopened.head().0, 0);
}

#[cfg(feature = "cap")]
#[test]
fn guarded_preparation_keeps_the_lock_and_refuses_an_empty_secret_first() {
    let scratch = Scratch::new();
    for (n, tier) in [Durability::Strict, Durability::Relaxed]
        .into_iter()
        .enumerate()
    {
        let path = scratch.log(&format!("valid-{n}.log"));
        let called = Cell::new(false);
        let broker =
            Broker::open_guarded_with_prepare(&path, b"fixture-secret".to_vec(), tier, || {
                called.set(true);
                let err = BrokerLog::open(&path)
                    .err()
                    .expect("the guarded open owns the log");
                assert_eq!(err.kind(), io::ErrorKind::AlreadyExists);
                Ok(())
            })
            .unwrap();
        assert!(called.get());
        drop(broker);

        let refused = scratch.log(&format!("empty-{n}.log"));
        let called = Cell::new(false);
        let err = Broker::open_guarded_with_prepare(&refused, Vec::new(), tier, || {
            called.set(true);
            Ok(())
        })
        .err()
        .expect("an empty secret is refused before preparation");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
        assert!(!called.get());
        assert!(!refused.exists());
        assert!(!sidecar(&refused).exists());
    }
}
