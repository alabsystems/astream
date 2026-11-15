// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A log sealed at rest by an earlier build opens in this one. `tests/fixtures/v2-at-rest.log`
//! and its `.id`, `.base`, `.hw` and `.state` sidecars were written by astream 7066fab,
//! whose astream-aead sealed through RustCrypto's `chacha20poly1305` 0.10.1, from a
//! scratch crate outside the workspace: `BrokerLog::open_encrypted_verified_init` under
//! key `5a` x 32, six records, `retain_before_carrying_state(3)`, two more. Every seal
//! the at-rest layer makes is in it: record payloads (their log index as AAD), the
//! anti-rollback watermark and the compacted state. `v2-at-rest.expected` is what that
//! build read back; this build must read the same, and refuse the wrong key with the
//! files untouched.
#![cfg(all(feature = "anti-rollback", feature = "retention"))]

use astream_broker::BrokerLog;
use astream_wire::{Filter, Offset};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

const KEY: [u8; 32] = [0x5a; 32];
const SIDECARS: [&str; 4] = ["id", "base", "hw", "state"];

/// A scratch directory holding copies of the fixture's log and sidecars, removed on drop.
struct Copied(PathBuf);

static COPIES: AtomicU64 = AtomicU64::new(0);

impl Copied {
    fn new() -> (Copied, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "astream-at-rest-fixture-{}-{}",
            std::process::id(),
            COPIES.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
        let log = dir.join("v2-at-rest.log");
        std::fs::copy(src.join("v2-at-rest.log"), &log).unwrap();
        for ext in SIDECARS {
            let name = format!("v2-at-rest.log.{ext}");
            std::fs::copy(src.join(&name), dir.join(&name)).unwrap();
        }
        (Copied(dir), log)
    }
}

impl Drop for Copied {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

/// What `log` reads back, in the expected file's own rows.
fn readback(log: &mut BrokerLog) -> Vec<String> {
    let mut rows = vec![
        format!("base\t{}", log.base().0),
        format!("head\t{}", log.head().0),
    ];
    for r in log.read_from(Offset(0)) {
        rows.push(format!(
            "read\t{}\t{}\t{}\t{}\t{}",
            r.seq.0,
            r.producer_id,
            r.producer_seq,
            r.subject,
            hex(&r.body)
        ));
    }
    let all = Filter::new("/a/>").unwrap();
    let (page, more) = {
        let last_head = log.head().0;
        drop(log.publish_last_visible(last_head).unwrap());
        let mut last_view = log.last_view_at(last_head).unwrap();
        log.last_matching(&all, "", 4096, 65536, &mut last_view)
            .unwrap()
            .into_page()
            .expect("the fixed fixture fits one bounded step")
    };
    assert!(more.is_none());
    for r in page {
        rows.push(format!(
            "last\t{}\t{}\t{}\t{}\t{}",
            r.seq.0,
            r.producer_id,
            r.producer_seq,
            r.subject,
            hex(&r.body)
        ));
    }
    rows
}

fn snapshot(log: &Path) -> Vec<Vec<u8>> {
    let mut files = vec![std::fs::read(log).unwrap()];
    for ext in SIDECARS {
        files.push(std::fs::read(log.with_extension(format!("log.{ext}"))).unwrap());
    }
    files
}

#[test]
fn a_log_sealed_by_the_recorded_build_reads_back_the_same() {
    let expected: Vec<String> = include_str!("../fixtures/v2-at-rest.expected")
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(str::to_string)
        .collect();
    // base, head, five records at 3..8, four subjects' last records (one from .state).
    assert_eq!(expected.len(), 11);
    let (_dir, log) = Copied::new();
    let mut opened = BrokerLog::open_encrypted_verified(&log, KEY).unwrap();
    assert_eq!(readback(&mut opened), expected);
}

#[test]
fn the_wrong_key_is_refused_and_leaves_the_recorded_files_untouched() {
    let (_dir, log) = Copied::new();
    let before = snapshot(&log);
    let mut wrong = KEY;
    wrong[31] ^= 0x01;
    assert!(BrokerLog::open_encrypted_verified(&log, wrong).is_err());
    assert!(BrokerLog::open_encrypted(&log, wrong).is_err());
    assert_eq!(snapshot(&log), before);
}

#[test]
fn bound_open_refuses_legacy_v1_unbound_fixture_without_modifying_files() {
    let (_dir, log) = Copied::new();
    let before = snapshot(&log);
    let err = BrokerLog::open_encrypted_bound(&log, KEY)
        .err()
        .expect("open_encrypted_bound must refuse legacy v1 unbound logs");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(
        err.to_string().contains("unbound") || err.to_string().contains(".seal"),
        "refusal should name the missing v2 seal binding: {err}"
    );
    assert_eq!(
        snapshot(&log),
        before,
        "refused open leaves fixture untouched"
    );
}
