// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The BREC rule's fixtures (`brecord.rs`, `BREC_VERSION`): stored bytes written by a
//! real build, committed under `tests/fixtures/` and never regenerated once a release
//! has written its format, read by THIS build — in both directions across the batch
//! marks.
//!
//! - `v2-unsealed.log` + `.id`: five records and a FORMAT 1 identity sidecar written by
//!   astream 9f95697, the release before the marks and FORMAT 2. This build opens it
//!   under the rules that predate the floor and reads every record back, its identity
//!   kept — and, appended above a floor this build recorded (a revert, then the upgrade
//!   again) or restored alone under one, keeps every record of it too.
//! - `v2-sealed.log` + `.id`: the same five records, then 24 published through one
//!   pipelined connection (so some batches hold several records), and a FORMAT 2
//!   sidecar, written by the first marking build. Every frame decodes through a FROZEN
//!   copy of the v2 parser as it stood at 2888062 — the downgrade property: an older
//!   build reads a marked log unchanged — and this build reads the same records and
//!   their marks.

use astream_broker::{BrokerLog, BrokerRecord, Durability, LogIdentity};
use astream_wire::{Frame, Offset};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// A scratch directory holding copies of a fixture's log and sidecar, removed on drop.
/// Each copy has a directory of its own: tests copying the same fixture run in parallel.
struct Copied(PathBuf);

static COPIES: AtomicU64 = AtomicU64::new(0);

impl Copied {
    fn new(fixture: &str) -> (Copied, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "astream-brec-fixture-{}-{}-{fixture}",
            std::process::id(),
            COPIES.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
        let log = dir.join(fixture);
        std::fs::copy(src.join(fixture), &log).unwrap();
        std::fs::copy(
            src.join(format!("{fixture}.id")),
            dir.join(format!("{fixture}.id")),
        )
        .unwrap();
        (Copied(dir), log)
    }
}

impl Drop for Copied {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// One expected record: `(producer_id, producer_seq, subject, body, commit)`.
type Expected = (
    u64,
    u64,
    &'static str,
    &'static [u8],
    Option<(&'static str, u64)>,
);

/// A record's fields as the frozen parser returns them: `(seq, producer_id,
/// producer_seq, subject, body, commit)`.
type Fields = (u64, u64, u64, String, Vec<u8>, Option<(String, u64)>);

/// What the fixture writer put in the first five records.
fn first_five() -> Vec<Expected> {
    vec![
        (7, 1, "/f/a/one", b"first body", None),
        (7, 2, "/f/a/two", b"second", None),
        (0, 0, "/a/commit", b"", Some(("g1", 1))),
        (8, 1, "/f/b/out", b"processed", Some(("g2", 0))),
        (9, 1, "/f/c/empty", b"", None),
    ]
}

fn assert_first_five(records: &[std::sync::Arc<BrokerRecord>]) {
    for (i, (pid, pseq, subject, body, commit)) in first_five().into_iter().enumerate() {
        let r = &records[i];
        assert_eq!(r.seq, Offset(i as u64));
        assert_eq!((r.producer_id, r.producer_seq), (pid, pseq), "record {i}");
        assert_eq!(
            (r.subject.as_str(), r.body.as_slice()),
            (subject, body),
            "record {i}"
        );
        assert_eq!(
            r.commit.as_ref().map(|c| (c.group.as_str(), c.upto)),
            commit,
            "record {i}"
        );
    }
}

#[test]
fn the_last_releases_unsealed_log_and_format_1_sidecar_open_and_read_back() {
    let (_dir, log_path) = Copied::new("v2-unsealed.log");
    let before = std::fs::read(&log_path).unwrap();
    let want = LogIdentity::parse("f4e33ee64c5f71080655149086efd2ff.0").unwrap();
    let log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
    assert_eq!(log.head(), Offset(5));
    assert_first_five(&log.read_from(Offset(0)));
    assert_eq!(log.identity(), want, "the release's identity is kept");
    drop(log);
    assert_eq!(std::fs::read(&log_path).unwrap(), before, "nothing was cut");
    // The sidecar is now FORMAT 2 (the open rewrote it); the identity stands.
    let log = BrokerLog::open_with(&log_path, Durability::Relaxed).unwrap();
    assert_eq!(log.identity(), want);
}

/// `stats().retained_bytes` is the log file's length on a log whose base is 0 and which
/// no retention has touched: after the open of a log an older build wrote, of a fresh one,
/// after an append and after a reopen. aterm-journal's checkpoint hashes that physical
/// prefix, and it refuses to open a journal whose length differs from this number.
#[test]
fn retained_bytes_is_the_files_length_on_a_log_with_no_retention() {
    for fixture in ["v2-unsealed.log", "v2-sealed.log", "fresh"] {
        let (_dir, log_path) = if fixture == "fresh" {
            let (dir, log_path) = Copied::new("v2-unsealed.log");
            let fresh = log_path.with_file_name(fixture);
            (dir, fresh)
        } else {
            Copied::new(fixture)
        };
        let length = || std::fs::metadata(&log_path).unwrap().len() as usize;
        let mut log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
        let opened = log.stats();
        assert_eq!(opened.base, Offset::ZERO, "{fixture}");
        assert_eq!(opened.retained_bytes, length(), "{fixture}: at the open");
        log.publish_checked(77, 1, "/f/c/next".into(), b"appended".to_vec())
            .unwrap();
        let appended = log.stats();
        assert!(appended.retained_bytes > opened.retained_bytes, "{fixture}");
        assert_eq!(appended.base, Offset::ZERO, "{fixture}");
        assert_eq!(
            appended.retained_bytes,
            length(),
            "{fixture}: after an append"
        );
        drop(log);
        let log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
        assert_eq!(
            log.stats().retained_bytes,
            length(),
            "{fixture}: at the reopen"
        );
    }
}

/// `BrokerRecord::from_payload` as it stood at 2888062 (the last release before the
/// seal), frozen: it returns at the commit field and never looks at what follows.
fn frozen_v2_from_payload(p: &[u8]) -> Option<Fields> {
    const HEADER: usize = 25;
    if p.len() < HEADER || p[0] != 2 {
        return None;
    }
    let seq = u64::from_le_bytes(p[1..9].try_into().ok()?);
    let producer_id = u64::from_le_bytes(p[9..17].try_into().ok()?);
    let producer_seq = u64::from_le_bytes(p[17..25].try_into().ok()?);
    let mut pos = HEADER;
    let sl = u32::from_le_bytes(p.get(pos..pos + 4)?.try_into().ok()?) as usize;
    pos += 4;
    let send = pos.checked_add(sl)?;
    let subject = String::from_utf8(p.get(pos..send)?.to_vec()).ok()?;
    pos = send;
    let bl = u32::from_le_bytes(p.get(pos..pos + 4)?.try_into().ok()?) as usize;
    pos += 4;
    let bend = pos.checked_add(bl)?;
    let body = p.get(pos..bend)?.to_vec();
    pos = bend;
    let commit = match *p.get(pos)? {
        0 => None,
        1 => {
            pos += 1;
            let gl = u32::from_le_bytes(p.get(pos..pos + 4)?.try_into().ok()?) as usize;
            pos += 4;
            let gend = pos.checked_add(gl)?;
            let group = String::from_utf8(p.get(pos..gend)?.to_vec()).ok()?;
            pos = gend;
            let upto = u64::from_le_bytes(p.get(pos..pos + 8)?.try_into().ok()?);
            Some((group, upto))
        }
        _ => return None,
    };
    Some((seq, producer_id, producer_seq, subject, body, commit))
}

#[test]
fn a_sealed_log_reads_back_through_the_frozen_v2_parser() {
    let (_dir, log_path) = Copied::new("v2-sealed.log");
    let bytes = std::fs::read(&log_path).unwrap();
    let want = LogIdentity::parse("057813af112ad1525910f21d9d15d9fc.0").unwrap();
    let log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
    assert_eq!(
        log.identity(),
        want,
        "the FORMAT 2 sidecar is read and kept"
    );
    let records = log.read_from(Offset(0));
    assert_eq!(records.len(), 29);
    assert_first_five(&records);
    drop(log);
    assert_eq!(std::fs::read(&log_path).unwrap(), bytes, "nothing was cut");

    // Every stored frame, through the frozen parser: the same record, seal or no seal.
    let mut pos = 0usize;
    let mut seals = Vec::new();
    let mut continues = Vec::new();
    for r in &records {
        let d = Frame::decode(&bytes[pos..])
            .unwrap()
            .expect("a whole frame");
        let p = &d.frame.payload;
        let old = frozen_v2_from_payload(p).expect("the frozen parser reads it");
        assert_eq!(
            old,
            (
                r.seq.0,
                r.producer_id,
                r.producer_seq,
                r.subject.clone(),
                r.body.clone(),
                r.commit.as_ref().map(|c| (c.group.clone(), c.upto))
            )
        );
        // The mark is the bytes after the last field: the seal on a batch's last record,
        // the one continues byte on every other.
        let unsealed = BrokerRecord {
            seq: r.seq,
            producer_id: r.producer_id,
            producer_seq: r.producer_seq,
            subject: r.subject.clone(),
            body: r.body.clone(),
            commit: r.commit.clone(),
        }
        .encode()
        .unwrap();
        let fields = unsealed.len() - 12;
        match &p[fields..] {
            [0xB4] => continues.push(r.seq.0),
            [0xB5, c0, c1, c2, c3] => {
                seals.push((r.seq.0, u32::from_le_bytes([*c0, *c1, *c2, *c3])))
            }
            other => panic!("record {} ends in {other:?}", r.seq.0),
        }
        pos += d.consumed;
    }
    assert_eq!(pos, bytes.len());
    // The five records the un-batched path wrote are each their own batch; the
    // pipelined ones end in seals whose counts cover them exactly.
    assert!(seals.iter().take(5).all(|&(_, c)| c == 1), "{seals:?}");
    let mut next = 0u64;
    for &(seq, count) in &seals {
        assert_eq!(
            seq + 1 - u64::from(count),
            next,
            "batches tile the log: {seals:?}"
        );
        next = seq + 1;
    }
    assert_eq!(next, 29, "the last record is sealed");
    assert!(
        seals.iter().any(|&(_, c)| c > 1),
        "some pipelined batch holds several records: {seals:?}"
    );
    // Every record of a batch but its last says the batch continues, and no other does.
    let mut expected_continues = Vec::new();
    for &(seq, count) in &seals {
        expected_continues.extend(seq + 1 - u64::from(count)..seq);
    }
    assert_eq!(continues, expected_continues, "{seals:?}");
}

/// Where each stored frame of `bytes` ends.
fn frame_ends(bytes: &[u8]) -> Vec<usize> {
    let mut ends = Vec::new();
    let mut pos = 0usize;
    while pos < bytes.len() {
        let d = Frame::decode(&bytes[pos..])
            .unwrap()
            .expect("a whole frame");
        pos += d.consumed;
        ends.push(pos);
    }
    ends
}

/// A REVERT to the release before the marks (which predates log identity too, so it
/// never rewrites `<log>.id`), then the upgrade again. This build opened the log at
/// two records, recording its durable floor there; the release then appended the
/// fixture's records 2, 3 and 4 — the very bytes it wrote: whole, CRC-valid, unmarked,
/// each acked under Strict. Reopened here (an inspection-only Strict open, as `asb
/// stats` makes), every one is kept and nothing moves: an unmarked record is a unit of
/// its own, never a torn batch whose seal was lost. The same after a clean close.
#[test]
fn a_revert_to_the_release_before_the_marks_keeps_every_record_it_appended() {
    let src =
        std::fs::read(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/v2-unsealed.log"))
            .unwrap();
    let ends = frame_ends(&src);
    assert_eq!(ends.len(), 5);
    for clean_close in [false, true] {
        let (_dir, log_path) = Copied::new("v2-unsealed.log");
        std::fs::remove_file(format!("{}.id", log_path.display())).unwrap();
        std::fs::write(&log_path, &src[..ends[1]]).unwrap();
        let mut log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
        assert_eq!(log.head(), Offset(2));
        let id = log.identity();
        if clean_close {
            log.close_clean().unwrap();
        }
        drop(log);
        // The release appends records 2..=4 and leaves the sidecar alone.
        std::fs::write(&log_path, &src).unwrap();
        let log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
        assert_eq!(
            log.head(),
            Offset(5),
            "clean close {clean_close}: nothing cut"
        );
        assert_first_five(&log.read_from(Offset(0)));
        assert_eq!(
            log.identity(),
            id,
            "clean close {clean_close}: nothing moved"
        );
        drop(log);
        assert_eq!(std::fs::read(&log_path).unwrap(), src);
    }
}

/// The documented way to give a log back an older state: RESTORE THE LOG FILE ALONE,
/// under the sidecar a sealing build keeps beside it. A copy the release before the
/// marks wrote, holding more records than the live log's durable floor, is read as
/// that release wrote it — all five records — never cut back to the floor.
#[test]
fn a_copy_the_release_wrote_restored_alone_above_the_floor_is_kept_whole() {
    let src =
        std::fs::read(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/v2-unsealed.log"))
            .unwrap();
    let ends = frame_ends(&src);
    let (_dir, log_path) = Copied::new("v2-unsealed.log");
    // The live log: the first three records, opened (its floor recorded at 3) here.
    std::fs::write(&log_path, &src[..ends[2]]).unwrap();
    let live = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
    assert_eq!(live.head(), Offset(3));
    drop(live);
    std::fs::write(&log_path, &src).unwrap();
    let log = BrokerLog::open_with(&log_path, Durability::Strict).unwrap();
    assert_eq!(log.head(), Offset(5), "the restored copy is read whole");
    assert_first_five(&log.read_from(Offset(0)));
}
