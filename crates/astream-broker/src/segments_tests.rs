// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The segmented log's tests (`segments.rs`, aterm tracker LT-A8): a cut that unlinks whole
//! segments and writes no record, the roll at the segment size and the reopen across
//! segments, and what an open refuses. The power-loss law over the roll and the cut is the
//! crash simulation's (`crash_sim_segments.rs`).

use crate::segments::{list, segment_path, SegmentBytes};
use crate::store::{BrokerLog, Durability, OpenOptions, WillRecord};
use crate::test_scratch::Scratch;
use astream_wire::{Filter, Offset};
use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};

/// A segment closes at the first batch boundary at or past this: a few records each.
pub(crate) const SEGMENT: u64 = 200;

pub(crate) fn segmented() -> OpenOptions {
    OpenOptions::new(Durability::Strict).with_segment_bytes(SegmentBytes::exactly(SEGMENT))
}

pub(crate) fn open_segmented(path: &Path) -> io::Result<BrokerLog> {
    BrokerLog::open_opts(path, segmented(), BrokerLog::prepare_nothing)
}

/// One log in its own scratch directory.
pub(crate) struct Fixture {
    /// Held for its drop, which removes the folder; read only through [`Fixture::dir`].
    #[cfg_attr(
        not(unix),
        expect(
            dead_code,
            reason = "read only by dir(), which only the Unix crash simulation calls"
        )
    )]
    root: Scratch,
    pub(crate) path: PathBuf,
}

impl Fixture {
    pub(crate) fn new(tag: &str) -> Fixture {
        let root = Scratch::new(tag);
        let path = root.path().join("log");
        Fixture { root, path }
    }

    /// The log's folder: the crash simulation's (`crash_sim_segments.rs`, Unix's alone).
    #[cfg(unix)]
    pub(crate) fn dir(&self) -> &Path {
        self.root.path()
    }

    /// Every segment file beside the log: its base, inode and bytes.
    pub(crate) fn segments(&self) -> BTreeMap<u64, (u64, Vec<u8>)> {
        let mut out = BTreeMap::new();
        for base in list(&self.path).unwrap() {
            let p = segment_path(&self.path, base);
            out.insert(base, (inode(&p), std::fs::read(&p).unwrap()));
        }
        out
    }
}

#[cfg(unix)]
fn inode(p: &Path) -> u64 {
    use std::os::unix::fs::MetadataExt;
    std::fs::metadata(p).unwrap().ino()
}

#[cfg(not(unix))]
fn inode(_p: &Path) -> u64 {
    0
}

pub(crate) fn will() -> WillRecord {
    WillRecord {
        producer_id: 9,
        producer_seq: 4,
        subject: "/a/w/gone".to_string(),
        body: b"bye".to_vec(),
    }
}

/// 30 records over many segments: a carrying log starts with a binding and a pending will
/// (which only a carrying cut may drop), a plain one with two publishes there; both then hold
/// a group commit and a QUIET subject's only record at the front (all below any cut the tests
/// take), then publishes over four subjects in batches of three.
pub(crate) fn seed(log: &mut BrokerLog, carry: bool) {
    if carry {
        log.stage_bind(7, "alice".into()).unwrap();
        log.stage_will_register(&will()).unwrap();
    } else {
        log.stage_publish(3, 1, "/a/p/early".into(), b"e0".to_vec())
            .unwrap();
        log.stage_publish(3, 2, "/a/p/early".into(), b"e1".to_vec())
            .unwrap();
    }
    log.stage_commit("g1".into(), 1).unwrap();
    log.stage_publish(7, 1, "/a/p/quiet".into(), b"quiet".to_vec())
        .unwrap();
    log.commit_batch().unwrap();
    for i in 0..26u64 {
        log.stage_publish(
            7,
            10 + i,
            format!("/a/s/{}", i % 4),
            format!("m{i}").into_bytes(),
        )
        .unwrap();
        if i % 3 == 2 {
            log.commit_batch().unwrap();
        }
    }
    log.commit_batch().unwrap();
    assert_eq!(log.head(), Offset(30));
}

/// What a reader sees of a log: every record (each offset from the base to the head exactly
/// once), every `Last` row, the binding, the pending wills and the group's resume point.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Snap {
    pub(crate) base: u64,
    pub(crate) head: u64,
    pub(crate) records: Vec<(u64, String, Vec<u8>)>,
    pub(crate) last: Vec<(String, u64, Vec<u8>)>,
    pub(crate) binding: Option<(String, u64)>,
    pub(crate) wills: Vec<WillRecord>,
    pub(crate) group: u64,
}

pub(crate) fn snap(log: &mut BrokerLog) -> Snap {
    let (base, head) = (log.base().0, log.head().0);
    let recs = log.read_from(Offset(0));
    for (i, r) in recs.iter().enumerate() {
        assert_eq!(
            r.seq.0,
            base + i as u64,
            "a record read twice, or one missing"
        );
    }
    assert_eq!(
        recs.len() as u64,
        head - base,
        "records missing below the head"
    );
    let all = Filter::new("/>").unwrap();
    drop(log.publish_last_visible(head).unwrap());
    let mut view = log.last_view_at(head).unwrap();
    let (page, _) = log
        .last_matching(&all, "", 1000, 100_000, &mut view)
        .unwrap()
        .into_page()
        .expect("the fixture fits one bounded step");
    Snap {
        base,
        head,
        records: recs
            .iter()
            .map(|r| (r.seq.0, r.subject.clone(), r.body.clone()))
            .collect(),
        last: page
            .iter()
            .map(|r| (r.subject.clone(), r.seq.0, r.body.clone()))
            .collect(),
        binding: log.binding(7).map(|(p, off)| (p.to_string(), off.0)),
        wills: log.pending_wills(),
        group: log.group_start("g1").0,
    }
}

/// THE CUT WRITES NO RECORD: a carrying cut of a segmented log to offset 13 takes the base of
/// the newest segment at or below it, UNLINKS the segments below that base, and leaves every
/// kept segment the same file (its inode) holding the same bytes; the bytes retention wrote of
/// records ([`BrokerLog::retention_copied_bytes`]) do not move, and no copy (`<log>.kept`) is
/// ever made. What the dropped segments held that a reader still needs stays in `<log>.state`:
/// the binding, the pending will, the group's commit and the quiet subject's `Last` row all
/// answer as before the cut, and again after a reopen, which reads the kept segments whole.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): the same test on a ONE-FILE log
/// (`OpenOptions::new(Durability::Strict)`, no `segment_bytes`), whose cut copies the kept
/// suffix to `<log>.kept`, fails the 0-bytes check: "a cut wrote record bytes: left: 1128,
/// right: 0" (the kept suffix it copied).
#[test]
fn retention_cut_unlinks_segments_without_copy() {
    let fx = Fixture::new("seg-cut");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, true);
    let before = snap(&mut log);
    let segs = fx.segments();
    let copied = log.retention_copied_bytes();

    let dropped = log.retain_before_carrying_state(Offset(13)).unwrap();

    assert_eq!(
        log.retention_copied_bytes() - copied,
        0,
        "a cut wrote record bytes"
    );
    assert!(
        segs.len() >= 5,
        "the seed spans segments: {:?}",
        segs.keys()
    );
    let floor = *segs.keys().filter(|&&b| b <= 13).max().unwrap();
    assert!(floor > 0 && floor <= 13);
    assert_eq!(dropped, floor, "the cut takes the segment's base");
    assert_eq!(log.base(), Offset(floor));
    let after = fx.segments();
    let kept: BTreeMap<_, _> = segs
        .iter()
        .filter(|(&b, _)| b >= floor)
        .map(|(b, v)| (*b, v.clone()))
        .collect();
    assert_eq!(
        after, kept,
        "the kept segments are the same files with the same bytes, and the rest are gone"
    );
    assert!(
        !crate::compact::kept_path(&fx.path).exists(),
        "no copy was made"
    );
    assert!(!crate::compact::intent_path(&fx.path).exists());
    assert!(
        crate::store::state_path(&fx.path).exists(),
        "the carry is in .state"
    );

    let mut want = before.clone();
    want.base = floor;
    want.records.retain(|r| r.0 >= floor);
    assert_eq!(
        snap(&mut log),
        want,
        "the cut drops the records below its base only"
    );
    assert_eq!(
        want.last.iter().find(|r| r.0 == "/a/p/quiet").map(|r| r.1),
        Some(3),
        "the quiet subject's Last row is carried"
    );
    drop(log);

    let mut log = open_segmented(&fx.path).unwrap();
    assert_eq!(
        snap(&mut log),
        want,
        "the reopen reads the kept segments whole"
    );
    assert_eq!(fx.segments(), kept, "the reopen writes none of them");
    log.publish(7, 99, "/a/s/late".into(), b"late".to_vec())
        .unwrap();
    assert_eq!(log.head(), Offset(31));
}

/// THE ROLL: a segment closes at the first batch boundary at or past the size, the next one
/// is named for the head's offset, every segment begins with the record its name gives, and a
/// reopen reads them all as one log. A segmented log opened without the option keeps its
/// segments; a one-file log opened with it is refused, untouched.
#[test]
fn a_segmented_log_rolls_at_its_size_and_reopens_whole() {
    let fx = Fixture::new("seg-roll");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, true);
    let want = snap(&mut log);
    let segs = fx.segments();
    let bases: Vec<u64> = segs.keys().copied().collect();
    assert_eq!(bases.first(), Some(&0));
    for (base, (_, bytes)) in &segs {
        assert!(!bytes.is_empty() || Some(base) == bases.last());
        let (payload, _) = astream_wire::frame::decode_frame_slice(bytes)
            .unwrap()
            .expect("a whole first frame");
        let (rec, _, _) = crate::brecord::BrokerRecord::from_payload_marked_bt(payload).unwrap();
        assert_eq!(
            rec.seq.0, *base,
            "the segment named {base} starts with that record"
        );
    }
    let (count, _) = log.disk_segments_and_bytes();
    assert!(count > segs.len() as u64);
    drop(log);

    let mut log = BrokerLog::open(&fx.path).unwrap();
    assert_eq!(
        snap(&mut log),
        want,
        "an open without the option keeps the segments"
    );
    drop(log);

    let one = Fixture::new("seg-one-file");
    let mut plain = BrokerLog::open(&one.path).unwrap();
    plain.publish(7, 1, "/a/x".into(), b"x".to_vec()).unwrap();
    drop(plain);
    let bytes = std::fs::read(&one.path).unwrap();
    let Err(err) = open_segmented(&one.path) else {
        panic!("a one-file log opened with segments");
    };
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput, "{err}");
    assert_eq!(
        std::fs::read(&one.path).unwrap(),
        bytes,
        "refused untouched"
    );
    assert!(list(&one.path).unwrap().is_empty());
}

/// A segmented log whose segments do not make one is REFUSED, not read short: a sealed
/// segment removed from the middle (the scan meets the offset gap), and an anchor emptied
/// beside segments (read as a new empty log, it would drop every record).
#[test]
fn an_open_refuses_segments_that_do_not_make_a_log() {
    let fx = Fixture::new("seg-gap");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, true);
    drop(log);
    let bases: Vec<u64> = fx.segments().keys().copied().collect();
    let middle = bases[bases.len() / 2];
    let p = segment_path(&fx.path, middle);
    let held = std::fs::read(&p).unwrap();
    std::fs::remove_file(&p).unwrap();
    assert!(
        open_segmented(&fx.path).is_err(),
        "a missing middle segment refuses"
    );
    std::fs::write(&p, &held).unwrap();
    assert!(open_segmented(&fx.path).is_ok());

    std::fs::write(&fx.path, b"").unwrap();
    let Err(err) = BrokerLog::open(&fx.path) else {
        panic!("an emptied anchor beside segments opened");
    };
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
    assert_eq!(fx.segments().len(), bases.len(), "nothing removed");
}

/// THE FIRST KEPT FRAME IS READ AT THE FINISH: a cut that keeps the active segment while it is
/// still empty (what a crash in a roll leaves, an empty newest segment at the head) and sees
/// the writer append its first record before the finish names that record in its intent, so
/// a crash after the base moved is finished by the reopen, not refused as a first frame that
/// is neither side's.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): a finish that keeps the first frame
/// read at the begin (none) fails: "... names a compaction from base 0 to base 30, but the
/// log's first frame is neither the one it began with nor the one it kept; refusing to open".
#[test]
fn a_cut_names_the_first_frame_appended_between_its_begin_and_its_finish() {
    use crate::compact::{Seam, Step};
    let fx = Fixture::new("seg-late-first");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, false);
    drop(log);
    std::fs::File::create(segment_path(&fx.path, 30)).unwrap();
    let mut log = open_segmented(&fx.path).unwrap();
    log.arm_compact_seam(Seam {
        crash_after: Some(Step::Base),
        ..Seam::default()
    });
    let mut c = log
        .compact_begin(Offset(30), false)
        .unwrap()
        .expect("a cut to the head");
    c.copy().unwrap();
    log.publish(7, 99, "/a/s/late".into(), b"late".to_vec())
        .unwrap();
    let err = log.compact_finish(c).expect_err("the armed crash");
    assert!(err.to_string().contains("injected crash"), "{err}");
    drop(log);
    let mut log = open_segmented(&fx.path).expect("the reopen finishes the cut");
    assert_eq!((log.base(), log.head()), (Offset(30), Offset(31)));
    let got = snap(&mut log);
    assert_eq!(
        got.records,
        vec![(30, "/a/s/late".to_string(), b"late".to_vec())]
    );
    assert_eq!(list(&fx.path).unwrap(), vec![30]);
}

/// A CUT BACK INTO A SEALED SEGMENT: an explicit repair of damage in a sealed segment, and a
/// replica's truncation to its primary, keep the log up to the cut, unlink every segment past
/// it and leave the segment holding it the active one; the reopen reads the same, and the log
/// takes appends (and rolls) again.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): the same cuts through the active
/// segment's resize alone fail: "the segmented log writes only its active segment, which
/// starts at byte 1872; byte 1275 is in a sealed one".
#[test]
fn a_repair_and_a_replica_cut_back_into_a_sealed_segment() {
    // Repair: one byte of a sealed segment in the middle flipped.
    let fx = Fixture::new("seg-repair");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, false);
    let before = snap(&mut log);
    drop(log);
    let bases: Vec<u64> = fx.segments().keys().copied().collect();
    let middle = bases[bases.len() / 2];
    let p = segment_path(&fx.path, middle);
    let mut bytes = std::fs::read(&p).unwrap();
    let at = bytes.len() / 2;
    bytes[at] ^= 0xFF;
    std::fs::write(&p, &bytes).unwrap();
    let Err(err) = open_segmented(&fx.path) else {
        panic!("damage in a sealed segment opened");
    };
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
    let (log, dropped) = BrokerLog::open_repair(&fx.path, Durability::Strict).unwrap();
    let head = log.head().0;
    assert!(dropped > 0 && (middle..30).contains(&head), "{head}");
    drop(log);
    let left = list(&fx.path).unwrap();
    assert!(left.iter().all(|&b| b <= head), "{left:?} past {head}");
    assert_eq!(
        left.last(),
        Some(&middle),
        "the damaged segment is the active one"
    );
    let mut log = open_segmented(&fx.path).unwrap();
    let got = snap(&mut log);
    assert_eq!(got.head, head);
    assert_eq!(got.records, before.records[..head as usize]);
    for i in 0..12u64 {
        log.publish(8, i, "/a/s/again".into(), b"again".to_vec())
            .unwrap();
    }
    drop(log);
    let log = open_segmented(&fx.path).unwrap();
    assert_eq!(log.head().0, head + 12);
    assert!(list(&fx.path).unwrap().len() > left.len(), "it rolls again");
    drop(log);

    // Replica: truncated to one record into a sealed segment.
    let fx = Fixture::new("seg-replica");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, false);
    let before = snap(&mut log);
    drop(log);
    let bases: Vec<u64> = fx.segments().keys().copied().collect();
    let middle = bases[bases.len() / 2];
    let mut marker = fx.path.clone().into_os_string();
    marker.push(".replica");
    std::fs::write(&marker, b"a replication target\n").unwrap();
    let mut log = open_segmented(&fx.path).unwrap();
    assert_eq!(
        log.truncate_replica_to(Offset(middle + 1)).unwrap(),
        30 - (middle + 1)
    );
    assert_eq!(log.head().0, middle + 1);
    drop(log);
    assert_eq!(list(&fx.path).unwrap().last(), Some(&middle));
    let mut log = open_segmented(&fx.path).unwrap();
    let got = snap(&mut log);
    assert_eq!(got.records, before.records[..=middle as usize]);
}

/// A REPAIR CUTS AT A GAP BETWEEN SEGMENTS: a sealed segment in the middle missing, or emptied,
/// is refused by a plain open (the scan meets the offset gap), and the explicit repair keeps
/// the records before the gap, unlinks every segment from the gap on (the one after it is
/// named for the gap's far side) and leaves the segment that ends at the gap the active one,
/// so the log reopens whole and its next roll names the next segment for the head.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): with the segment that starts at the
/// cut held to its name, the repair of the missing segment fails: "the segmented log is not
/// whole: the segment named for offset 22 does not start with that record (it starts at
/// byte 1076 of the log, which keeps 16 records from 0)".
#[test]
fn a_repair_cuts_at_a_gap_between_segments() {
    for emptied in [false, true] {
        let fx = Fixture::new(if emptied {
            "seg-gap-emptied"
        } else {
            "seg-gap-missing"
        });
        let mut log = open_segmented(&fx.path).unwrap();
        seed(&mut log, false);
        let before = snap(&mut log);
        drop(log);
        let bases: Vec<u64> = fx.segments().keys().copied().collect();
        let (gap, prior) = (bases[bases.len() / 2], bases[bases.len() / 2 - 1]);
        let p = segment_path(&fx.path, gap);
        if emptied {
            std::fs::write(&p, b"").unwrap();
        } else {
            std::fs::remove_file(&p).unwrap();
        }
        assert!(
            open_segmented(&fx.path).is_err(),
            "emptied {emptied}: a plain open refuses"
        );
        let (log, dropped) = BrokerLog::open_repair(&fx.path, Durability::Strict)
            .unwrap_or_else(|e| panic!("emptied {emptied}: the repair: {e}"));
        assert!(dropped > 0);
        assert_eq!(log.head().0, gap, "emptied {emptied}: kept up to the gap");
        drop(log);
        assert_eq!(
            list(&fx.path).unwrap().last(),
            Some(&prior),
            "emptied {emptied}: the segment ending at the gap is the active one"
        );
        let mut log = open_segmented(&fx.path).unwrap();
        let got = snap(&mut log);
        assert_eq!(got.records, before.records[..gap as usize]);
        for i in 0..12u64 {
            log.publish(8, i, "/a/s/again".into(), b"again".to_vec())
                .unwrap();
        }
        drop(log);
        let log = open_segmented(&fx.path).unwrap();
        assert_eq!(log.head().0, gap + 12);
        assert!(
            list(&fx.path).unwrap().contains(&gap),
            "emptied {emptied}: the next roll names the segment after the gap's base again"
        );
    }
}

/// A ROLL'S FAILED FULL FLUSH IS EVERY FAILED FULL FLUSH: on a Relaxed log, whose acks no
/// full flush covered, the roll's flush of the active segment failing (the injected fsync
/// fault) counts as a failed flush, latches the log to Strict and poisons it, as a failed
/// horizon flush does.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): a roll that only poisons the log
/// fails: "a failed flush counted: left: 0, right: 1".
#[test]
fn a_rolls_failed_flush_is_a_failed_full_flush() {
    let fx = Fixture::new("seg-roll-flush");
    let opts =
        OpenOptions::new(Durability::Relaxed).with_segment_bytes(SegmentBytes::exactly(SEGMENT));
    let mut log = BrokerLog::open_opts(&fx.path, opts, BrokerLog::prepare_nothing).unwrap();
    log.publish(7, 1, "/a/s/0".into(), b"zero".to_vec())
        .unwrap();
    log.inject_faults(crate::store::InjectedFaults {
        sync: true,
        ..Default::default()
    });
    let mut refused = None;
    for i in 2..40u64 {
        if let Err(e) = log.publish(7, i, "/a/s/0".into(), b"record".to_vec()) {
            refused = Some(e);
            break;
        }
    }
    let err = refused.expect("a roll came due");
    assert!(err.to_string().contains("injected fsync fault"), "{err}");
    assert_eq!(log.flush_counts().failed, 1, "a failed flush counted");
    assert!(log.poisoned().is_some(), "poisoned");
    assert_eq!(
        log.served().reason,
        crate::proto::ServedReason::LatchedAfterFlushFailure,
        "latched to Strict"
    );
}

/// A NEXT SEGMENT THAT CANNOT BE CREATED REFUSES ONE APPEND, NOT THE LOG: with the log's
/// directory read-only, the append whose roll is due is refused and the log is not poisoned
/// (nothing changed: the active segment was flushed whole); once the directory is writable
/// again the next append rolls and every record reads back.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): a roll that poisons the log on any
/// failure fails: "not poisoned by a segment it could not create".
#[cfg(unix)]
#[test]
fn a_segment_that_cannot_be_created_refuses_one_append() {
    use std::os::unix::fs::PermissionsExt;
    let fx = Fixture::new("seg-roll-create");
    let mut log = open_segmented(&fx.path).unwrap();
    log.publish(7, 1, "/a/s/0".into(), b"zero".to_vec())
        .unwrap();
    std::fs::set_permissions(fx.dir(), std::fs::Permissions::from_mode(0o500)).unwrap();
    // Running as root (or on a filesystem that ignores the mode) defeats the scenario:
    // probe rather than guess.
    let probe = fx.dir().join("probe");
    if std::fs::File::create(&probe).is_ok() {
        let _ = std::fs::remove_file(&probe);
        std::fs::set_permissions(fx.dir(), std::fs::Permissions::from_mode(0o700)).unwrap();
        return;
    }
    let mut refused = None;
    let mut seq = 2u64;
    while seq < 40 {
        let r = log.publish(7, seq, "/a/s/0".into(), b"record".to_vec());
        seq += 1;
        if let Err(e) = r {
            refused = Some(e);
            break;
        }
    }
    std::fs::set_permissions(fx.dir(), std::fs::Permissions::from_mode(0o700)).unwrap();
    let err = refused.expect("a roll came due");
    assert_eq!(err.kind(), io::ErrorKind::PermissionDenied, "{err}");
    assert!(
        log.poisoned().is_none(),
        "not poisoned by a segment it could not create"
    );
    let head = log.head().0;
    let segs = list(&fx.path).unwrap().len();
    log.publish(7, seq, "/a/s/0".into(), b"after".to_vec())
        .unwrap();
    assert_eq!(log.head().0, head + 1);
    assert_eq!(list(&fx.path).unwrap().len(), segs + 1, "it rolled");
    drop(log);
    let mut log = open_segmented(&fx.path).unwrap();
    assert_eq!(snap(&mut log).head, head + 1);
}

/// A FULL FLUSH SETTLES NO FURTHER THAN THE HEAD: a flush issued for the replica's head, which
/// settles after a truncation cut the log below it (on a segmented log, the flush of a segment
/// the cut unlinked), leaves the durable head at the truncated head, so the records appended
/// again above it still owe their full flush.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-19): a settle that takes its target
/// whole fails: "the durable head past the log's head: 30 > 5".
#[test]
fn a_full_flush_settles_no_further_than_the_head() {
    let fx = Fixture::new("seg-flush-clamp");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, false);
    drop(log);
    let mut marker = fx.path.clone().into_os_string();
    marker.push(".replica");
    std::fs::write(&marker, b"a replication target\n").unwrap();
    let mut log = open_segmented(&fx.path).unwrap();
    let issued = log.head().0;
    log.truncate_replica_to(Offset(5)).unwrap();
    log.full_flush_done(issued);
    assert!(
        log.durable_head().0 <= log.head().0,
        "the durable head past the log's head: {} > {}",
        log.durable_head().0,
        log.head().0
    );
}
