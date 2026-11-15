// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The compaction's tests (`compact.rs`): the intent and its judgement, a crash after
//! every durable step (with and without carried state, plaintext and under anti-rollback),
//! the bounded copy, the delta a finish copies and flushes, the files' permissions, and
//! what an open does with files no intent names.
//!
//! Every crash is the seam's ([`Seam::crash_after`]): the compaction stops dead after
//! that durable step, cleaning nothing up. The next open is then tried on each directory
//! the crash can leave: the files as they stand (a process that stopped dead: what the
//! kernel holds survives), and, on unix, every directory a POWER LOSS there can leave
//! (`power_loss.rs`: only what was flushed survives, and of the name changes since the
//! last directory flush only a prefix). No clock is read, nothing sleeps.
//!
//! NEGATIVE CONTROLS (each a planted break, scratch-reverted, that fails the test named):
//! no intent written, the protocol before this one (`a_crash_after_any_durable_step_*`:
//! the reopen after the rename refuses); the intent, the copy and the directory never
//! flushed (the same tests: a power loss after the rename leaves a log its base disowns,
//! or an empty one); no watermark re-identification at the open
//! (`..._under_anti_rollback`: the verified reopen refuses); a re-identification only
//! under a verified open, or none by a keyed compaction that does not verify
//! (`a_keyed_open_that_does_not_verify_leaves_a_watermark_a_verified_open_accepts`); the
//! copy reading its whole range in one read (`the_copy_holds_one_chunk_and_one_frame`);
//! no delta copied at the finish, or the bulk flushed there instead of by the unlocked
//! copy (`what_the_log_takes_while_the_copy_runs_is_kept`); no leftover cleared
//! (`an_open_clears_a_copy_no_intent_names`); a created log that keeps a deleted one's
//! intent (`a_log_created_where_a_compacting_one_was_deleted_opens_again`); the intent or
//! the staged state created under the umask
//! (`the_compactions_files_are_never_readable_more_widely_than_the_log`); and a judgement
//! that reads an unknown first frame as either side
//! (`the_open_judges_an_intent_by_the_logs_first_frame`,
//! `an_intent_that_names_neither_side_refuses_the_open`).

use super::*;
use crate::store::{BrokerLog, WillRecord};
use crate::test_scratch::Scratch;
use astream_wire::{Filter, Offset};
use std::sync::atomic::Ordering;

/// The floor every crash case compacts to: offsets 0..12 dropped, 12..24 kept.
const MIN: u64 = 12;

/// The log every case seeds (24 records) has its newest publish under this key, at
/// offset 23 — kept, so a resend of it must still dedup after any recovery.
const NEWEST_KEY: (u64, u64) = (7, 29);

#[cfg(feature = "anti-rollback")]
const KEY: [u8; 32] = [0x6d; 32];

/// A directory a crash leaves for the next open (`power_loss.rs`; unix only).
#[cfg(unix)]
type Image = crate::power_loss::Image;
#[cfg(not(unix))]
type Image = ();

/// Start recording what a power loss would leave of `dir`.
#[cfg(unix)]
fn arm_power_loss(dir: &Path) {
    crate::power_loss::arm(dir);
}
#[cfg(not(unix))]
fn arm_power_loss(_dir: &Path) {}

/// Every directory a power loss now leaves, and stop recording.
#[cfg(unix)]
fn power_loss_images() -> Vec<Image> {
    crate::power_loss::disarm()
        .expect("the power-loss model was armed")
        .images()
}
#[cfg(not(unix))]
fn power_loss_images() -> Vec<Image> {
    Vec::new()
}

/// The directory as it stands.
#[cfg(unix)]
fn capture(dir: &Path) -> Image {
    crate::power_loss::capture(dir)
}
#[cfg(not(unix))]
fn capture(_dir: &Path) -> Image {}

/// Make `dir` hold `image`.
#[cfg(unix)]
fn apply(dir: &Path, image: &Image) {
    crate::power_loss::apply(dir, image);
}
#[cfg(not(unix))]
fn apply(_dir: &Path, _image: &Image) {}

/// The log's permissions, for the intents a test writes by hand.
fn perms_of(p: &Path) -> Permissions {
    std::fs::metadata(p).unwrap().permissions()
}

/// One log in its own scratch directory, plaintext or sealed under anti-rollback.
struct Fixture {
    _root: Scratch,
    path: PathBuf,
    sealed: bool,
}

impl Fixture {
    fn new(tag: &str, sealed: bool) -> Fixture {
        let root = Scratch::new(tag);
        let path = root.path().join("log");
        Fixture {
            _root: root,
            path,
            sealed,
        }
    }

    /// The first open: creates the log (and, sealed, its watermark).
    fn create(&self) -> BrokerLog {
        #[cfg(feature = "anti-rollback")]
        if self.sealed {
            return BrokerLog::open_encrypted_verified_init(&self.path, KEY).unwrap();
        }
        #[cfg(not(feature = "anti-rollback"))]
        assert!(!self.sealed, "a sealed fixture needs anti-rollback");
        BrokerLog::open(&self.path).unwrap()
    }

    /// Every later open: sealed, the VERIFIED one, which refuses a watermark that does not
    /// name the log's first frame and base.
    fn open(&self) -> io::Result<BrokerLog> {
        #[cfg(feature = "anti-rollback")]
        if self.sealed {
            return BrokerLog::open_encrypted_verified(&self.path, KEY);
        }
        BrokerLog::open(&self.path)
    }

    fn exists(&self, p: &Path) -> bool {
        std::fs::symlink_metadata(p).is_ok()
    }

    /// The directory that holds the log and every file beside it.
    fn dir(&self) -> &Path {
        self._root.path()
    }

    /// The compaction's own files beside the log that are present.
    fn leftovers(&self) -> Vec<PathBuf> {
        let mut out = Vec::new();
        for p in [
            intent_path(&self.path),
            kept_path(&self.path),
            staged_state_path(&self.path),
        ] {
            if self.exists(&p) {
                out.push(p);
            }
        }
        out
    }
}

fn will() -> WillRecord {
    WillRecord {
        producer_id: 9,
        producer_seq: 4,
        subject: "/a/w/gone".to_string(),
        body: b"bye".to_vec(),
    }
}

/// 24 records in eight batches. A carrying log starts with a binding and a pending will
/// (which only a carrying compaction may drop); a plain one with two publishes there.
/// Both then hold a group commit and a QUIET subject's only record below the cut, and
/// twenty publishes over four subjects across it.
fn seed(log: &mut BrokerLog, carry: bool) {
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
    for i in 0..20u64 {
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
    assert_eq!(log.head(), Offset(24));
}

/// What a reader can see of a log: every record (checked to be each offset from the
/// base to the head exactly once), every `Last` row, the binding, the pending wills and
/// the group's resume point.
#[derive(Debug, PartialEq, Eq)]
struct Snap {
    base: u64,
    head: u64,
    records: Vec<(u64, u64, u64, String, Vec<u8>)>,
    last: Vec<(String, u64, Vec<u8>)>,
    binding: Option<(String, u64)>,
    wills: Vec<WillRecord>,
    group: u64,
}

fn snap(log: &mut BrokerLog) -> Snap {
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
    let (page, _) = {
        let last_head = head;
        drop(log.publish_last_visible(last_head).unwrap());
        let mut last_view = log.last_view_at(last_head).unwrap();
        log.last_matching(&all, "", 1000, 100_000, &mut last_view)
            .unwrap()
            .into_page()
            .expect("the fixed fixture fits one bounded step")
    };
    Snap {
        base,
        head,
        records: recs
            .iter()
            .map(|r| {
                (
                    r.seq.0,
                    r.producer_id,
                    r.producer_seq,
                    r.subject.clone(),
                    r.body.clone(),
                )
            })
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

fn compact(log: &mut BrokerLog, carry: bool, min: u64) -> io::Result<u64> {
    if carry {
        log.retain_before_carrying_state(Offset(min))
    } else {
        log.retain_before(Offset(min))
    }
}

#[test]
fn replacement_inode_remains_exclusively_owned_after_rename() {
    let fx = Fixture::new("compact-lock-continuity", false);
    let mut log = fx.create();
    seed(&mut log, false);
    let (gate, held) = gate();
    log.arm_compact_seam(Seam {
        step_gate: Some((Step::Rename, gate)),
        ..Seam::default()
    });
    let worker = std::thread::spawn(move || {
        let result = compact(&mut log, false, MIN);
        (log, result)
    });
    assert!(held.wait(), "compaction did not reach the renamed inode");
    let competing = fx.open();
    held.resume();
    let (mut log, result) = worker.join().unwrap();
    assert!(
        matches!(&competing, Err(error) if error.kind() == io::ErrorKind::AlreadyExists),
        "a second broker acquired the live replacement inode"
    );
    assert_eq!(result.unwrap(), MIN);
    assert!(log.poisoned().is_none());
    log.publish(9, 1, "after/switch".into(), b"still owned".to_vec())
        .unwrap();
    drop(log);
    let reopened = fx.open().unwrap();
    assert_eq!(reopened.read_floor(), Offset(MIN));
}

#[test]
fn an_opener_cannot_acquire_the_detached_inode_after_compaction() {
    let fx = Fixture::new("compact-stale-open", false);
    let mut log = fx.create();
    seed(&mut log, false);
    let files = || -> std::collections::BTreeMap<_, _> {
        std::fs::read_dir(fx.path.parent().unwrap())
            .unwrap()
            .map(|entry| {
                let path = entry.unwrap().path();
                let bytes = std::fs::read(&path).unwrap();
                (path, bytes)
            })
            .collect()
    };
    let mut before = None;
    let competing = crate::store::open_log_file(&fx.path, crate::store::sync_parent_dir, || {
        assert_eq!(compact(&mut log, false, MIN).unwrap(), MIN);
        before = Some(files());
    });
    assert!(
        matches!(&competing, Err(error) if error.kind() == io::ErrorKind::AlreadyExists),
        "an opener acquired the inode detached by the compaction"
    );
    assert_eq!(
        files(),
        before.unwrap(),
        "a refused stale opener changed the log or its sidecars"
    );
    assert!(log.poisoned().is_none());
    log.publish(9, 1, "after/switch".into(), b"still owned".to_vec())
        .unwrap();
}

#[test]
fn a_failed_post_rename_step_keeps_exclusive_ownership_until_drop() {
    for step in [
        Step::Rename,
        Step::StateInstalled,
        Step::Base,
        Step::IntentRemoved,
    ] {
        let fx = Fixture::new("compact-poisoned-lock", false);
        let mut log = fx.create();
        seed(&mut log, true);
        log.arm_compact_seam(Seam {
            crash_after: Some(step),
            ..Seam::default()
        });
        assert!(compact(&mut log, true, MIN).is_err());
        assert!(log.poisoned().is_some());
        assert!(matches!(fx.open(), Err(error) if error.kind() == io::ErrorKind::AlreadyExists));
        drop(log);
        let recovered = fx.open().unwrap();
        assert_eq!(recovered.read_floor(), Offset(MIN));
    }
}

/// The reference: the seeded log as a reopen reads it before the compaction, and after
/// an uninterrupted one.
fn reference(sealed: bool, carry: bool) -> (Snap, Snap) {
    let fx = Fixture::new("compact-ref", sealed);
    let mut log = fx.create();
    seed(&mut log, carry);
    drop(log);
    let mut log = fx.open().unwrap();
    let before = snap(&mut log);
    assert_eq!(compact(&mut log, carry, MIN).unwrap(), MIN);
    drop(log);
    let mut log = fx.open().unwrap();
    let after = snap(&mut log);
    assert_eq!((after.base, after.head), (MIN, 24));
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
    (before, after)
}

const STEPS: [Step; 8] = [
    Step::Copy,
    Step::State,
    Step::Intent,
    Step::Rename,
    Step::StateInstalled,
    Step::Base,
    Step::Watermark,
    Step::IntentRemoved,
];

/// Whether a compaction takes `step` at all: the state steps carry state, the watermark
/// step needs a watermark.
fn takes(step: Step, sealed: bool, carry: bool) -> bool {
    match step {
        Step::State | Step::StateInstalled => carry,
        Step::Watermark => sealed,
        _ => true,
    }
}

/// Whether the log on disk is the kept suffix once `step` is durable.
const fn switched(step: Step) -> bool {
    !matches!(step, Step::Copy | Step::State | Step::Intent)
}

/// THE CRASH LAW: after a crash following any durable step, whether the process stopped
/// dead or the power went (every directory that can leave), the next open opens; it reads
/// either the log as it was (the switch had not happened) or as the uninterrupted
/// compaction leaves it (it had), never anything else — no acked record lost, none read
/// twice, every `Last` row answering as before — and it leaves none of the compaction's
/// files behind. A second open reads the same, a resend of a kept record still dedups to
/// its offset, and the log compacts again.
fn crash_law(sealed: bool, carry: bool) {
    let (before, after) = reference(sealed, carry);
    if carry {
        assert_eq!(
            before.last, after.last,
            "a carrying compaction keeps every Last row"
        );
    }
    for step in STEPS {
        if !takes(step, sealed, carry) {
            continue;
        }
        let fx = Fixture::new("compact-crash", sealed);
        let mut log = fx.create();
        seed(&mut log, carry);
        drop(log);
        let mut log = fx.open().unwrap();
        log.arm_compact_seam(Seam {
            crash_after: Some(step),
            ..Seam::default()
        });
        arm_power_loss(fx.dir());
        let err = compact(&mut log, carry, MIN).expect_err("the armed crash");
        let lost = power_loss_images();
        assert!(
            err.to_string().contains("injected crash"),
            "{step:?}: {err}"
        );
        drop(log);
        let stood = capture(fx.dir());
        let want = if switched(step) { &after } else { &before };
        let left = std::iter::once(("a process crash", stood))
            .chain(lost.into_iter().map(|image| ("a power loss", image)));
        for (how, image) in left {
            apply(fx.dir(), &image);
            reopens_whole(&fx, carry, &format!("{step:?}, {how}"), want);
        }
    }
}

/// The crash law's reopen of what one crash left (`at` names the step and the crash).
fn reopens_whole(fx: &Fixture, carry: bool, at: &str, want: &Snap) {
    let mut log = fx
        .open()
        .unwrap_or_else(|e| panic!("{at}: the open after the crash refused: {e}"));
    assert_eq!(&snap(&mut log), want, "{at}");
    drop(log);
    assert!(
        fx.leftovers().is_empty(),
        "{at}: left behind {:?}",
        fx.leftovers()
    );

    let mut log = fx
        .open()
        .unwrap_or_else(|e| panic!("{at}: the second open refused: {e}"));
    assert_eq!(&snap(&mut log), want, "{at}: the second open");
    let resend = log
        .publish(NEWEST_KEY.0, NEWEST_KEY.1, "/a/s/3".into(), b"m19".to_vec())
        .unwrap();
    assert_eq!(resend, (Offset(23), true), "{at}: the kept key dedups");
    log.publish(7, 99, "/a/s/late".into(), b"late".to_vec())
        .unwrap();
    assert_eq!(compact(&mut log, carry, 20).unwrap(), 20 - want.base);
    drop(log);
    let log = fx.open().unwrap();
    assert_eq!(
        (log.base().0, log.head().0),
        (20, 25),
        "{at}: compacts again"
    );
}

#[test]
fn a_crash_after_any_durable_step_of_a_carrying_compaction_reopens_whole() {
    crash_law(false, true);
}

#[test]
fn a_crash_after_any_durable_step_of_a_plain_compaction_reopens_whole() {
    crash_law(false, false);
}

/// The same law on a log sealed at rest under anti-rollback, reopened VERIFIED: so every
/// recovery that finishes a compaction re-identifies the watermark to the kept suffix's
/// first frame and the new base, and one that discards it leaves the watermark as it was.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_crash_after_any_durable_step_under_anti_rollback_reopens_whole() {
    crash_law(true, true);
    crash_law(true, false);
}

/// A KEYED OPEN THAT DOES NOT VERIFY (an operator's inspection, a broker opened by the
/// unverified constructor) finishes a compaction a crash interrupted after its rename
/// exactly as a verified open does, the watermark included: the verified open after it
/// accepts the log and reads what the uninterrupted compaction leaves. The same holds for
/// a compaction such a handle makes itself. Each case is one crash (or none) and two
/// opens, carrying state and not.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_keyed_open_that_does_not_verify_leaves_a_watermark_a_verified_open_accepts() {
    for carry in [false, true] {
        let (_, after) = reference(true, carry);
        for step in STEPS {
            if !switched(step) || !takes(step, true, carry) {
                continue;
            }
            let fx = Fixture::new("compact-unverified", true);
            let mut log = fx.create();
            seed(&mut log, carry);
            drop(log);
            let mut log = fx.open().unwrap();
            log.arm_compact_seam(Seam {
                crash_after: Some(step),
                ..Seam::default()
            });
            compact(&mut log, carry, MIN).expect_err("the armed crash");
            drop(log);
            let mut log = BrokerLog::open_encrypted(&fx.path, KEY)
                .unwrap_or_else(|e| panic!("{step:?}: the keyed open refused: {e}"));
            assert_eq!(snap(&mut log), after, "{step:?}: the keyed open");
            drop(log);
            assert!(fx.leftovers().is_empty(), "{step:?}: {:?}", fx.leftovers());
            let mut log = fx.open().unwrap_or_else(|e| {
                panic!("{step:?}: the verified open after the keyed one refused: {e}")
            });
            assert_eq!(snap(&mut log), after, "{step:?}: the verified open");
        }

        let fx = Fixture::new("compact-unverified-live", true);
        let mut log = fx.create();
        seed(&mut log, carry);
        drop(log);
        let mut log = BrokerLog::open_encrypted(&fx.path, KEY).unwrap();
        assert_eq!(compact(&mut log, carry, MIN).unwrap(), MIN);
        drop(log);
        let mut log = fx.open().unwrap_or_else(|e| {
            panic!("the verified open after a keyed handle's compaction refused: {e}")
        });
        assert_eq!(snap(&mut log), after, "a keyed handle's own compaction");
    }
}

/// A LOG CREATED WHERE A COMPACTING ONE WAS DELETED carries none of its compaction: the
/// compaction dies after its intent, the log file alone is deleted, and the open that
/// creates the log anew clears the intent and the copy, so every open after it opens the
/// new log (with the intent left, one would judge it by a first frame it never named, and
/// refuse).
#[test]
fn a_log_created_where_a_compacting_one_was_deleted_opens_again() {
    let fx = Fixture::new("compact-created", false);
    let mut log = fx.create();
    seed(&mut log, false);
    drop(log);
    let mut log = fx.open().unwrap();
    log.arm_compact_seam(Seam {
        crash_after: Some(Step::Intent),
        ..Seam::default()
    });
    compact(&mut log, false, MIN).expect_err("the armed crash");
    drop(log);
    assert!(fx.exists(&intent_path(&fx.path)), "the intent is left");
    std::fs::remove_file(&fx.path).unwrap();

    let mut log = fx.open().expect("the open creates the log");
    assert_eq!((log.base().0, log.head().0), (0, 0));
    log.publish(1, 1, "/a/s/new".into(), b"new".to_vec())
        .unwrap();
    drop(log);
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
    let log = fx
        .open()
        .unwrap_or_else(|e| panic!("the second open of the created log refused: {e}"));
    assert_eq!((log.base().0, log.head().0), (0, 1));
}

/// THE COMPACTION'S FILES ARE NEVER READABLE MORE WIDELY THAN THE LOG: the copy, the
/// staged state (bodies of quiet subjects' `Last` rows and of pending wills) and the
/// intent (on a plaintext log its identities are bytes of two records) are created with
/// the log's own permissions, and so is the carried state an open's recovery installs. The
/// log's mode is one the umask does not give a new file here, so a file created without the
/// log's permissions shows.
#[cfg(unix)]
#[test]
fn the_compactions_files_are_never_readable_more_widely_than_the_log() {
    use std::os::unix::fs::PermissionsExt;
    let mode = |p: &Path| std::fs::metadata(p).unwrap().permissions().mode() & 0o777;
    let fx = Fixture::new("compact-perms", false);
    let probe = fx.dir().join("probe");
    std::fs::write(&probe, b"").unwrap();
    let plain = mode(&probe);
    std::fs::remove_file(&probe).unwrap();
    let want = if plain == 0o600 { 0o640 } else { 0o600 };
    let mut log = fx.create();
    seed(&mut log, true);
    drop(log);
    std::fs::set_permissions(&fx.path, Permissions::from_mode(want)).unwrap();

    let mut log = fx.open().unwrap();
    log.arm_compact_seam(Seam {
        crash_after: Some(Step::Intent),
        ..Seam::default()
    });
    compact(&mut log, true, MIN).expect_err("the armed crash");
    drop(log);
    for p in [
        kept_path(&fx.path),
        staged_state_path(&fx.path),
        intent_path(&fx.path),
    ] {
        assert_eq!(mode(&p), want, "{} (umask gives {plain:o})", p.display());
    }

    let mut log = fx.open().unwrap();
    log.arm_compact_seam(Seam {
        crash_after: Some(Step::Rename),
        ..Seam::default()
    });
    compact(&mut log, true, MIN).expect_err("the armed crash");
    drop(log);
    let log = fx.open().unwrap();
    assert_eq!(log.base().0, MIN, "the open finished the compaction");
    drop(log);
    for p in [fx.path.clone(), crate::store::state_path(&fx.path)] {
        assert_eq!(mode(&p), want, "{} (umask gives {plain:o})", p.display());
    }
}

/// THE COPY READS THROUGH THE LOG'S OWN DESCRIPTOR, never a second open of its path. On
/// Windows the open's whole-file exclusive lock (`LockFileEx` through the log's handle,
/// `lock_exclusive`) denies reads through any other handle of the file, this process's
/// included, so a copy read through a second open would fail every compaction there and the
/// log would never shrink. The Unix stand-in for that lock: once the log is open, its path is
/// made write-only (0o200), which the open's own descriptor reads past and a second open for
/// reading does not. The carrying compaction still cuts, and the log reopens (every file made
/// readable again first) as the uninterrupted compaction leaves it.
#[cfg(unix)]
#[test]
fn the_copy_reads_through_the_logs_own_descriptor() {
    use std::os::unix::fs::PermissionsExt;
    let (_, after) = reference(false, true);
    let fx = Fixture::new("compact-own-descriptor", false);
    let mut log = fx.create();
    seed(&mut log, true);
    drop(log);
    let mut log = fx.open().unwrap();
    std::fs::set_permissions(&fx.path, Permissions::from_mode(0o200)).unwrap();
    let cut = compact(&mut log, true, MIN);
    for entry in std::fs::read_dir(fx.dir()).unwrap() {
        let p = entry.unwrap().path();
        std::fs::set_permissions(&p, Permissions::from_mode(0o600)).unwrap();
    }
    assert_eq!(
        cut.expect("a compaction reading the log through its own descriptor"),
        MIN
    );
    drop(log);
    let mut log = fx.open().unwrap();
    assert_eq!(snap(&mut log), after);
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
}

/// THE COPY IS STREAMED: compacting a log many chunks long, no read the copy makes is
/// larger than one chunk plus one frame (the frames it reads whole for their identities),
/// while the suffix it copies is many times that.
#[test]
fn the_copy_holds_one_chunk_and_one_frame() {
    const CHUNK: usize = 512;
    let fx = Fixture::new("compact-stream", false);
    let mut log = fx.create();
    for i in 0..300u64 {
        log.stage_publish(
            1,
            i,
            format!("/a/s/{}", i % 7),
            vec![b'x'; 64 + (i % 5) as usize],
        )
        .unwrap();
        if i % 50 == 49 {
            log.commit_batch().unwrap();
        }
    }
    let bytes = std::fs::read(&fx.path).unwrap();
    let mut frame_max = 0usize;
    let mut pos = 0usize;
    let mut cut = 0usize;
    let mut n = 0u64;
    while let Ok(Some(d)) = Frame::decode(&bytes[pos..]) {
        frame_max = frame_max.max(d.consumed);
        pos += d.consumed;
        n += 1;
        if n == 100 {
            cut = pos;
        }
    }
    assert_eq!(pos, bytes.len());
    let kept = bytes.len() - cut;
    assert!(
        kept > 10 * (CHUNK + frame_max),
        "the suffix is many chunks long"
    );
    let meter = Arc::new(Meter::default());
    log.arm_compact_seam(Seam {
        chunk: Some(CHUNK),
        meter: Some(Arc::clone(&meter)),
        ..Seam::default()
    });
    assert_eq!(log.retain_before(Offset(100)).unwrap(), 100);
    let peak = meter.peak.load(Ordering::Relaxed);
    assert!(
        peak <= CHUNK + frame_max,
        "a read held {peak} bytes; the bound is a chunk ({CHUNK}) plus a frame ({frame_max})"
    );
    assert!(
        meter.reads.load(Ordering::Relaxed) > kept / CHUNK,
        "the suffix was read in chunks"
    );
    drop(log);
    let log = fx.open().unwrap();
    assert_eq!((log.base().0, log.head().0), (100, 300));
    assert_eq!(std::fs::metadata(&fx.path).unwrap().len() as usize, kept);
}

/// OFF THE ACK PATH, IN THE LOG: a compaction's copy runs to the durable length it began
/// at and flushes it; records the log takes after that, while the copy runs, are copied by
/// the finish before it switches, and the finish's flush covers only them. Driven by calls:
/// begin, copy, three publishes, finish; the seam's meter counts what each flush covered.
#[test]
fn what_the_log_takes_while_the_copy_runs_is_kept() {
    let fx = Fixture::new("compact-delta", false);
    let mut log = fx.create();
    for i in 0..10u64 {
        log.publish(1, i, "/a/s/x".into(), format!("m{i}").into_bytes())
            .unwrap();
    }
    let meter = Arc::new(Meter::default());
    log.arm_compact_seam(Seam {
        meter: Some(Arc::clone(&meter)),
        ..Seam::default()
    });
    let len = |p: &Path| std::fs::metadata(p).unwrap().len();
    let begun = len(&fx.path);
    let mut c = log
        .compact_begin(Offset(6), true)
        .unwrap()
        .expect("six records to drop");
    c.copy().unwrap();
    for i in 10..13u64 {
        log.publish(1, i, "/a/s/x".into(), format!("m{i}").into_bytes())
            .unwrap();
    }
    let taken = len(&fx.path) - begun;
    assert_eq!(log.compact_finish(c).unwrap(), 6);
    let kept = len(&fx.path);
    assert_eq!(
        *meter.flushes.lock().unwrap(),
        vec![kept - taken, taken],
        "the copy flushes the suffix it copied; the finish flushes only the delta"
    );
    let bodies = |log: &BrokerLog| -> Vec<(u64, Vec<u8>)> {
        log.read_from(Offset(0))
            .iter()
            .map(|r| (r.seq.0, r.body.clone()))
            .collect()
    };
    let want: Vec<(u64, Vec<u8>)> = (6..13u64)
        .map(|i| (i, format!("m{i}").into_bytes()))
        .collect();
    assert_eq!(bodies(&log), want, "in memory");
    drop(log);
    let mut log = fx.open().unwrap();
    assert_eq!((log.base().0, log.head().0), (6, 13));
    assert_eq!(
        bodies(&log),
        want,
        "the records published during the copy are in the file"
    );
    assert_eq!(
        log.publish(1, 12, "/a/s/x".into(), b"m12".to_vec())
            .unwrap(),
        (Offset(12), true)
    );
}

/// A compaction that died before its intent leaves a copy and a staged state that no
/// intent names: the next open removes them and reads the log as it was.
#[test]
fn an_open_clears_a_copy_no_intent_names() {
    let fx = Fixture::new("compact-leftover", false);
    let mut log = fx.create();
    seed(&mut log, true);
    drop(log);
    let mut log = fx.open().unwrap();
    let before = snap(&mut log);
    drop(log);
    std::fs::write(kept_path(&fx.path), b"a copy cut short").unwrap();
    std::fs::write(staged_state_path(&fx.path), b"a state never named").unwrap();
    assert_eq!(fx.leftovers().len(), 2);
    let mut log = fx.open().unwrap();
    assert_eq!(snap(&mut log), before);
    drop(log);
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
}

fn id(b: u8) -> FrameId {
    FrameId {
        fp: [b; 16],
        tag: [b.wrapping_add(100); 16],
    }
}

/// The pure judgement: the kept suffix's first frame finishes, the old one discards,
/// anything else — another frame, or an empty log where one was kept — refuses. An
/// intent that keeps nothing finishes on an empty log.
#[test]
fn the_open_judges_an_intent_by_the_logs_first_frame() {
    let keeps = Intent {
        old_base: 0,
        new_base: 5,
        old: id(1),
        new: Some(id(2)),
        carries_state: true,
    };
    assert_eq!(judge(&keeps, Some(id(2))), Verdict::Finish);
    assert_eq!(judge(&keeps, Some(id(1))), Verdict::Discard);
    assert_eq!(judge(&keeps, Some(id(3))), Verdict::Neither);
    assert_eq!(judge(&keeps, None), Verdict::Neither);
    let empties = Intent { new: None, ..keeps };
    assert_eq!(judge(&empties, None), Verdict::Finish);
    assert_eq!(judge(&empties, Some(id(1))), Verdict::Discard);
    assert_eq!(judge(&empties, Some(id(3))), Verdict::Neither);
}

/// An intent round-trips through its file, and only as itself: a file that is one frame
/// of something else — what an older build left at this name, its copy of the log, when
/// it died mid-compaction — is no intent, and an open acts on nothing for it.
#[test]
fn an_intent_round_trips_and_an_older_builds_copy_is_none() {
    let fx = Fixture::new("compact-intent", false);
    let mut log = fx.create();
    seed(&mut log, false);
    drop(log);
    let intent = Intent {
        old_base: 0,
        new_base: 7,
        old: id(4),
        new: None,
        carries_state: false,
    };
    assert_eq!(Intent::decode(&intent.encode()), Some(intent));
    let backwards = Intent {
        old_base: 7,
        new_base: 7,
        ..intent
    };
    assert_eq!(
        Intent::decode(&backwards.encode()),
        None,
        "a base that does not rise"
    );
    write_intent(&fx.path, None, &intent, &perms_of(&fx.path)).unwrap();
    assert_eq!(read_intent(&fx.path, None).unwrap(), Found::Intent(intent));
    remove_intent(&fx.path).unwrap();
    assert_eq!(read_intent(&fx.path, None).unwrap(), Found::Absent);

    let mut log = fx.open().unwrap();
    let before = snap(&mut log);
    drop(log);
    let copy = std::fs::read(&fx.path).unwrap();
    let first = Frame::decode(&copy).unwrap().unwrap().consumed;
    std::fs::write(intent_path(&fx.path), &copy[..first]).unwrap();
    assert_eq!(
        read_intent(&fx.path, None).unwrap(),
        Found::Unreadable("not an intent")
    );
    std::fs::write(intent_path(&fx.path), &copy).unwrap();
    assert_eq!(
        read_intent(&fx.path, None).unwrap(),
        Found::Unreadable("not one frame")
    );
    let mut log = fx.open().unwrap();
    assert_eq!(snap(&mut log), before);
    drop(log);
    assert_eq!(
        std::fs::read(intent_path(&fx.path)).unwrap(),
        copy,
        "left as it was"
    );

    // The opened-handle admission is also the boundary after an entry lookup:
    // replacement by a link or directory must not turn that lookup into a read.
    #[cfg(any(
        target_os = "macos",
        windows,
        all(
            target_os = "linux",
            any(target_arch = "x86_64", target_arch = "aarch64")
        )
    ))]
    {
        use crate::store::open_regular_sidecar;
        let path = intent_path(&fx.path);
        assert!(std::fs::symlink_metadata(&path).unwrap().is_file());
        std::fs::remove_file(&path).unwrap();
        #[cfg(unix)]
        {
            let target = fx.dir().join("foreign-to-intent");
            std::fs::write(&target, b"preserve").unwrap();
            std::os::unix::fs::symlink(&target, &path).unwrap();
            assert!(
                open_regular_sidecar(&path, INTENT_FILE_CAP).is_err(),
                "the post-lookup open must not follow a substituted link"
            );
            assert_eq!(std::fs::read(&target).unwrap(), b"preserve");
            std::fs::remove_file(&path).unwrap();
        }
        std::fs::create_dir(&path).unwrap();
        assert!(
            open_regular_sidecar(&path, INTENT_FILE_CAP).is_err(),
            "the opened handle must be a regular file"
        );
        std::fs::remove_dir(&path).unwrap();
        std::fs::write(&path, b"ab").unwrap();
        assert!(
            open_regular_sidecar(&path, 1).is_err(),
            "the opened file must fit its own reader's bound"
        );
        let mut admitted = open_regular_sidecar(&path, 2).unwrap();
        let mut bytes = Vec::new();
        admitted.read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes, b"ab", "an at-bound regular file is admitted");
        drop(admitted);
        assert_eq!(std::fs::read(&path).unwrap(), b"ab");
    }
}

/// Sealed under the log's at-rest key, an intent reads only under that key.
#[cfg(feature = "at-rest")]
#[test]
fn a_sealed_intent_reads_only_under_its_key() {
    let root = Scratch::new("compact-sealed-intent");
    let log = root.path().join("log");
    std::fs::write(&log, b"").unwrap();
    let intent = Intent {
        old_base: 2,
        new_base: 9,
        old: id(5),
        new: Some(id(6)),
        carries_state: true,
    };
    let k11 = crate::store::AtRestRef::v1(&[0x11; 32]);
    let k12 = crate::store::AtRestRef::v1(&[0x12; 32]);
    write_intent(&log, Some(k11), &intent, &perms_of(&log)).unwrap();
    assert_eq!(read_intent(&log, Some(k11)).unwrap(), Found::Intent(intent));
    assert_eq!(
        read_intent(&log, Some(k12)).unwrap(),
        Found::Unreadable("does not authenticate")
    );
    assert!(matches!(
        read_intent(&log, None).unwrap(),
        Found::Unreadable(_)
    ));
}

/// An intent whose identities match neither the log's first frame as it began nor the
/// kept suffix's: the log is not the one it was written for. The open refuses, naming it,
/// and changes no file.
#[test]
fn an_intent_that_names_neither_side_refuses_the_open() {
    let fx = Fixture::new("compact-neither", false);
    let mut log = fx.create();
    seed(&mut log, false);
    drop(log);
    write_intent(
        &fx.path,
        None,
        &Intent {
            old_base: 0,
            new_base: 4,
            old: id(8),
            new: Some(id(9)),
            carries_state: false,
        },
        &perms_of(&fx.path),
    )
    .unwrap();
    let files = || -> Vec<Option<Vec<u8>>> {
        [
            fx.path.clone(),
            intent_path(&fx.path),
            crate::store::base_path(&fx.path),
        ]
        .iter()
        .map(|p| std::fs::read(p).ok())
        .collect()
    };
    let untouched = files();
    let err = fx
        .open()
        .err()
        .expect("an intent for another log must refuse");
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains("neither"), "{err}");
    assert_eq!(files(), untouched, "the refusal touched a file");
}
