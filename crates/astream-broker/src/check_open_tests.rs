// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The read-only open check's tests (`check_open.rs`), on real logs with the sidecars an
//! aterm broker leaves (`.id`, `.base`, `.state`, `.held`, and sealed, `.seal`): the check
//! answers what the open answers, and every file in the log's folder is byte for byte what it
//! was before the check, no file added or gone.
//!
//! NEGATIVE CONTROLS, each on the same logs: an open closed at once, the probe a caller made
//! before the check existed, rewrites `<log>.id` (so the byte comparison sees a write); the
//! open cuts the torn tail the check only counts; and the open finishes the seal's switch and
//! the compaction the check only names, and removes their markers.

use super::*;
use crate::retention::{Retention, Rule};
use crate::test_scratch::Scratch;
use std::collections::BTreeMap;

#[cfg(feature = "at-rest")]
const KEY: [u8; 32] = [0x5a; 32];
#[cfg(feature = "at-rest")]
const OTHER_KEY: [u8; 32] = [0x5b; 32];

const EV: &str = "/f/F/pub/n1/s1/ev";
/// Mail the hold rule keeps below the cut, unread: what `.held` carries.
const MAIL: &str = "/f/F/in/n1/from/a";
/// A quiet subject whose one record falls below the cut: its `Last` row is carried in `.state`.
const QUIET: &str = "/a/q/quiet";
/// The hand clock (unix ms).
const T0: u64 = 1_800_000_000_000;

/// The keys a log is sealed under here: none, and, with `at-rest`, one.
fn keys() -> Vec<Option<[u8; 32]>> {
    #[cfg_attr(not(feature = "at-rest"), allow(unused_mut))]
    let mut keys = vec![None];
    #[cfg(feature = "at-rest")]
    keys.push(Some(KEY));
    keys
}

/// One log in its own scratch folder.
struct Fx {
    root: Scratch,
    path: PathBuf,
}

impl Fx {
    fn new(tag: &str) -> Fx {
        let root = Scratch::new(tag);
        let path = root.path().join("bus.log");
        Fx { root, path }
    }

    /// The open a broker makes of the log: bound under `key`, or keyless.
    fn open(&self, key: Option<[u8; 32]>, durability: Durability) -> io::Result<BrokerLog> {
        match key {
            #[cfg(feature = "at-rest")]
            Some(key) => BrokerLog::open_encrypted_bound_with(&self.path, durability, key),
            _ => BrokerLog::open_with(&self.path, durability),
        }
    }

    /// The refusal of a Strict open under `key`.
    fn refused(&self, key: Option<[u8; 32]>) -> io::Error {
        match self.open(key, Durability::Strict) {
            Ok(_) => panic!("{key:?}: the open served a log the check refused"),
            Err(e) => e,
        }
    }

    /// Every file in the log's folder, by name, with its bytes.
    fn files(&self) -> BTreeMap<String, Vec<u8>> {
        std::fs::read_dir(self.root.path())
            .unwrap()
            .map(|entry| {
                let entry = entry.unwrap();
                let name = entry.file_name().to_string_lossy().into_owned();
                let bytes = if entry.file_type().unwrap().is_dir() {
                    Vec::new()
                } else {
                    std::fs::read(entry.path()).unwrap()
                };
                (name, bytes)
            })
            .collect()
    }

    fn len(&self) -> u64 {
        std::fs::metadata(&self.path).unwrap().len()
    }
}

/// aterm's shape of rules, small: the bulk stream by its bytes, mail held until its node's
/// inbox reads it, everything else by its last value.
fn rules() -> Retention {
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev").unwrap().max_bytes(2_000),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .until_read("/f/{2}/cur/{4}/node/inbox")
                .unwrap(),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// A log as aterm's broker leaves one, sealed under `key` or plaintext: its rules set (a
/// `.held`), records, a cut the rules make (a `.base` and a carried `.state`), and a record
/// after it. Its last run served Relaxed and was killed, never closed cleanly, so the Strict
/// open the controls make records a run of its own in `.id`.
fn seed(fx: &Fx, key: Option<[u8; 32]>) {
    let mut log = fx.open(key, Durability::Relaxed).unwrap();
    log.set_retention(rules()).unwrap();
    log.stage_publish(9, 1, QUIET.into(), b"quiet".to_vec())
        .unwrap();
    log.stage_publish(9, 2, MAIL.into(), b"mail".to_vec())
        .unwrap();
    log.commit_batch().unwrap();
    for i in 0..60u64 {
        log.stage_publish(
            7,
            10 + i,
            EV.into(),
            format!("ev-{i:04}-padding-padding").into_bytes(),
        )
        .unwrap();
        if i % 7 == 6 {
            log.commit_batch().unwrap();
        }
    }
    log.commit_batch().unwrap();
    let tick = log.retain_by_rules(T0).unwrap();
    assert!(tick.base > 5, "the rules cut below the head: {tick:?}");
    log.publish(7, 499, EV.into(), b"after the cut".to_vec())
        .unwrap();
    drop(log);
    let files = fx.files();
    for sfx in [".id", ".base", ".state", ".held"] {
        assert!(
            files.contains_key(&format!("bus.log{sfx}")),
            "the seed has {sfx}"
        );
    }
    assert_eq!(
        files.contains_key("bus.log.seal"),
        key.is_some(),
        "a keyed seed is bound"
    );
}

/// THE LAW: a check of a log that opens writes nothing, and answers the base and head the
/// open serves. Its negative control is the probe it replaces, an open closed at once, which
/// rewrites `<log>.id` on the same log: the comparison sees a write when there is one.
#[test]
fn a_check_writes_nothing_where_an_open_closed_at_once_rewrites_the_identity() {
    for key in keys() {
        let fx = Fx::new("check-open-quiet");
        seed(&fx, key);
        let before = fx.files();
        let checked = BrokerLog::check_open(&fx.path, key).unwrap();
        let OpenCheck::Opens { base, head, torn } = checked else {
            panic!("{key:?}: the seed opens: {checked:?}");
        };
        assert!(base.0 > 5, "{key:?}: the check reads the base the cut left");
        assert_eq!(torn, 0, "{key:?}");
        assert_eq!(fx.files(), before, "{key:?}: the check wrote");
        assert_eq!(
            BrokerLog::check_open(&fx.path, key).unwrap(),
            checked,
            "{key:?}: a second check finds the log the first left"
        );

        let mut log = fx.open(key, Durability::Strict).unwrap();
        assert_eq!((log.base(), log.head()), (base, head), "{key:?}");
        log.close_clean().unwrap();
        drop(log);
        let after = fx.files();
        assert_ne!(
            after.get("bus.log.id"),
            before.get("bus.log.id"),
            "{key:?}: NEGATIVE CONTROL: an open closed at once rewrites `.id`"
        );
    }
}

/// What an open refuses the check refuses, by the open's kind, and the folder is as it was:
/// no log (and none is made), a folder (which no read-write open takes), a log another open
/// holds, a corrupt record.
#[test]
fn a_check_refuses_what_an_open_refuses_and_changes_nothing() {
    let fx = Fx::new("check-open-none");
    let none = BrokerLog::check_open(&fx.path, None).unwrap_err();
    assert_eq!(none.kind(), io::ErrorKind::NotFound, "{none}");
    assert!(fx.files().is_empty(), "the check made a log");
    std::fs::create_dir(&fx.path).unwrap();
    let folder = BrokerLog::check_open(&fx.path, None).unwrap_err();
    assert_eq!(folder.kind(), io::ErrorKind::IsADirectory, "{folder}");
    assert_eq!(
        folder.kind(),
        fx.refused(None).kind(),
        "the open's own kind"
    );

    for key in keys() {
        let fx = Fx::new("check-open-held");
        seed(&fx, key);
        let holder = fx.open(key, Durability::Strict).unwrap();
        let before = fx.files();
        let held = BrokerLog::check_open(&fx.path, key).unwrap_err();
        assert_eq!(held.kind(), io::ErrorKind::AlreadyExists, "{key:?}: {held}");
        assert_eq!(fx.files(), before, "{key:?}");
        drop(holder);

        let fx = Fx::new("check-open-corrupt");
        seed(&fx, key);
        let mut bytes = std::fs::read(&fx.path).unwrap();
        let mid = bytes.len() / 2;
        bytes[mid] ^= 0xff;
        std::fs::write(&fx.path, &bytes).unwrap();
        let before = fx.files();
        let corrupt = BrokerLog::check_open(&fx.path, key).unwrap_err();
        assert_eq!(
            corrupt.kind(),
            io::ErrorKind::InvalidData,
            "{key:?}: {corrupt}"
        );
        assert_eq!(fx.files(), before, "{key:?}");
        let opened = fx.refused(key);
        assert_eq!(
            corrupt.to_string(),
            opened.to_string(),
            "{key:?}: the open's own refusal"
        );
    }
}

/// A LOG OR A HELD STORE THE OPEN COULD NOT OPEN FOR WRITING is refused as the open refuses
/// it, `PermissionDenied`, the folder as it was: the open opens both read-write (the log, and
/// the held store for the appends it makes later), and so does the check, writing through
/// neither. CONTROL: the same files back at their own mode are answered `Opens`. Root writes
/// past a mode, so as root the check answers `Opens` at 0400 too.
#[cfg(unix)]
#[test]
fn a_log_or_held_store_no_open_could_write_is_refused_as_the_open_refuses_it() {
    use std::os::unix::fs::PermissionsExt as _;
    for key in keys() {
        for sfx in ["", ".held"] {
            let fx = Fx::new("check-open-unwritable");
            seed(&fx, key);
            let at = beside_log(&fx, sfx);
            let mode = std::fs::metadata(&at).unwrap().permissions();
            std::fs::set_permissions(&at, std::fs::Permissions::from_mode(0o400)).unwrap();
            let before = fx.files();
            let checked = BrokerLog::check_open(&fx.path, key);
            if astream_sys::euid() == 0 {
                assert!(
                    matches!(checked, Ok(OpenCheck::Opens { .. })),
                    "{key:?} {sfx:?}: root writes past a mode: {checked:?}"
                );
                continue;
            }
            let refused = checked.expect_err("no open could write it");
            assert_eq!(
                refused.kind(),
                io::ErrorKind::PermissionDenied,
                "{key:?} {sfx:?}: {refused}"
            );
            assert_eq!(fx.files(), before, "{key:?} {sfx:?}");
            assert_eq!(
                refused.kind(),
                fx.refused(key).kind(),
                "{key:?} {sfx:?}: the open's own refusal"
            );
            std::fs::set_permissions(&at, mode).unwrap();
            assert!(
                matches!(
                    BrokerLog::check_open(&fx.path, key).unwrap(),
                    OpenCheck::Opens { .. }
                ),
                "{key:?} {sfx:?}: CONTROL: writable again, it opens"
            );
        }
    }
}

/// A sealed log is checked under its key and its binding or not at all: keyless, under the
/// wrong key, and with its `.seal` gone the check refuses as the bound open does, the folder
/// as it was.
#[cfg(feature = "at-rest")]
#[test]
fn a_sealed_log_is_checked_only_under_its_key_and_its_binding() {
    let fx = Fx::new("check-open-sealed");
    seed(&fx, Some(KEY));
    for (key, what) in [(None, "keyless"), (Some(OTHER_KEY), "the wrong key")] {
        let before = fx.files();
        let refused = BrokerLog::check_open(&fx.path, key).unwrap_err();
        assert_eq!(
            refused.kind(),
            io::ErrorKind::InvalidData,
            "{what}: {refused}"
        );
        assert_eq!(fx.files(), before, "{what}");
        let opened = fx.refused(key);
        assert_eq!(
            opened.kind(),
            io::ErrorKind::InvalidData,
            "{what}: {opened}"
        );
    }
    std::fs::remove_file(seal_path(&fx.path)).unwrap();
    let before = fx.files();
    let unbound = BrokerLog::check_open(&fx.path, Some(KEY)).unwrap_err();
    assert_eq!(unbound.kind(), io::ErrorKind::InvalidData, "{unbound}");
    assert!(unbound.to_string().contains("bus.log.seal"), "{unbound}");
    assert_eq!(fx.files(), before);
    let opened = fx.refused(Some(KEY));
    assert_eq!(unbound.to_string(), opened.to_string());
}

/// A torn tail is counted, and only the open cuts it (the control): the zero-filled tail an
/// interrupted write leaves past the last record.
#[test]
fn a_torn_tail_is_counted_and_only_the_open_cuts_it() {
    for key in keys() {
        let fx = Fx::new("check-open-torn");
        seed(&fx, key);
        let whole = fx.len();
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .open(&fx.path)
            .unwrap();
        f.write_all(&[0u8; 64]).unwrap();
        drop(f);
        let before = fx.files();
        let checked = BrokerLog::check_open(&fx.path, key).unwrap();
        let OpenCheck::Opens { head, torn, .. } = checked else {
            panic!("{key:?}: a torn tail opens: {checked:?}");
        };
        assert_eq!(torn, 64, "{key:?}");
        assert_eq!(fx.files(), before, "{key:?}: the check cut");
        let log = fx.open(key, Durability::Strict).unwrap();
        assert_eq!(log.head(), head, "{key:?}");
        drop(log);
        assert_eq!(fx.len(), whole, "{key:?}: CONTROL: the open cuts the tail");
    }
}

/// A compaction a crash stopped after its rename is named, and only the open finishes it (the
/// control): the check leaves its intent, and the open moves the base and removes it.
#[test]
fn a_compaction_a_crash_left_is_named_and_only_the_open_finishes_it() {
    for key in keys() {
        let fx = Fx::new("check-open-compact");
        seed(&fx, key);
        let mut log = fx.open(key, Durability::Strict).unwrap();
        let (base, head) = (log.base().0, log.head().0);
        log.arm_compact_seam(crate::compact::Seam {
            crash_after: Some(crate::compact::Step::Rename),
            ..crate::compact::Seam::default()
        });
        log.retain_before(Offset(head - 2))
            .expect_err("the armed crash");
        drop(log);
        let before = fx.files();
        assert!(before.contains_key("bus.log.compact"), "{key:?}: an intent");
        let checked = BrokerLog::check_open(&fx.path, key).unwrap();
        let OpenCheck::Unsettled(InterruptedStep::Compaction { new_base }) = checked else {
            panic!("{key:?}: the compaction is named: {checked:?}");
        };
        assert!(
            base < new_base && new_base <= head - 2,
            "{key:?}: {new_base}"
        );
        assert_eq!(fx.files(), before, "{key:?}: the check settled it");
        let log = fx.open(key, Durability::Strict).unwrap();
        assert_eq!(
            log.base().0,
            new_base,
            "{key:?}: CONTROL: the open finishes it"
        );
        drop(log);
        assert!(!fx.files().contains_key("bus.log.compact"), "{key:?}");
    }
}

/// An offline seal's switch a crash stopped after its marker is named, keyed or keyless (the
/// open settles it before it reads the key), and only the open finishes it (the control). The
/// crash is the public seam an embedder's tests make one with
/// (`seal_plaintext_stopped_at_its_switch`).
#[cfg(all(feature = "at-rest", unix))]
#[test]
fn a_seal_switch_a_crash_left_is_named_and_only_the_open_finishes_it() {
    let fx = Fx::new("check-open-switch");
    seed(&fx, None);
    BrokerLog::seal_plaintext_stopped_at_its_switch(&fx.path, KEY).expect("stopped at its switch");
    let before = fx.files();
    assert!(before.contains_key("bus.log.sealmove"), "a marker");
    for key in [Some(KEY), None] {
        assert_eq!(
            BrokerLog::check_open(&fx.path, key).unwrap(),
            OpenCheck::Unsettled(InterruptedStep::SealSwitch),
            "{key:?}"
        );
        assert_eq!(fx.files(), before, "{key:?}: the check settled it");
    }
    drop(fx.open(Some(KEY), Durability::Strict).unwrap());
    assert!(
        !fx.files().contains_key("bus.log.sealmove"),
        "CONTROL: the open finishes the switch"
    );
    assert!(matches!(
        BrokerLog::check_open(&fx.path, Some(KEY)).unwrap(),
        OpenCheck::Opens { .. }
    ));
}

/// The settle's own refusals are the check's, before it answers `Unsettled`, the folder as it
/// was: a compaction whose base sidecar reads neither base, and a switch over a log that
/// changed after its marker. So an open that settles what the check names fails only by a
/// write.
#[test]
fn a_step_the_open_would_refuse_to_settle_is_refused_and_not_named() {
    for key in keys() {
        let fx = Fx::new("check-open-compact-refused");
        seed(&fx, key);
        let mut log = fx.open(key, Durability::Strict).unwrap();
        let head = log.head().0;
        log.arm_compact_seam(crate::compact::Seam {
            crash_after: Some(crate::compact::Step::Rename),
            ..crate::compact::Seam::default()
        });
        log.retain_before(Offset(head - 2))
            .expect_err("the armed crash");
        drop(log);
        std::fs::write(beside_log(&fx, ".base"), 999u64.to_le_bytes()).unwrap();
        let before = fx.files();
        let refused = BrokerLog::check_open(&fx.path, key).unwrap_err();
        assert_eq!(
            refused.kind(),
            io::ErrorKind::InvalidData,
            "{key:?}: {refused}"
        );
        assert!(
            refused.to_string().contains("reads 999"),
            "{key:?}: {refused}"
        );
        assert_eq!(fx.files(), before, "{key:?}");
        assert_eq!(refused.to_string(), fx.refused(key).to_string(), "{key:?}");
    }

    #[cfg(all(feature = "at-rest", unix))]
    {
        let fx = Fx::new("check-open-switch-refused");
        seed(&fx, None);
        let seam = offline_seal::Seam {
            crash_after: Some(offline_seal::Step::Marker),
            alter: None,
        };
        offline_seal::seal(&fx.path, KEY, &seam).expect_err("the armed crash");
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .open(&fx.path)
            .unwrap();
        f.write_all(b"written after the marker").unwrap();
        drop(f);
        let before = fx.files();
        let refused = BrokerLog::check_open(&fx.path, Some(KEY)).unwrap_err();
        assert_eq!(refused.kind(), io::ErrorKind::InvalidData, "{refused}");
        assert!(
            refused.to_string().contains("has changed since"),
            "{refused}"
        );
        assert_eq!(fx.files(), before);
        assert_eq!(refused.to_string(), fx.refused(Some(KEY)).to_string());
    }
}

/// `<log>` with `sfx` appended, in `fx`'s folder.
fn beside_log(fx: &Fx, sfx: &str) -> PathBuf {
    let mut p = fx.path.clone();
    p.as_mut_os_string().push(sfx);
    p
}
