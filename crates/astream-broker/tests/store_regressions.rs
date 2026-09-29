//! Regression tests for the durable log (`store.rs`): each one pins a defect that
//! was reproducible through `BrokerLog`'s public API. Each exercises an optional
//! feature of the log (retention, at-rest encryption, anti-rollback).
#![cfg(any(feature = "retention", feature = "at-rest"))]

use astream_broker::BrokerLog;
use astream_wire::Offset;
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
        Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
    }
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            remove_with_sidecars(path);
        }
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory — a file, a symlink
/// (never its target), or a directory planted at a sidecar's name.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
            let _ = std::fs::remove_dir_all(entry.path());
        }
    }
}

fn tmp(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("asstore_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&path]), path)
}

fn sidecar(log: &std::path::Path, ext: &str) -> std::path::PathBuf {
    let mut s = log.as_os_str().to_os_string();
    s.push(ext);
    std::path::PathBuf::from(s)
}

fn cleanup(log: &std::path::Path) {
    for ext in ["", ".base", ".hw", ".hw.tmp", ".compact", ".replica"] {
        let p = sidecar(log, ext);
        let _ = std::fs::remove_file(&p);
        let _ = std::fs::remove_dir(&p);
    }
}

/// After retention the retained records sit base-relative in memory, but `fetch` and
/// `last_matching` are addressed by ABSOLUTE offset. Both must map through the base:
/// `fetch` from a retained offset returns exactly the records at and after it, and
/// the last-value page returns each subject's OWN newest record — never the record
/// that happens to sit at that index after compaction (another subject's), and
/// nothing for a subject whose newest record was pruned.
#[cfg(feature = "retention")]
#[test]
fn fetch_and_last_value_read_the_right_records_after_retention() {
    use astream_wire::Filter;
    let (_tmp, path) = tmp("retreads");
    cleanup(&path);
    let mut log = BrokerLog::open(&path).unwrap();
    for i in 0..5u64 {
        log.publish(1, i, format!("/a/s/{i}"), format!("m{i}").into_bytes())
            .unwrap();
    }
    assert_eq!(log.retain_before(Offset(3)).unwrap(), 3);
    let head = log.head().0;
    let all = Filter::new("/a/>").unwrap();

    let (page, next) = log.fetch(3, &all, 10, 100, head);
    let got: Vec<(u64, &[u8])> = page.iter().map(|r| (r.seq.0, &r.body[..])).collect();
    assert_eq!(got, vec![(3, &b"m3"[..]), (4, &b"m4"[..])]);
    assert_eq!(next, head);
    let (page, _) = log.fetch(4, &all, 10, 100, head);
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].seq, Offset(4));
    // A read from below the base starts at the earliest retained record, and the
    // pruned range does not eat the scan budget.
    let (page, next) = log.fetch(0, &all, 10, 2, head);
    let seqs: Vec<u64> = page.iter().map(|r| r.seq.0).collect();
    assert_eq!((seqs, next), (vec![3, 4], head));

    // A wildcard-free filter can only ever be answered with its own subject.
    let (page, _) = log.last_matching(&Filter::new("/a/s/0").unwrap(), "", 10, 100, head);
    assert!(
        page.is_empty(),
        "subject /a/s/0 was pruned, yet the page answered it with {:?}",
        page.iter().map(|r| &r.subject).collect::<Vec<_>>()
    );
    let (page, _) = log.last_matching(&Filter::new("/a/s/*").unwrap(), "", 10, 100, head);
    let got: Vec<(&str, u64)> = page.iter().map(|r| (r.subject.as_str(), r.seq.0)).collect();
    assert_eq!(got, vec![("/a/s/3", 3), ("/a/s/4", 4)]);
    drop(log);
}

/// The anti-rollback watermark is fail-closed: a record is never acknowledged unless
/// the watermark covers it. When the watermark write fails after the record's own
/// fsync, the log must not be left in a state where a retry of the same key either
/// appends a SECOND copy (the un-batched path skipped its dedup insert) or is
/// acknowledged as a dedup hit the watermark does not cover.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_failed_watermark_write_neither_duplicates_nor_acks_the_retry() {
    const KEY: [u8; 32] = [0x41; 32];
    let (_tmp, path) = tmp("hwfail");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"one".to_vec()).unwrap();
        // The watermark is rewritten through `<log>.hw.tmp`; a directory there makes
        // that write fail after the record itself is durable.
        std::fs::create_dir(sidecar(&path, ".hw.tmp")).unwrap();
        assert!(log.publish(1, 2, "/a/x".into(), b"two".to_vec()).is_err());
        std::fs::remove_dir(sidecar(&path, ".hw.tmp")).unwrap();
        // The retry must not append another copy, and must not be acknowledged while
        // the watermark is behind.
        match log.publish(1, 2, "/a/x".into(), b"two".to_vec()) {
            Err(_) => {}
            Ok(r) => panic!("the retry was acknowledged ({r:?}) past a failed watermark"),
        }
        assert!(log.head().0 <= 2, "a second copy was appended");
    }
    // Reopen: the record that did land is recovered once, the watermark catches up,
    // and the retried key dedups to it.
    let mut log = BrokerLog::open_encrypted_verified(&path, KEY).unwrap();
    assert_eq!(log.head(), Offset(2));
    assert_eq!(
        log.publish(1, 2, "/a/x".into(), b"two".to_vec()).unwrap(),
        (Offset(1), true)
    );
    drop(log);
}

/// Retention replaces the log file with a compacted copy; the copy must keep the
/// original's permissions. The log is a recording of every published byte, and an
/// operator who restricted it (0600) must not find it re-created with the umask
/// default after a compaction.
#[cfg(all(unix, feature = "retention"))]
#[test]
fn retention_keeps_the_log_file_permissions() {
    use std::os::unix::fs::PermissionsExt;
    let (_tmp, path) = tmp("retperm");
    cleanup(&path);
    let mut log = BrokerLog::open(&path).unwrap();
    for i in 0..4u64 {
        log.publish(1, i, "/a/x".into(), b"secret".to_vec())
            .unwrap();
    }
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
    assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    let mode = std::fs::metadata(&path).unwrap().permissions().mode() & 0o777;
    assert_eq!(mode, 0o600, "compaction widened the log's permissions");
    drop(log);
}

/// No record can be written at offset `u64::MAX` (no offset follows it). One found on
/// disk — reachable only through a crafted `<log>.base` sidecar — is refused as
/// corruption rather than overflowing the offset arithmetic on open.
#[cfg(feature = "retention")]
#[test]
fn a_record_at_the_last_offset_is_refused_on_open() {
    let (_tmp, path) = tmp("maxoff");
    cleanup(&path);
    let rec = astream_broker::BrokerRecord {
        seq: Offset(u64::MAX),
        producer_id: 1,
        producer_seq: 1,
        subject: "/a/x".into(),
        body: b"x".to_vec(),
        commit: None,
    };
    std::fs::write(&path, rec.encode().unwrap()).unwrap();
    std::fs::write(sidecar(&path, ".base"), u64::MAX.to_le_bytes()).unwrap();
    let err = BrokerLog::open(&path).err().expect("must refuse to open");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
}

/// An append at the last offset fails BEFORE a byte is written: a record the log
/// cannot give a successor offset to must not reach the disk (where it would make
/// the log unopenable) or the last-value index.
#[cfg(feature = "retention")]
#[test]
fn an_append_at_the_last_offset_writes_nothing() {
    let (_tmp, path) = tmp("maxappend");
    cleanup(&path);
    std::fs::write(sidecar(&path, ".base"), u64::MAX.to_le_bytes()).unwrap();
    let mut log = BrokerLog::open(&path).unwrap();
    assert_eq!(log.head(), Offset(u64::MAX));
    assert!(log.publish(1, 1, "/a/x".into(), b"x".to_vec()).is_err());
    assert!(log.commit("g".into(), 1).is_err());
    assert_eq!(
        log.subjects_per_producer(1),
        0,
        "the failed append was indexed"
    );
    drop(log);
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        0,
        "bytes were written"
    );
    assert_eq!(BrokerLog::open(&path).unwrap().head(), Offset(u64::MAX));
}

/// The record cap holds on an encrypted log too: a record whose payload is exactly
/// `MAX_RECORD_PAYLOAD` is stored and recovered with its sealing overhead, so a
/// record a plaintext leader accepts is one an encrypting follower can store.
#[cfg(feature = "at-rest")]
#[test]
fn an_encrypted_log_stores_a_record_at_the_record_cap() {
    const KEY: [u8; 32] = [0x13; 32];
    let (_tmp, path) = tmp("capenc");
    cleanup(&path);
    let fixed = 1 + 8 + 8 + 8 + 4 + 4 + 1; // version, seq, ids, two lengths, commit tag
    let subject = "/a/x";
    let body = vec![7u8; astream_broker::MAX_RECORD_PAYLOAD - fixed - subject.len()];
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        assert_eq!(
            log.publish(1, 1, subject.into(), body.clone()).unwrap(),
            (Offset(0), false)
        );
    }
    let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0))[0].body, body);
    drop(log);
}

/// The watermark and base sidecars are replaced through a temporary file at a fixed
/// name. A symlink planted there by someone who can write the log directory — the
/// attacker anti-rollback exists for — must not redirect that write: the file it
/// points to stays untouched, and the log keeps working.
#[cfg(all(unix, feature = "anti-rollback", feature = "retention"))]
#[test]
fn sidecar_writes_do_not_follow_a_planted_symlink() {
    const KEY: [u8; 32] = [0x77; 32];
    let (_tmp, path) = tmp("symlink");
    cleanup(&path);
    let victim = sidecar(&path, ".victim");
    std::fs::write(&victim, b"precious").unwrap();
    let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
    for ext in [".hw.tmp", ".base.tmp"] {
        std::os::unix::fs::symlink(&victim, sidecar(&path, ext)).unwrap();
    }
    for i in 0..3u64 {
        log.publish(1, i, "/a/x".into(), b"x".to_vec()).unwrap();
    }
    assert_eq!(log.retain_before(Offset(1)).unwrap(), 1);
    assert_eq!(std::fs::read(&victim).unwrap(), b"precious");
    drop(log);
    let log = BrokerLog::open_encrypted_verified(&path, KEY).unwrap();
    assert_eq!((log.base(), log.head()), (Offset(1), Offset(3)));
    drop(log);
}

/// The first commit on an anti-rollback log must never leave the log AHEAD of a
/// watermark that is not bound to it. Here the watermark write of that commit fails
/// (as a crash right there would leave it): the log must still be one
/// `open_encrypted_verified` accepts — not one that needs `_init` to re-establish
/// trust in it.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_failed_first_watermark_write_leaves_a_log_verified_open_accepts() {
    const KEY: [u8; 32] = [0x5e; 32];
    let (_tmp, path) = tmp("hwfirst");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        std::fs::create_dir(sidecar(&path, ".hw.tmp")).unwrap();
        assert!(log.publish(1, 1, "/a/x".into(), b"one".to_vec()).is_err());
        std::fs::remove_dir(sidecar(&path, ".hw.tmp")).unwrap();
    }
    let mut log = BrokerLog::open_encrypted_verified(&path, KEY)
        .expect("a failed first watermark write left a log verified open refuses");
    // Whatever landed is served, and the key is exactly-once from here on.
    let (off, _) = log.publish(1, 1, "/a/x".into(), b"one".to_vec()).unwrap();
    assert_eq!(log.head(), Offset(off.0 + 1));
    drop(log);
    assert!(BrokerLog::open_encrypted_verified(&path, KEY).is_ok());
}
